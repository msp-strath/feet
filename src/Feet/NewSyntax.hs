{-# LANGUAGE  TypeSynonymInstances
            , FlexibleInstances
            , PatternSynonyms
            , TupleSections
            , GADTs
            , TypeOperators
            , DeriveFunctor
            , DeriveFoldable
            , DeriveTraversable
            , LambdaCase
            , TypeFamilies
#-}
module Feet.NewSyntax where

import Data.Void
import Data.Bits

import Control.Applicative
import Control.Monad
import Control.Arrow

import Utils.Bwd

import Debug.Trace

data Chk
  m -- what's the meta
  = A String       -- atoms
  | Chk m :& Chk m -- pairs
  | B (Chk m)      -- binder
  | E (Syn m)      -- embedding Syn
  | M m            -- metas
  deriving (Show, Functor, Eq, Ord)

data Syn
  m -- what's the meta
  = V Int           -- variables
  | P Name (HideEq Type)     -- parameters
  | Syn m :$ Chk m  -- elimination
  | Chk m ::: Chk m -- radicals
  deriving (Show, Functor, Eq, Ord)

newtype HideEq a = Hide { unHide :: a }
  deriving (Functor)

instance Show (HideEq a) where
  show (Hide a) = ""

instance Eq (HideEq a) where
  x == y = True

instance Ord (HideEq a) where
  compare x y = EQ

type Name = [(String, Int)] -- namespaces and deBruijn levels
type NameSupply = (Bwd (String, Int), Int) -- (namespaces and deBruijn levels), local deBruijn level

initNameSupply = (B0, 0)

infixr 2 :&
infixl 3 :$
infix  1 :::

upsE :: Syn m -> Chk m
upsE (t ::: _) = t
upsE s = E s

-- the object language

type ChkTm = Chk Void
type SynTm = Syn Void

-- these should not contain any V constructors
type Value = Chk Void
type Neutral = Syn Void
type Type = Value
newtype Env = Env [(Value, Type)]
  deriving Show

-- the meta language

type ChkPa = Chk (String, Thinning)

type ChkEx = Chk Meta
type SynEx = Syn Meta

data Meta = String :/ Bwd SynEx
  deriving Show

pm :: String -> ChkPa -- pattern metavariable
pm x = M (x, mempty)

em :: String -> ChkEx -- expression metavariable
em x = M (x :/ B0)

-- thinnings

newtype Thinning = Th Integer

instance Show Thinning where
  show (Th th) = go th where
    go 0 = "...0"
    go (-1) = "...1"
    go th = case unsnocBit th of
      (th, b) -> go th ++ if b then "1" else "0"

os :: Thinning -> Thinning
os (Th th) = Th (snocBit th True)

o' :: Thinning -> Thinning
o' (Th th) = Th (snocBit th False)

snocBit :: Bits a => a -> Bool -> a
snocBit bs True = shiftL bs 1 .|. (bit 0)
snocBit bs False = shiftL bs 1

unsnocBit :: Bits a => a -> (a, Bool)
unsnocBit bs = (shiftR bs 1, testBit bs 0)

instance Semigroup Thinning where
  (<>) = mappend

instance Monoid Thinning where
  mempty = Th (-1)
  Th th `mappend` Th ph = Th (go th ph) where
    go th 0    =  0
    go th (-1) =  th
    go th ph = case unsnocBit ph of
      (ph, False) -> snocBit (go th ph) False
      (ph, True)  -> case unsnocBit th of
        (th, b) -> snocBit (go th ph) b

class Thin t where
  (<^>) :: t -> Thinning -> t
  thicken :: Thinning -> t -> Maybe t

instance Thin Int where
  i <^> Th th = case (th `mod` 2, th `div` 2) of
    (0, th) -> 1 + (i <^> Th th)
    (1, th) -> case i of
      0 -> 0
      _ -> 1 + ((i - 1) <^> Th th)
  thicken (Th th) i = go th i where
    go 0 i = Nothing
    go (-1) i = Just i
    go th i = case (unsnocBit th, i) of
      ((th, False), 0) -> Nothing
      ((th, False), i) -> go th (i-1)
      ((th, True), 0) -> Just 0
      ((th, True), i) -> (1+) <$> go th (i-1)

instance Thin ChkTm where
  t <^> th = case t of
    A a     -> A a
    t :& t' -> (t <^> th) :& (t' <^> th)
    B t   -> B (t <^> os th)
    E s     -> E (s <^> th)
    M m     -> M m

  thicken th t = case t of
    A a     -> Just (A a)
    t :& t' -> (:&) <$> thicken th t <*> thicken th t'
    B t     -> B <$> thicken (os th) t
    E s     -> E <$> thicken th s
    M m     -> Just (M m)

instance Thin SynTm where
  s <^> th = case s of
    V i        -> V (i <^> th)
    P n ty     -> P n ty
    s :$ t     -> (s <^> th) :$ (t <^> th)
    (t ::: t') -> (t <^> th) ::: (t' <^> th)

  thicken th s = case s of
    V i        -> V <$> thicken th i
    P n ty     -> Just (P n ty)
    s :$ t     -> (:$) <$> thicken th s <*> thicken th t
    (t ::: t') -> (:::) <$> thicken th t <*> thicken th t'

-- pattern matching

trail :: (Foldable t, Monoid (f a), Applicative f) => t a -> f a
trail = foldMap pure

type Matching = [(String, ChkTm)]

match :: ChkPa -> ChkTm -> Maybe Matching
match (M (x,th)) t = ((:[]) . (x,)) <$> thicken th t
match (A a) (A a') = guard (a == a') >> return []
match (t :& t') (v :& v') = (++) <$> match t v <*> match t' v'
match (B t) (B t') = match t t'
match (E s) _ = Nothing
match _ _ = Nothing

class Instantiate a where
  type InstTarget a
  instantiate :: Matching -> a -> InstTarget a

instance Instantiate Meta where
  type InstTarget Meta = ChkTm

  instantiate m (x :/ si) = substitute (instantiate m si) 0 t
    where Just t = lookup x m

instance Instantiate ChkEx where
  type InstTarget ChkEx = ChkTm

  instantiate m (M x) = instantiate m x
  instantiate m (A a) = A a
  instantiate m (t :& t') = (instantiate m t) :& (instantiate m t')
  instantiate m (B t) = B (instantiate m t)
  instantiate m (E s) = upsE (instantiate m s)

instance Instantiate SynEx where
  type InstTarget SynEx = SynTm

  instantiate m (V i) = V i
  instantiate m (P n ty) = P n ty
  instantiate m (s :$ t) = instantiate m s :$ instantiate m t
  instantiate m (t ::: t') = instantiate m t ::: instantiate m t'

instance Instantiate ChkPa where
  type InstTarget ChkPa = ChkTm

  instantiate m (M (x, th)) = case lookup x m of
    Nothing -> error $ "instantiate: no premise given for " ++ show x
    Just t  -> t <^> th
  instantiate m (A a) = A a
  instantiate m (t :& t') = (instantiate m t :& instantiate m t')
  instantiate m (B t) = B (instantiate m t)
  instantiate m (E s) = error "instantiate: non-canonical pattern"

instance (Instantiate a, Instantiate b) => Instantiate (Premiss a b) where
  type InstTarget (Premiss a b) = Premiss (InstTarget a) (InstTarget b)

  instantiate m (as :- x) = fmap (fmap (instantiate m)) as :- instantiate m x

instance Instantiate a => Instantiate [a] where
  type InstTarget [a] = [InstTarget a]

  instantiate m = fmap (instantiate m)

instance Instantiate a => Instantiate (Bwd a) where
  type InstTarget (Bwd a) = Bwd (InstTarget a)

  instantiate m = fmap (instantiate m)

instance (Instantiate a, Instantiate b) => Instantiate (a, b) where
  type InstTarget (a, b) = (InstTarget a, InstTarget b)

  instantiate m = instantiate m *** instantiate m

class Substitute t where
  substitute :: Bwd SynTm -> Int -> t -> t

(//) :: Substitute t => t -> SynTm -> t
t // e = substitute (B0 :< e) 0 t

instance Substitute m => Substitute (Chk m) where
  substitute si i (M m) = M m
  substitute si i (A a) = A a
  substitute si i (t :& t') = (substitute si i t :& substitute si i t')
  substitute si i (B t) = B (substitute si (i+1) t)
  substitute si i (E s) = upsE (substitute si i s)

instance Substitute Void where
  substitute si i a = a

instance (Substitute a, Substitute b) => Substitute (a, b) where
  substitute si i (a, b) = (substitute si i a, substitute si i b)

instance Substitute Meta where
  substitute si i (m :/ ez) = m :/ fmap (substitute si i) ez

instance Substitute m => Substitute (Syn m) where
  substitute si i (V j) = vacuous (bwdProj si' j) where
    si' = fromi i <> fmap (<^> th) si <> toi 0
    fromi k = fromi (k+1) :< V k
    toi k = if k >= i then B0 else  toi (k+1) :< V k
    th = Th (shiftL (-1) i)
  substitute si i (P n ty) = P n ty
  substitute si i (s :$ t) = substitute si i s :$ substitute si i t
  substitute si i (t ::: t') = substitute si i t ::: substitute si i t'

instance (Substitute a, Substitute b) => Substitute (Premiss a b) where
  substitute si i ([] :- x) = [] :- substitute si i x
  substitute si i (((n,a):ps) :- x) = (((n,a'):ps') :- x') where
    a' = substitute si i a
    ps' :- x' = substitute si (i+1) (ps :- x)


data Premiss a b = [(String,a)] :- (a,b) -- types of params, (name and type of s. var)
  deriving (Show)

data ElimRule = ElimRule
  { targetType :: ChkPa
  , eliminator :: ChkPa
  , elimPremisses :: [Premiss ChkEx Meta]
  , reductType :: ChkEx
  , betaRules :: [(ChkPa, ChkEx)]
  }
  deriving Show

betaContract :: ElimRule -> SynTm -> Maybe SynTm
betaContract r (e@(t ::: ty) :$ s) = do
  mtTy <- match (targetType r) ty
  me <- match (eliminator r) s
  let rTy = (instantiate (me ++ mtTy) $ reductType r) // e
  case [ (mt, rhs) | (p, rhs) <- betaRules r, mt <- trail (match p t) ] of
    [(mt, rhs)] -> do
      let m = mtTy ++ mt ++ me
      return (instantiate m rhs ::: rTy)
    _ -> Nothing
betaContract r _ = Nothing

data Setup = Setup
  { elimRules :: [ElimRule]
  , weakAnalyserSetup :: (Type, ChkTm) -> TCM (Maybe WeakAnalysis) -- expecting types to be head normalised,
                                                                   -- ensuring that output types are
  }

data WeakAnalysis where
  WeakAnalysis :: (Traversable f) => f (Type, ChkTm) -> (f ChkTm -> ChkTm) -> WeakAnalysis

newtype TCM a = TCM { runTCM :: Setup -> NameSupply -> Either String a }
  deriving (Functor)

instance Applicative TCM where
  pure = return
  (<*>) = ap

instance Monad TCM where
  return x = TCM $ \ s ns -> Right x

  TCM tx >>= f = TCM $ \ s ns -> case tx s ns of
    Left err -> Left err
    Right x -> runTCM (f x) s ns

  fail x = TCM $ \ _ _ -> Left x

refresh :: String -> TCM x -> TCM x
refresh y x = TCM $ \ s (root, level) -> runTCM x s (root :< (y, level), 0)

fresh :: (String, Type) -> (SynTm -> TCM x) -> TCM x
fresh (y, ty) f = TCM $ \ s (root, level) -> runTCM (f (P (root <>> [(y, level)]) (Hide ty))) s (root, level+1)

vP :: Name -> HideEq Type -> TCM SynTm
vP n ty = TCM $ \ s (root, level) -> case B0 <>< n of
   (nz :< (_, k)) | nz == root -> return $ V (level - k - 1)
   _                           -> return $ P n ty

-- type is head normal
checkEquality :: Type -> ChkTm -> ChkTm -> TCM Bool
checkEquality ty x y = (==) <$> normalise (ty, x) <*> normalise (ty, y)

demandEquality :: Type -> ChkTm -> ChkTm -> TCM ()
demandEquality ty x y = do
  b <- checkEquality ty x y
  if b then return () else fail $ "not equal: " ++ show x ++ " and " ++ show y

weakAnalyser :: (Type, ChkTm) -> TCM (Maybe WeakAnalysis)
weakAnalyser x = TCM $ \ s ns -> runTCM (weakAnalyserSetup s x) s ns

eliminate :: Type -> ChkTm -> TCM (Matching, ElimRule)
eliminate ty s = TCM $ \ setup ns -> case [ (mTy ++ melim, rule) | rule <- elimRules setup, mTy <- trail (match (targetType rule) ty), melim <- trail (match (eliminator rule) s) ] of
  [(m, rule)] -> Right $ (m, rule)
  []          -> Left $ "eliminator: no rule applies"
  x           -> Left $ "eliminator: more than one rule applies! " ++ show x

-- Assuming type is already head normalised
weakChkEval :: (Type, ChkTm) -> TCM ChkTm
-- weakChkEval x | trace ("chk: " ++ show x) False = undefined
weakChkEval (Thinning _X ga de, th) = do
  de <- weakChkEval (List _X, de)
  (ga', th) <- weakChkThinning th de
  -- demandEquality (List _X) ga ga' --this should never fail
  return (evalThinNF th de)
weakChkEval x = do
  r <- weakAnalyser x
  case r of
    Just (WeakAnalysis xs recon) -> recon <$> traverse weakChkEval xs
    Nothing -> case x of
      (ty, E e) -> upsE <$> (fst <$> weakEvalSyn e)
      x         -> return (snd x)


expandThx :: ChkTm -> ChkTm -> ChkTm
expandThx x Nil = Nil
expandThx x (Cons _ xs) = Cons x (expandThx x xs)
expandThx x ys = x

isExpandedThx :: ChkTm -> ChkTm -> Bool
isExpandedThx x Nil = True
isExpandedThx x (Cons y xs) = y == x && isExpandedThx x xs
isExpandedThx x ys = x == ys

isAnnihilatedSemi :: ChkTm -> Maybe ChkTm
isAnnihilatedSemi (Cons Th0 th) = isAnnihilatedSemi th
isAnnihilatedSemi (ThSemi th ph) | isExpandedThx Th0 ph = Just th
                                 | otherwise = ThSemi th <$> isAnnihilatedSemi ph
isAnnihilatedSemi _ = Nothing

thSemi :: ChkTm -> ChkTm -> ChkTm -> ChkTm -> ChkTm -> ChkTm
thSemi Nil th ga ph de = expandThx Th0 de
thSemi rh th ga (Cons Th0 ph) (Cons _ de) = Cons Th0 (thSemi rh th ga ph de)
thSemi rh (Cons Th0 th) (Cons _ ga) (Cons Th1 ph) (Cons _ de) = Cons Th0 (thSemi rh th ga ph de)
thSemi (Cons _ rh) (Cons Th1 th) (Cons _ ga) (Cons Th1 ph) (Cons _ de) = Cons Th1 (thSemi rh th ga ph de)

thSemi rh th ga ph de | isExpandedThx Th1 th = ph
thSemi rh th ga ph de | isExpandedThx Th1 ph = th

thSemi rh th ga ph de | Just th <- isAnnihilatedSemi th = ThSemi th (expandThx Th0 de)
thSemi rh th Nil ph de = ThSemi th (expandThx Th0 de)


data ThinNF = IsNone
            | IsNonNilId
            | NoneAfter SynTm
            | NotViaNil ChkTm

evalThinNF :: ThinNF -> ChkTm -> ChkTm
evalThinNF IsNone de = expandThx Th0 de
evalThinNF IsNonNilId de = expandThx Th1 de
evalThinNF (NoneAfter th) de = go de where
  go Nil = E th
  go (Cons _ de) = Cons Th0 (go de)
  go de = ThSemi (E th) Th0
evalThinNF (NotViaNil th) = th

-- de is head normal
-- returns origin + evaled thinning
weakChkThinning :: ChkTm -> ChkTm -> TCM (ChkTm, ThinNF)
weakChkThinning th de = case th of
  Th1 -> return (de, case de of Nil -> IsNone; _ -> IsNonNilId)
  Th0 -> return (Nil, IsNone)
  Nil -> return (Nil, IsNone)
  Cons Th1 th -> case de of
    Cons x xs -> do
      (ga, th) <- weakChkThinning th xs
      return $ (Cons x ga,) $ case (th, xs) of
        (IsNone, Nil) -> IsNonNilId
        (IsNonNilId, xs) -> IsNonNilId
        _ -> NotViaNil (Cons Th1 (evalThinNF th de))
  Cons Th0 th -> case de of
    Cons x xs -> do
      (ga, th) <- weakChkThinning th xs
      return $ (ga,) $ case th of
        IsNone -> IsNone
        IsNonNilId -> NotViaNil (Cons Th0 (expandThx Th1 xs))
        NoneAfter th -> NoneAfter th
        NotViaNil th -> NotViaNil (Cons Th0 th)
  ThSemi th ph -> do
    (ga, ph) <- weakChkThinning ph de
    (rh, th) <- weakChkThinning th ga
    return $ (rh,) $ case th of
      IsNone -> IsNone
      IsNonNilId -> ph
      NoneAfter th -> NoneAfter th
      NotViaNil th -> case ph of
        IsNone -> case th of E th -> NoneAfter th
        IsNonNilId -> NotViaNil th
        NoneAfter ph -> NoneAfter ()
  E th -> do
    (th, t) <- weakEvalSyn th
    case t of
      Thinning _X ga de' -> do
        -- demandEquality (List _X) de de'
        ga <- weakChkEval (List _X, ga)
        case ga of
          Nil -> return (Nil, IsNone)
          _   -> case th of
            (th ::: _) -> weakChkThinning th de'
            _ -> case de of
              Nil -> return (ga, NoneAfter th)
              _ -> return (ga, NotViaNil (E th))
{-
We cannot have the eta law that every thinning th : xs -> xs is the
identity. Because consider a context where we have the following:

  th0 : xs -> ys
  th1 : ys -> xs
  th2 : xs -> ys

Then since th0 ; th1 : xs -> xs and th1 ; th2 : ys -> ys, we would
then have th0 ; th1 = id and th1 ; th2 = id, and hence

  th0 = th0 ; th1 ; th2 = th2

ie we would have definitional equalites depending on proof search in
the context.
-}

-- Ensures that the type is head normalised
weakEvalSyn :: SynTm -> TCM (SynTm, Type)
-- weakEvalSyn x | trace ("syn: " ++ show x) False = undefined
weakEvalSyn (V i) = fail "weakEvalSyn applied to non-closed term"
weakEvalSyn (P n ty) = return (P n ty, unHide ty)
weakEvalSyn (t ::: ty) = do
  weakChkEval (Ty, ty) >>= \case
    ty -> weakChkEval (ty, t) >>= \case
        t -> return (t ::: ty, ty)
weakEvalSyn (e :$ s) = do
  (e, ty) <- weakEvalSyn e
  (m , rule) <- eliminate ty s
  rTy <- weakChkEval (Ty, (instantiate m $ reductType rule) // e)
  (,rTy) <$>
    case e of
      (t ::: _) -> case [ (mt, rhs) | (p, rhs) <- betaRules rule, mt <- trail (match p t) ] of
        [(mt, rhs)] -> do
           r <-  weakChkEval (rTy, instantiate (m ++ mt) rhs)
           return (r ::: rTy)
        [] -> return (e :$ s)
        _  -> fail "weakEvalSyn: more than one rule applies"
      _ -> return (e :$ s)


normalise :: (Type, ChkTm) -> TCM ChkTm
normalise = refresh "n" . go where
  go (Ty, e) = weakChkEval (Ty, e) >>= \case
    Ty -> return Ty
    Pi s t -> do
      s <- go (Ty, s)
      t <- fresh ("x", s) $ \ x -> go (Ty, t // x)
      return (Pi s t)
    Sg s t -> do
      s <- go (Ty, s)
      t <- fresh ("y", s) $ \ y -> go (Ty, t // y)
      return (Sg s t)
    E e -> do
      (e, _) <- stop e
      return (E e)
    x -> error $ "hm " ++ show x
  go (a@(Pi s t), e) = Lam <$> (fresh ("x", s) $ \ x -> go (t // x, E ((e ::: a) :$ E x)))
  go (a@(Sg s t), e) = do
    e <- weakChkEval (a, e)
    s <- weakChkEval (Ty, s)
    let e0 = (e ::: a) :$ Fst
    e0' <- go (s, E e0)
    t <- weakChkEval (Ty, t // e0)
    let e1 = (e ::: a) :$ Snd
    e1' <- go (t, E e1)
    return (e0' :& e1')
  go (One, _) = return Void
  go (List _X, e) = do
    _X <- weakChkEval (Ty, _X)
    weakChkEval (List _X, e) >>= \case
      Nil -> return Nil
      Single x -> Single <$> go (_X, x)
      xs :++: ys -> do
        xs' <- go (List _X, xs)
        ys' <- go (List _X, ys)
        let tidy Nil bs = bs
            tidy as Nil = as
            tidy (as :++: bs) cs = tidy as (tidy bs cs)
            tidy as bs = as :++: bs
        return $ tidy xs' ys'
      {-
      Cons s ss -> do
        s'  <- go (x, s)
        ss' <- go (List x, ss)
        return $ Cons s' ss'
      -}
      E e -> do
        (e', _) <- stop e
        return (E e')
  go (E ty, E e) = do
    (e, _) <- weakEvalSyn e
    (e, _) <- stop e
    return (E e)


  stop :: SynTm -> TCM (SynTm, Type)
  stop (V i) = error "normalise: applied to non-closed term"
  stop (P n ty) = (,) <$> vP n ty <*> weakChkEval (Ty, unHide ty)
  stop (E e ::: t) = stop e
  stop (s ::: t) = error "normalise: failure of canonicity"
  stop (e :$ s) = do
    (e', ty) <- stop e
    (m, rule) <- eliminate ty s
    let ps = elimPremisses rule
    let names = [ n | (_ :- (_, n :/ _)) <- ps ]
    values <- traverse prem (instantiate m ps)
    let m' = zip names values
    rTy <- weakChkEval (Ty, (instantiate m $ reductType rule) // e)
    return (e' :$ instantiate m' (eliminator rule), rTy)

  prem :: Premiss ChkTm ChkTm -> TCM ChkTm
  prem ([] :- p) = go p
  prem (((y, ty):hs) :- p) = fresh (y, ty) $ \ y -> prem ((hs :- p) // y)


-- Type
pattern Ty = A "Ty"

-- Pi
pattern Pi s t = A "Pi" :& s :& B t
pattern Lam t = A "lam" :& B t

piElim = ElimRule
  { targetType = Pi (pm "S") (pm "T")
  , eliminator = pm "s"
  , elimPremisses = [[] :- (em "S", "s" :/ B0)]
  , reductType = M ("T" :/ si)
  , betaRules = [(Lam (pm "t"), M ("t" :/ si))]
  }
  where si = B0 :< (em "s" ::: em "S")

-- Sigma
pattern Sg s t = A "Sg" :& s :& B t
-- Pair s t = s :& t
pattern Fst = A "fst"
pattern Snd = A "snd"

fstElim = ElimRule
  { targetType = Sg (pm "S") (pm "T")
  , eliminator = Fst
  , elimPremisses = []
  , reductType = M ("S" :/ B0)
  , betaRules = [(pm "s" :& pm "t", em "s")]
  }

sndElim = ElimRule
  { targetType = Sg (pm "S") (pm "T")
  , eliminator = Snd
  , elimPremisses = []
  , reductType = M ("T" :/ si)
  , betaRules = [(pm "s" :& pm "t", em "t")]
  }
  where si = B0 :< (V 0 :$ Fst)

-- One
pattern One = A "One"
pattern Void = A ""

-- List
pattern List _X = A "List" :& _X
pattern Nil = A ""
pattern Single x = A "single" :& x
pattern (:++:) xs ys = A "append" :& xs :& ys
pattern Cons x xs = Single x :++: xs
pattern ListElim p n c = A "ListElim" :& B p :& n :& B (B (B c))

listElim = ElimRule
  { targetType = List (pm "X")
  , eliminator = ListElim (pm "P") (pm "n") (pm "c")
  , elimPremisses =
    [ [("xs", List (em "X"))] :- (Ty, "P" :/ B0)
    , [] :- (M ("P" :/ (B0 :< (Nil ::: List (em "X")))), "n" :/ B0)
    , [("x", em "X"), ("xs", List (em "X")), ("ih", M ("P" :/ (B0 :< V 0)))]
      :- (M ("P" :/ (B0 :< (Cons (E (V 2)) (E (V 1)) ::: List (em "X")))), "c" :/ B0)]
  , reductType = M ("P" :/ (B0 :< V 0))
  , betaRules =
    [ (Nil, em "n")
    , (Single (pm "x"),
       M ("c" :/ (B0
         :< (em "x" ::: em "X")
         :< (Nil ::: List (em "X"))
         :< (em "n" ::: M ("P" :/ (B0 :< (Nil ::: List (em "X"))))))))
    , (pm "xs" :++: pm "ys",
       E ((em "xs" ::: List (em "X")) :$ ListElim
         (M ("P" :/ (B0 :< ((E (V 0) :++: em "ys") ::: List (em "X")))))
         (E ((em "ys" ::: List (em "X")) :$ ListElim (em "P") (em "n") (em "c")))
         (M ("c" :/ (B0 :< V 2 :< ((E (V 1) :++: em "ys") ::: List (em "X")) :< V 0)))))
    {-
    , (Cons (pm "x") (pm "xs"),
       M ("c" :/ (B0 :< (em "x" ::: em "X") :< (em "xs" ::: List (em "X")) :<
        ((em "xs" ::: List (em "X")) :$ ListElim (em "P") (em "n") (em "c")))))
    -}
    ]
  }

-- Thinnings

pattern Thinning _X ga de = A "Th" :& _X :& ga :& de

pattern Th1 = A "1"
pattern Th0 = A "0"
pattern ThSemi th th' = A ";" :& th :& th'

-- Kit

newtype I x = I { unI :: x }
  deriving (Functor, Foldable, Traversable)

newtype K a x = K { unK :: a }
  deriving (Functor, Foldable, Traversable)

data (f :*: g) x = (:*:) { outL :: f x , outR :: g x }
  deriving (Functor, Foldable, Traversable)

data (f :+: g) x = InL (f x) | InR (g x)
  deriving (Functor, Foldable, Traversable)

-- Returns longest prefix of conses, and the suffix
consPrefix :: Type -> ChkTm -> ([] :*: K ChkTm) (Type, ChkTm)
consPrefix _X xs = case xs of
  Nil -> [] :*: K Nil
  Single x -> [(_X, x)] :*: K Nil
  ys :++: zs -> case consPrefix _X ys of
    (ys :*: K Nil) -> case consPrefix _X zs of
      (zs :*: t) -> (ys ++ zs) :*: t
    (ys :*: K t) -> ys :*: K (t :++: zs)

ourSetup = Setup
  { elimRules = [piElim, fstElim, sndElim, listElim]
  , weakAnalyserSetup = \ x -> case x of
      (Ty, Pi s t) -> return $ Just $ WeakAnalysis (I (Ty, s)) (\ (I s') -> Pi s' t)
      (Ty, Sg s t) -> return $ Just $ WeakAnalysis (I (Ty, s)) (\ (I s') -> Sg s' t)
      (Sg s t, x :& y) -> do
        t <- weakChkEval (Ty, t // (x ::: s))
        return $ Just $ WeakAnalysis (I (s, x) :*: I (t , y)) (\ (I x' :*: I y') -> (x' :& y'))
      -- Ensures that a list equal to Nil is Nil, and a list equal to a Cons is a Cons, and hereditarily
      (List _X, x) -> do
        _X <- weakChkEval (Ty, _X)
        return $ Just $ WeakAnalysis (consPrefix _X x) (\ (xs :*: K t) -> foldr Cons t xs)
      _ -> return $ Nothing
  }


run :: TCM x -> Either String x
run x = runTCM x ourSetup initNameSupply

chkEval = run . weakChkEval
evalSyn = run . weakEvalSyn

-- testing

idTy = Pi Ty (Pi (E (V 0)) (E (V 1)))
idTm = Lam (Lam (E (V 0)))

fam :: ChkTm -> ChkTm
fam x = Sg Ty (Pi (E (V 0)) (x <^> o' (o' mempty)))

famTytm = idTy :& Lam idTy

pairTy = Sg Ty Ty

revTy = ListElim
  (Pi (List Ty) (List Ty))
  (Lam (E (V 0)))
  (Lam (E (V 1 :$ Cons (E (V 3)) (E (V 0)))))

myTys = Cons Ty (Cons (Pi Ty Ty) (Cons (Sg Ty Ty) Nil)) ::: List Ty

{-
TODO
1. More infrastructure towards canonical representatives
2. Additional interesting types (lists, abelian group, thinnings)
3. Typechecking
-}
