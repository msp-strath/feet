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
            , MultiParamTypeClasses
#-}
module Feet.NewSyntax where

import Data.Void
import Data.Bits

import qualified Data.Map as Map

import Control.Applicative
import Control.Monad
import Control.Arrow

import Utils.Utils
import Utils.Bwd

import Debug.Trace

-- track = trace
track = tracko
tracko x = id


data Chk
  m -- what's the meta
  = A String       -- atoms
  | Chk m :& Chk m -- pairs
  | B (Chk m)      -- binder
  | (:-:) (Syn m) (Chk m) -- embedding Syn
  | M m            -- metas
  deriving (Show, Functor, Eq, Ord)

type Adapter = ChkTm

pattern E e = e :-: Idapter

-- Adapters are:

pattern Idapter = A "Idapter" -- identity
-- List f, where f is an arbitrary function

data Syn
  m -- what's the meta
  = V Int           -- variables
  | P Name (HideEq Type)     -- parameters
  | Syn m :$ Chk m  -- elimination
  | Chk m ::: Chk m -- radicals
  deriving (Show, Functor, Eq, Ord)

newtype HideEq a = Hide { unHide :: a }
  deriving (Functor)

instance {-Show a =>-} Show (HideEq a) where
  show (Hide a) = "" -- show a

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

data Mangler m f = Mangler
  { mangV :: Int -> f (Syn m)
  , mangP :: Name -> HideEq Type -> f (Syn m)
  , mangM :: m -> f (Chk m)
  , mangB :: Mangler m f
  }

class Mangle t where
  type MangleM t
  mangle :: Applicative f => Mangler (MangleM t) f -> t -> f t

instance Mangle (Chk m) where
  type MangleM (Chk m) = m
  mangle mangler t = case t of
    A s -> pure (A s)
    s :& t -> (:&) <$> mangle mangler s <*> mangle mangler t
    B t -> B <$> mangle (mangB mangler) t
    E e -> upsE <$> mangle mangler e
    s :-: t -> (:-:) <$> mangle mangler s <*> mangle mangler t
    M m -> mangM mangler m

instance Mangle (Syn m) where
  type MangleM (Syn m) = m
  mangle mangler e = case e of
    V i -> mangV mangler i
    P n ty -> mangP mangler n ty
    e :$ t -> (:$) <$> mangle mangler e <*> mangle mangler t
    e ::: t -> (:::) <$> mangle mangler e <*> mangle mangler t

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

instance Thin Void where
  i <^> th = absurd i
  thicken th i = absurd i

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

instance Thin m => Thin (Chk m) where
  s <^> th = unI (mangle (thinM th) s)
  thicken = mangle . thickenM

instance Thin m => Thin (Syn m) where
  s <^> th = unI (mangle (thinM th) s)
  thicken = mangle . thickenM

thinM :: Thin m => Thinning -> Mangler m I
thinM th = Mangler
  { mangV = \ i -> pure (V (i <^> th))
  , mangP = \ n ty -> pure (P n ty)
  , mangM = \ m -> pure (M (m <^> th))
  , mangB = thinM (os th)
  }

thickenM :: Thin m => Thinning -> Mangler m Maybe
thickenM th = Mangler
  { mangV = \ i -> (V <$> thicken th i)
  , mangP = \ n ty -> pure (P n ty)
  , mangM = \ m -> (M <$> thicken th m)
  , mangB = thickenM (os th)
  }

-- pattern matching

trail :: (Foldable t, Monoid (f a), Applicative f) => t a -> f a
trail = foldMap pure

type Matching = [(String, ChkTm)]

match :: ChkPa -> ChkTm -> Maybe Matching
match (M (x,th)) t = ((:[]) . (x,)) <$> thicken th t
match (Cons x xs) (Single t) = (++) <$> match x t <*> match xs Nil
match (A a) (A a') = guard (a == a') >> return []
match (t :& t') (v :& v') = (++) <$> match t v <*> match t' v'
match (B t) (B t') = match t t'
match (e :-: s) _ = Nothing
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
  instantiate m (E e) = upsE (instantiate m e)
  instantiate m (e :-: s) = (instantiate m e) :-: (instantiate m s)

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
  instantiate m (e :-: s) = error "instantiate: non-canonical pattern"

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

substM :: Substitute m => Bwd SynTm -> Int -> Mangler m I
substM si i = Mangler
  { mangV = \ j -> let si' = fromi i <> fmap (<^> th) si <> toi 0
                       fromi k = fromi (k+1) :< V k
                       toi k = if k >= i then B0 else  toi (k+1) :< V k
                       th = Th (shiftL (-1) i)
                   in pure (vacuous (bwdProj si' j))
  , mangP = \ n ty -> pure (P n ty)
  , mangM = \ m -> pure (M (substitute si i m))
  , mangB = substM si (i+1)
  }

instance Substitute m => Substitute (Chk m) where
  substitute si i = unI . mangle (substM si i)

instance Substitute Void where
  substitute si i a = a

instance (Substitute a, Substitute b) => Substitute (a, b) where
  substitute si i (a, b) = (substitute si i a, substitute si i b)

instance Substitute Meta where
  substitute si i (m :/ ez) = m :/ fmap (substitute si i) ez

instance Substitute m => Substitute (Syn m) where
  substitute si i = unI . mangle (substM si i)

instance (Substitute a, Substitute b) => Substitute (Premiss a b) where
  substitute si i ([] :- x) = [] :- substitute si i x
  substitute si i (((n,a):ps) :- x) = (((n,a'):ps') :- x') where
    a' = substitute si i a
    ps' :- x' = substitute si (i+1) (ps :- x)

data Premiss a b = [(String,a)] :- (a,b) -- types of params, (name and type of s. var)
  deriving Show

class Abstract t where
  abstract :: Name -> Int -> t -> t


abstractM :: Abstract m => Name -> Int -> Mangler m I
abstractM n i = Mangler
  { mangV = \ i -> pure (V i)
  , mangP = \ n' ty -> if n == n' then pure (V i) else pure (P n' ty)
  , mangM = \ m -> pure (M (abstract n i m))
  , mangB = abstractM n (i + 1)
  }

(\\) :: Abstract t => Name -> t -> t
n \\ x = abstract n 0 x

instance Abstract Void where
  abstract n i t = absurd t

instance Abstract m => Abstract (Syn m) where
  abstract n i = unI . mangle (abstractM n i)

instance Abstract m => Abstract (Chk m) where
  abstract n i = unI . mangle (abstractM n i)


data Prog' = Ret ChkEx
           | Case ChkEx ChkEx Prog -- type, scrutinee, cases
  deriving Show

type Prog = [(ChkPa,Prog')]

runProg :: Matching -> Value -> Prog -> TCM (Maybe ChkTm)
runProg m v ps =
  case [ (mv, rhs) | (p, rhs) <- ps, mv <- trail (match p v) ] of
    [ (mv, rhs) ] -> runProg' (mv ++ m) rhs
    _ -> return Nothing

runProg' :: Matching -> Prog' -> TCM (Maybe ChkTm)
runProg' m (Ret t) = return (Just (instantiate m t))
runProg' m (Case ty sc ps) = do
  ty <- weakChkEval (Ty, instantiate m ty)
  sc <- weakChkEval (ty, instantiate m sc)
  runProg m sc ps

data ElimRule = ElimRule
  { targetType :: ChkPa
  , eliminator :: ChkPa
  , elimPremisses :: [Premiss ChkEx Meta]
  , reductType :: ChkEx
  , betaRules :: Prog
  , fusionRules :: [(ChkPa, ChkPa, ChkEx)]
  }
  deriving Show

{-
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
-}

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

pNom :: Name -> TCM String
pNom n = TCM $ \ s (root, _) -> case B0 <>< n of
    (nz :< s) | nz == root  -> return $ seg s
    _                       -> return $ foldMap seg n
  where
    seg (x, 0) = x
    seg (x, i) = x ++ show i
    
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
  []          -> Left $ "eliminator: no rule applies! ty = " ++ show ty ++ " s = " ++ show s
  x           -> Left $ "eliminator: more than one rule applies! " ++ show x

-- Assuming type is already head normalised
weakChkEval :: (Type, ChkTm) -> TCM ChkTm
weakChkEval x | track ("chk:\n   " ++ show x) False = undefined
weakChkEval (FAb _X, x) = do
  _X <- weakChkEval (Ty, _X)
  Map.foldrWithKey folder FOne <$> chkFAb _X x
 where
 folder x n xs = case compare n 0 of
   LT -> smartmul (Inv x) (folder x (n+1) xs)
   EQ -> xs
   GT -> smartmul x (folder x (n-1) xs)
 smartmul x FOne = x
 smartmul FOne y = y
 smartmul x y = x :.: y
weakChkEval (List _X, xs) = case xs of
  Nil -> return Nil
  Single x -> return $ Single x
  xs :++: ys -> do
    xs <- weakChkEval (List _X, xs)
    case xs of
      Nil -> weakChkEval (List _X, ys)
      Single x -> return (Cons x ys)
      Cons x xs -> return (Cons x (xs :++: ys))
      _ -> return (xs :++: ys)
  E e-> upsE <$> (fst <$> weakEvalSyn e)
  e :-: a ->  do
    (e, src) <- weakEvalSyn e
    weakAdapt e src a (List _X)
weakChkEval (AllT _X _P xs, ps) = do
  xs <- weakChkEval (List _X, xs)
  (ps, leftovers) <- chkAll _X _P xs ps
  demandEquality (List _X) leftovers Nil --this should never fail
  return ps
weakChkEval (Enum as, x) = do
  weakFind as x >>= \case
    Right t -> return t
    Left _ -> fail ("out of bounds as = " ++ show as ++ " x = " ++ show x)
weakChkEval (Thinning _X ga de, th) = do
  de <- weakChkEval (List _X, de)
  (ga', th) <- weakChkThinning _X th de
  -- demandEquality (List _X) ga ga' --this should never fail
  return th
weakChkEval x = do
  r <- weakAnalyser x
  case r of
    Just (WeakAnalysis xs recon) -> recon <$> traverse weakChkEval xs
    Nothing -> case x of
      (ty, E e) -> upsE <$> (fst <$> weakEvalSyn e)
      (tgt, e :-: a) -> do
        (e, src) <- weakEvalSyn e
        -- a <- weakEvalAdapter src a tgt
        weakAdapt e src a tgt
      x         -> return (snd x)


-- Given xs, xs' : List _X such that xs = xs' ++ xs'', computes xs''
unprefix :: Type -> ChkTm -> ChkTm -> TCM ChkTm
unprefix _X xs xs' = weakChkEval (List _X, xs') >>= \case
  Nil -> return xs
  Single x' -> (consView <$> weakChkEval (List _X, xs)) >>= \case
    Cons x xs -> do
      demandEquality _X x x'
      return xs
  xs' :++: ys' -> do
    xs <- unprefix _X xs xs'
    unprefix _X xs ys'
  e' -> weakChkEval (List _X, xs) >>= \case
    xs :++: ys -> do
      xs <- unprefix _X xs e'
      return (xs ++++ ys)
    e -> do -- must be neutral
      demandEquality (List _X) e e'
      return Nil

-- Given type Thinning _X xs ys, th of that type, and ys' a prefix of ys
-- Returns ((xs', xs''), (ys0, ys1, ys''), (th', th''))
-- s.t.:
--   xs = xs' ++ xs''
--   ys = ys' ++ ys''
--   ys' = ys0 ++ ys1
--   th'  : Thinning _X xs' ys0
--   th'' : Thinning _X xs'' (ys1 ++ ys'')
--   th = th' ++ th''
-- for minimal ys1
thunprefix :: Type -> ChkTm -> ChkTm -> TCM ((ChkTm, ChkTm),(ChkTm, ChkTm, ChkTm), (ChkTm, ChkTm))
thunprefix (Thinning _X xs ys) th ys' = (consView <$> weakChkEval (List _X, ys')) >>= \case
  Nil -> return ((Nil, xs), (Nil, Nil, ys), (NoThin, th))
  Cons y ys' -> (consView <$> weakChkEval (List _X, ys)) >>= \case
    Cons _ ys -> (consThView <$> weakChkEval (Thinning _X xs ys, th)) >>= \case
      Cons Th0 th -> do
        ((xs', xs''), (ys0, ys1, ys''), (th', th'')) <- thunprefix (Thinning _X xs ys) th ys'
        return ((xs', xs''), (Cons y ys0, ys1, ys''), (Cons Th0 th', th''))
      Cons Th1 th -> (consView <$> weakChkEval (List _X, ys)) >>= \case
        Cons x xs -> do
          ((xs', xs''), (ys0, ys1, ys''), (th', th'')) <- thunprefix (Thinning _X xs ys) th ys'
          return ((Cons x xs', xs''), (Cons y ys0, ys1, ys''), (Cons Th1 th', th''))
      th -> do
        ys'' <- unprefix _X ys ys'
        return ((Nil, xs), (Nil,Cons y ys', ys''), (NoThin, th))
  ys' -> do
    ys'' <- unprefix _X ys ys'
    return ((Nil, xs), (Nil, ys', ys''), (NoThin, th))



{-
-- f : _Y -> _X
-- g : (y : _Y) -> _P (f y) -> Q y
-- th : Thinning _X (List f ys) xs
-- ps : AllT _X _P xs' for some xs' s.t. xs = xs' ++ xs''
---------------------------------------------------------
-- Returns ((qs, ps''), (xs'', th'', ys'')) where
--   ps = ps' ++ ps''
--   qs : AllT _Y _Q ys' for some ys' s.t. ys = ys' ++ ys''
--   th = th' ++ th''  for some th' : Thinning _X (List f ys') xs', th'' : Thinning _X (List f ys'') xs''
--   qs = ps' mapped by g, selected by th'
chkAll :: (Type, ChkTm, Type) -> (ChkTm, ChkTm, ChkTm) -> (ChkTm, ChkTm, ChkTm) -> ChkTm -> TCM ((ChkTm, ChkTm), (ChkTm, ChkTm, ChkTm))
chkAll ff@(_X, f, _Y) gg@(_P , g, _Q) thth@(xs, th, ys) ps = case ps of
    (e :-: a) -> weakEvalSyn e >>= \case
      (e, AllT _W _O ws) -> case a of
        Idapter -> synAll e ff gg thth
        AllT h k ph -> do
          ((ps, os), phph) <- synAll e (_W , h, _X) (_O, k, _P) (ws, ph, xs)
          undefined
{-
      (e, AllT _W _O ws) -> adapterSemicolon (AllT _W _O ws) a (AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys) >>= \case
        AllT f g th -> do
          ((qs, os), thth) <- synAll e (_W, f, _Y) (_O, g, _Q) (ws, th, ys)
-}

    Nil -> return ((Nil, Nil), (xs, th, ys))
    Single p -> (consView <$> weakChkEval (List _X, xs)) >>= \case
      Cons x xs -> (consThView <$> weakChkEval (Thinning _X ((ys ::: List _Y) :-: List f) (Cons x xs), th)) >>= \case
        Cons Th0 th -> return ((Nil, Nil), (xs, th, ys))
        Cons Th1 th -> (consView <$> weakChkEval (List _Y, ys)) >>= \case
          Cons y ys -> do
            let q = (g ::: Pi _Y (Pi (_P // ((f ::: Pi _Y _X) :$ E (V 0))) (_Q <^> o' mempty))) :$ y :$ p
            return ((Single q, Nil), (xs, th, ys))
        th -> return ((Nil, Single p), thth)
    ps :++: ps' -> do
      ((qs, ps), (xs, th, ys)) <- chkAll ff gg (xs, th, ys) ps
      case ps of
        Nil -> do
          ((qs', ps'), (xs, th, ys)) <- chkAll ff gg (xs, th, ys) ps'
          return ((qs ++++ qs', ps'), (xs, th, ys))
        _ -> return ((qs, ps ++++ ps'), (xs, th, ys))

-- e is head normal
synAll :: SynTm -> (Type, ChkTm, Type) -> (ChkTm, ChkTm, ChkTm) -> (ChkTm, ChkTm, ChkTm) -> TCM ((ChkTm,ChkTm), (ChkTm, ChkTm, ChkTm))
synAll (t ::: _) ff gg thth = chkAll t ff gg thth
synAll e ff gg thth = return ((Nil, E e), thth)
-}

-- f : _X -> _W
-- xs = xs' ++ xs''
-- ws' = List f xs'
-- Returns (xs', xs'')
unmapprefix :: Type -> ChkTm -> Type -> ChkTm -> ChkTm -> TCM (ChkTm, ChkTm)
unmapprefix _X f _W xs ws' = weakChkEval (List _W, ws') >>= \case
  Nil -> return (Nil, xs)
  Single _ -> (consView <$> weakChkEval (List _X, xs)) >>= \case
    Cons x xs -> return (Single x, xs)
  ws0 :++: ws1 -> do
    (xs0', xs) <- unmapprefix _X f _W xs ws0
    (xs1', xs'') <- unmapprefix _X f _W xs ws1
    return (xs0' ++++ xs1', xs'')
  (e :-: a) -> helper xs
  where
    helper xs = weakChkEval (List _X, xs) >>= \case
      xs0 :++: xs1 -> do
        (xs0', xs0'') <- helper xs0
        return (xs0', xs0'' ++++ xs1)
      xs -> return (xs, Nil) -- here xs must be stuck (because ws' is), hence match the stuck ws'


-- returns (ps', xs'') where ps' = evaled ps
-- xs = xs' ++ xs''
-- ps' : AllT _X _P xs'
chkAll :: Type -> ChkTm -> ChkTm -> ChkTm -> TCM (ChkTm, ChkTm) -- (evaled ps, leftovers)
chkAll _X _P xs ps | track ("chkAll:\n   xs = " ++ show xs ++ "\n   ps = " ++ show ps ++ "\n") False = undefined
chkAll _X _P xs ps = case ps of
  Nil -> return (Nil, xs)
  Single p -> (consView <$> weakChkEval (List _X, xs)) >>= \case
    Cons x xs -> do
      _P <- weakChkEval (Ty, _P // (x ::: _X))
      p <- weakChkEval (_P, p)
      return (Single p, xs)
    xs -> error $ show xs
  ps :++: qs -> do
    (ps, xs) <- chkAll _X _P xs ps
    (qs, xs) <- chkAll _X _P xs qs
    return (ps ++++ qs, xs)
  (e :-: AllT f g th) -> weakEvalSyn e >>= \case
    (e, AllT _W _R ws) -> do
    -- We have th : Thinning _W (xs' :-: List f) ws
    -- for xs' a prefix of xs whose suffix we must compute.
      ws <- weakChkEval (List _W, ws)
      (ws', th) <- weakChkThinning _W th ws
      (xs', xs'') <- unmapprefix _X f _W xs ws'
      ps' <- weakAdapt e (AllT _W _R ws) (AllT f g th) (AllT _X _P xs')
      return (ps', xs'')
  (e :-: Idapter) -> weakEvalSyn e >>= \case
    (e, AllT _X' _P' xs') -> do
      -- demandEquality Ty _X _X' --this should never fail
      leftovers <- unprefix _X xs xs'
      return (upsE e, leftovers)

-- type is assumed weak head normalised
chkFAb :: Type -> ChkTm -> TCM (Map.Map ChkTm Integer)
chkFAb _X x = case x of
  Eta x -> do
    x <- normalise (_X, x)
    return (Map.singleton (Eta x) 1)
  FOne -> return Map.empty
  x :.: y -> do
    xm <- chkFAb _X x
    ym <- chkFAb _X y
    return (Map.unionWith (+) xm ym)
  Inv x -> do
    xm <- chkFAb _X x
    return (Map.map negate xm)
  (e :-: Idapter) -> do
    (e, ty) <- weakEvalSyn e
    case e of
      (t ::: _) -> chkFAb _X t
      e -> do
        (e, _) <- normStop e
        return (Map.singleton (upsE e) 1)
  x -> error (show x)

weakFind :: ChkTm -> ChkTm -> TCM (Either (ChkTm -> ChkTm, ChkTm) ChkTm)
weakFind as x = weakChkEval (List Atom, as) >>= \case
    Nil -> return (Left (id, x))
    Single a -> do
      a <- weakChkEval (Atom, a)
      case (a, x) of
        (_, Z) -> return (Right Z)
        (_, S x) -> return (Left (S, x))
        (A a, A b) | a == b -> return (Right Z)
                   | otherwise -> return (Left (S, x))
        (A a, (A b :& Z)) | a == b -> return (Right Z)
                   | otherwise -> return (Left (S, x))
        (A a, (A b :& S n)) | a == b -> return (Left (S, (A b :& n)))
                   | otherwise -> return (Left (S, x))
        (_, E e) -> do
          (e, _) <- weakEvalSyn e
          return (Right (upsE e))
    as :++: bs -> weakFind as x >>= \case
      Right t -> return (Right t)
      Left (f, x) -> weakFind bs x >>= \case
        Right t -> return (Right (f t))
        Left (g, x) -> return (Left (f . g, x))
    _ -> case x of
      E e -> do
        (e, _) <- weakEvalSyn e
        return (Right (upsE e))
      _ -> fail "expecting neutral list of atoms and neutral x"


-- assumes types are in whnf and V-closed
weakAdapt :: SynTm -> ChkTm -> Adapter -> ChkTm -> TCM ChkTm
weakAdapt e src a tgt | track ("weakAdapt:\n   e = " ++ show e ++ "\n   src = " ++ show src ++ "\n   a = " ++ show a ++ "\n   tgt = " ++ show tgt ++ "\n") False = undefined
weakAdapt ((e :-: a) ::: _) mid b tgt = do
  (e , src) <- weakEvalSyn e
  ab <- adapterSemicolon src a mid b tgt
  weakAdapt e src ab tgt
weakAdapt e src Idapter tgt = return (upsE e)
weakAdapt (t ::: _) (List src) (Hom f) (List tgt) = case t of
  Nil -> return Nil
  Single x -> weakChkEval (tgt, E ((f ::: Pi src (List tgt)) :$ x))
  (xs :++: ys) -> (:++:) <$> rec xs <*> rec ys
    where rec z = weakAdapt (z ::: List src) (List src) (Hom f) (List tgt)
{-
weakAdapt e (List src) (List f) (List tgt) =
  weakAdapt e (List src) (Hom (Lam (E ((f ::: Pi src (List tgt)) :$ Single (E (V 0)))))) (List tgt)
-}
weakAdapt (t ::: _) (List src) (List f) (List tgt) = case t of
  Nil -> return Nil
  Single x -> Single <$> weakChkEval (tgt, E ((f ::: Pi src tgt) :$ x))
  (xs :++: ys) -> (:++:) <$> rec xs <*> rec ys
    where rec z = weakAdapt (z ::: List src) (List src) (List f) (List tgt)

weakAdapt e inn@(Thinning src ga de) (Thinning f th ph) out@(Thinning tgt ga' de') = do
  -- f : src -> tgt
  -- th : thinning from ga' -> List f ga
  -- ph : thinning from List f de -> de'
  let lf = List f
  -- lf <- weakEvalAdapter (List src) (List f) (List tgt)
  t <- weakAdapt e inn lf out
  weakChkEval (out, ThSemi (ThSemi th t) ph)
weakAdapt e inn@(Thinning src ga de) (List f) out@(Thinning tgt ga' de') = case e of
  (t ::: _) -> mapThin src f tgt t
  e         -> return (e :-: List f)
weakAdapt e (AllT _X _P xs) (AllT f g th) (AllT _Y _Q Nil) = return Nil
weakAdapt (t ::: _) (AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys) = case consView t of
  -- f : _Y -> _X
  -- g : (y : _Y) -> _P (f y) -> Q y
  -- th : Thinning _X (List f ys) xs
  Nil -> return ((Nil ::: AllT _X _P xs) :-: AllT f g th)  -- don't like this, but best we can do
  Cons p ps -> (consView <$> weakChkEval (List _X, xs)) >>= \case
    Cons x xs -> (consThView <$> weakChkEval (Thinning _X ((ys ::: List _Y) :-: List f) (Cons x xs), th)) >>= \case
      Cons Th0 th -> weakAdapt (ps ::: AllT _X _P xs) (AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys)
      Cons Th1 th -> (consView <$> weakChkEval (List _Y, ys)) >>= \case
        Cons y ys -> do
          let q = (g ::: Pi _Y (Pi (_P // ((f ::: Pi _Y _X) :$ E (V 0))) (_Q <^> o' mempty))) :$ y :$ p
          qs <- weakAdapt (ps ::: AllT _X _P xs) (AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys)
          return (Cons (upsE q) qs)
      th -> return ((Cons p ps ::: AllT _X _P (Cons x xs)) :-: AllT f g th) -- or this; should have an eliminator that gets stuck here instead
weakAdapt e src a tgt = return (e :-: a)

mapThin :: ChkTm -> ChkTm -> ChkTm -> ChkTm -> TCM ChkTm
mapThin src f tgt Th1 = return Th1
mapThin src f tgt Th0 = return Th0
mapThin src f tgt NoThin = return NoThin
mapThin src f tgt (Cons b th) = Cons b <$> (mapThin src f tgt th)
mapThin src f tgt (ThSemi th ph) = ThSemi <$> mapThin src f tgt th <*> mapThin src f tgt ph
mapThin mid f tgt (e :-: a) = do
  (e , ty) <- weakEvalSyn e
  case ty of
    Thinning src _ _ -> do
      af <- adapterSemicolon (List src) a (List mid) (List f) (List tgt)
      return (e :-: af)

{-
-- returns Idapter when possible
weakEvalAdapter :: ChkTm -> Adapter -> ChkTm -> TCM Adapter
--weakEvalAdapter src a tgt | track ("weakEvalAdapter: src = " ++ show src ++ " a = " ++ show a ++ " tgt = " ++ show tgt ++ "\n") False = undefined
weakEvalAdapter src Idapter tgt = return Idapter
weakEvalAdapter (List src) (List f) (List tgt) = do
  eq <-mandy (checkEquality Ty src tgt) (checkEquality (Pi src tgt) f (Lam (E (V 0))))
  if eq then return Idapter else return (List f)
weakEvalAdapter (Thinning src ga de) (List f) (Thinning tgt ga' de') = weakEvalAdapter (List src) (List f) (List tgt)
weakEvalAdapter (Thinning src ga de) (Thinning f th ph) (Thinning tgt ga' de') = do
  lfga <- weakChkEval (List tgt, (ga ::: List src) :-: List f)
  lfde <- weakChkEval (List tgt, (de ::: List src) :-: List f)
  th <- weakChkEval (Thinning tgt ga' lfga, th)
  ph <- weakChkEval (Thinning tgt lfde de', ph)
  if isNormalIdThinning th && isNormalIdThinning ph
    then weakEvalAdapter (List src) (List f) (List tgt)
    else return (Thinning f th ph)
-}

-- all arguments assumed to be in whnf, and V-closed
adapterSemicolon :: ChkTm -> Adapter -> ChkTm -> Adapter -> ChkTm -> TCM Adapter
adapterSemicolon src Idapter mid b tgt = return b
adapterSemicolon src a mid Idapter tgt = return a
adapterSemicolon (List src) (Hom a) (List mid) b (List tgt) = do
  let ab = Lam $ ((a ::: Pi src (List mid)) :$ E (V 0)) :-: b
  return (Hom ab)
  -- weakEvalAdapter (List src) (Hom ab) (List tgt)
adapterSemicolon (List src) (List a) (List mid) (Hom b) (List tgt) = do
  let ab = Lam $ E ((b ::: Pi mid (List tgt)) :$ E ((a ::: Pi src mid) :$ E (V 0)))
  return (Hom ab)
  -- weakEvalAdapter (List src) (Hom ab) (List tgt)
adapterSemicolon (List src) (List a) (List mid) (List b) (List tgt) = do
  let ab = Lam $ E ((b ::: Pi mid tgt) :$ E ((a ::: Pi src mid) :$ E (V 0)))
  return (List ab)
  -- weakEvalAdapter (List src) (List ab) (List tgt)
adapterSemicolon inn@(Thinning src ga0 de0) a (Thinning mid ga1 de1) b out@(Thinning tgt ga2 de2) = do
  let (fa, tha, pha) = expandThinAdapter a
  let (fb, thb, phb) = expandThinAdapter b
  let fab = Lam $ E ((fb ::: Pi mid tgt) :$ E ((fa ::: Pi src mid) :$ E (V 0)))
  return (Thinning fab (ThSemi thb tha) (ThSemi pha phb))
  -- weakEvalAdapter inn (Thinning fab (ThSemi thb tha) (ThSemi pha phb)) out
adapterSemicolon inn@(AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys) (AllT f' g' ph) (AllT _Z _R zs) = do
  let fr = f ::: Pi _Y _X
  let gr = g ::: Pi _Y (Pi (_P // (fr :$ E (V 0))) (_Q <^> o' mempty))
  let f'r = f' ::: Pi _Z _Y
  let g'r = g' ::: Pi _Z (Pi (_Q // (f'r :$ E (V 0))) (_R <^> o' mempty))
  let ff' = Lam $ E (fr :$ E (f'r :$ E (V 0)))
  let gg' = Lam $ Lam $ E (g'r :$ E (V 1) :$ E ((gr :$ E (f'r :$ E (V 1))) :$ E (V 0)))
  let pha = (ph ::: Thinning _Y ((zs ::: List _Z) :-: List f') ys) :-: List f -- Thinning _X (zs :-: List f';f) (ys :-: List f)
  let phath = ThSemi pha th
  return (AllT ff' gg' phath)

expandThinAdapter :: Adapter -> (ChkTm, ChkTm, ChkTm)
expandThinAdapter Idapter = (Lam (E (V 0)), Th1, Th1)
expandThinAdapter (List f) = (f, Th1, Th1)
expandThinAdapter (Thinning f th ph) = (f, th, ph)

expandTh0 :: ChkTm -> ChkTm -> TCM ChkTm
expandTh0 _X de = do
  de <- weakChkEval (List _X, de)
  case consView de of
    Nil -> return NoThin
    Cons x de -> Cons Th0 <$> expandTh0 _X de
    ys -> return Th0

etaThinning :: SynTm -> ChkTm -> TCM ChkTm
etaThinning e src | track ("etaThinning:\n   e = " ++ show e ++ "\n   src = " ++ show src) False = undefined
etaThinning e (Thinning _W ga0 de0) = do
  ga0 <- weakChkEval (List _W, ga0)
  case ga0 of
    Nil -> expandTh0 _W de0
    _   -> return (upsE e)

isNormalIdThinning :: ChkTm -> Bool
isNormalIdThinning Nil           = True
isNormalIdThinning Th1           = True
isNormalIdThinning (Cons Th1 th) = isNormalIdThinning th
isNormalIdThinning _             = False

consThView :: ChkTm -> ChkTm
consThView Th0 = Cons Th0 Th0
consThView Th1 = Cons Th1 Th1
consThView th = th


-- assumes argument is head normal
consView :: ChkTm -> ChkTm
consView (Single x) = Cons x Nil
consView xs = xs

-- _X is element type
-- th is thinning to be evaled
-- de is head normal
-- returns (origin, evaled thinning)
weakChkThinning :: ChkTm -> ChkTm -> ChkTm -> TCM (ChkTm, ChkTm)
weakChkThinning _X th de | track ("weakChkThinning:\n   th = " ++ show th ++ "\n   de = " ++ show de ++ "\n") False = undefined
weakChkThinning _X th de = case th of
  Th1 -> case consView de of
    Nil -> return (Nil, NoThin)
    (Cons x de) -> do
      de <- weakChkEval (List _X, de)
      (ga, th) <- weakChkThinning _X Th1 de
      return (Cons x ga, Cons Th1 th)
    _ -> return (de, Th1)
  Th0 -> do
    th0 <- expandTh0 _X de
    return (Nil, th0)
  NoThin -> return (Nil, NoThin)
  Cons Th1 th -> case consView de of
    Cons x de -> do
      de <- weakChkEval (List _X, de)
      (ga, th) <- weakChkThinning _X th de
      return (Cons x ga, Cons Th1 th)
    de -> error $ "de = " ++ show de ++ " th = " ++ show th
  Cons Th0 th -> case consView de of
    Cons x de -> do
      de <- weakChkEval (List _X, de)
      (ga, th) <- weakChkThinning _X th de
      return (ga, Cons Th0 th)
  ThSemi th ph -> do
    (mu, ph) <- weakChkThinning _X ph de
    (ga, th) <- weakChkThinning _X th mu
    case ga of
      Nil -> do
        th0 <- expandTh0 _X de
        return (Nil, th0)
      _ | isNormalIdThinning th -> return (ga, ph)
        | isNormalIdThinning ph -> return (ga, th)
      _ -> case ph of
        Cons Th0 ph -> case consView de of
          Cons x de -> do
            de <- weakChkEval (List _X, de)
            (ga, ps) <- weakChkThinning _X (ThSemi th ph) de
            return (ga, Cons Th0 ps)
        Cons Th1 ph -> case consView de of
          Cons x de -> case th of
            Cons b th -> do
              de <- weakChkEval (List _X, de)
              (ga, ps) <- weakChkThinning _X (ThSemi th ph) de
              return (Cons x ga, Cons b ps)
            _ -> return (ga, ThSemi th (Cons Th1 ph))
        ThSemi ph0 ph1 -> do
          (ka, ph1) <- weakChkThinning _X ph1 de
          (_, ps0) <- weakChkThinning _X (ThSemi th ph0) ka
          weakChkThinning _X (ThSemi ps0 ph1) de
        _ -> return (ga, ThSemi th ph)
  e :-: a -> do
    (e, src) <- weakEvalSyn e
    th <- etaThinning e src
    (ga, tgt) <- reconstructThinningAdapterTarget src a _X de
    -- a <- weakEvalAdapter src a tgt
    t <- weakAdapt (th ::: src) src a tgt
    return (ga, t)


reconstructThinningAdapterTarget :: ChkTm -> Adapter -> ChkTm -> ChkTm -> TCM (ChkTm, ChkTm)
reconstructThinningAdapterTarget src@(Thinning _W ga0 de0) a _X de = do
  ga0 <- weakChkEval (List _W, ga0)
  case a of
    Idapter -> return (ga0, src)
    List f  -> do
      ga <- weakChkEval (List _X, (ga0 ::: List _W) :-: List f)
      return (ga, Thinning _X ga de)
    Thinning f ph ps -> do
      lfga0 <- weakChkEval (List _X, (ga0 ::: List _W) :-: List f)
      (ga, _) <- weakChkThinning _X ph lfga0
      return (ga, Thinning _X ga de)


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
weakEvalSyn x | track ("syn:\n   " ++ show x ++ "\n") False = undefined
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
      ((e' :-: a) ::: _) -> do
        (e', src) <- weakEvalSyn e'
        case [ (m ++ msrc ++ ma, rhs) | (psrc, pa, rhs) <- fusionRules rule, msrc <- trail (match psrc src), ma <- trail (match pa a) ] of
          [(m, rhs)] -> return (e' :$ instantiate m rhs)
          [] -> return (e :$ s)
          _ -> fail "weakEvalSyn: more than one fusion rule applies"
      (t ::: _) -> runProg m t (betaRules rule) >>= \case
        Just y -> do
          r <- weakChkEval (rTy, y)
          return (r ::: rTy)
        Nothing -> return (e :$ s)
      _ -> return (e :$ s)

normalise = fst normalisers
normStop  = snd normalisers

normalisers :: ((Type, ChkTm) -> TCM ChkTm, SynTm -> TCM (SynTm, Type))
normalisers = (refresh "n" . go, refresh "n" . stop) where
  go (Ty, e) = weakChkEval (Ty, e) >>= \case
    Ty -> return Ty
    Atom -> return Atom
    Enum as -> do
      as' <- go (List Atom, as)
      return (Enum as')
    Pi s t -> do
      s' <- go (Ty, s)
      t' <- fresh ("x", s) $ \ x -> go (Ty, t // x)
      return (Pi s' t')
    Sg s t -> do
      s' <- go (Ty, s)
      t' <- fresh ("y", s) $ \ y -> go (Ty, t // y)
      return (Sg s' t')
    One -> return One
    List s -> do
      s' <- go (Ty, s)
      return (List s')
    AllT _X _P xs -> do
      _X' <- go (Ty, _X)
      _P' <- fresh ("x", _X) $ \ x -> go (Ty, _P // x)
      xs' <- go (List _X, xs)
      return (AllT _X' _P' xs')
    Thinning _X ga de -> do
      _X' <- go (Ty, _X)
      ga' <- go (List _X, ga)
      de' <- go (List _X, de)
      return (Thinning _X' ga' de')
    FAb _X -> do
      _X' <- go (Ty, _X)
      return (FAb _X')
    e :-: a -> do
      (e', src) <- stop e
      a' <- quad src a Ty
      return (e' :-: a')
    x -> error $ "hm " ++ show x
  go (Atom, e) = weakChkEval (Atom, e) >>= \case
    A s -> return (A s)
    E e -> (upsE .fst) <$> stop e
  go (Enum as, x) = weakChkEval (Enum as, x) >>= \case
    Z -> return Z
    S x -> (consView <$> weakChkEval (List Atom, as)) >>= \case
      Cons _ as -> S <$> go (Enum as, x)
    E e -> (upsE .fst) <$> stop e
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
      xs :++: ys -> (++++) <$> go (List _X, xs) <*> go (List _X, ys)
      e :-: a -> do
        (e', src) <- stop e
        a' <- quad src a (List _X)
        return (e' :-: a')
  go (AllT _X _P xs, ps) = consView <$> weakChkEval (List _X, xs) >>= \case
    Nil -> return Nil
    Cons x xs' ->
      Cons <$> go (_P // (x ::: _X), E ((((ps ::: AllT _X _P xs) :-: AllT (Lam $ E (V 0)) (Lam (Lam $ E (V 0))) (Cons Th1 Th0)) ::: AllT _X _P (Single x)) :$ Only))
           <*> go (AllT _X _P xs', (ps ::: AllT _X _P xs) :-: AllT (Lam $ E (V 0)) (Lam (Lam $ E (V 0))) (Cons Th0 Th1))
    _ -> weakChkEval (AllT _X _P xs, ps) >>= \case
      e :-: a -> do
        (e', src) <- stop e
        a' <- quad src a (AllT _X _P xs)
        return (e' :-: a')
  go (ty@(Thinning _X ga de), th) = do
    th <- weakChkEval (ty, th)
    de <- weakChkEval (List _X, de)
    snd <$> quoth _X th de
  go (FAb _X, x) = weakChkEval (FAb _X, x)
  go (E ty, E e) = do -- only canonical types have non-Idapter adapters
    (e, _) <- weakEvalSyn e
    (e', _) <- stop e
    return (E e')

  quoth :: ChkTm -> ChkTm -> ChkTm -> TCM (ChkTm, ChkTm)
  quoth _X Th0 de = return (Nil, Th0)
  quoth _X Th1 de = return (de, Th1)
  quoth _X NoThin de = return (Nil, NoThin)
  quoth _X (Cons b th) de = case consView de of
    Cons x de -> do
      de <- weakChkEval (List _X, de)
      (ga, th') <- quoth _X th de
      case b of
        Th0 -> return (ga, Cons Th0 th')
        Th1 -> return (Cons x ga, Cons Th1 th')
  quoth _X (ThSemi th ph) de = do
    (ka, ph') <- quoth _X ph de
    (ga, th') <- quoth _X th ka
    return (ga, ThSemi th' ph')
  quoth _X (e :-: a) de = do
    (e', src) <- stop e
    (ga, tgt) <- reconstructThinningAdapterTarget src a _X de
    a' <- quad src a tgt
    return (ga, e' :-: a')

  quad :: ChkTm -> Adapter -> ChkTm -> TCM Adapter
  quad src Idapter tgt = return Idapter
  quad (List src) (Hom f) (List tgt) = do
    isMap <- fresh ("x", src) $ \ x@(P n ty) -> go (List tgt, E ((f ::: Pi src (List tgt)) :$ E x)) >>= \case
      Single t -> return (Just (Lam (n \\ t)))
      _ -> return Nothing
    case isMap of
      Just g -> quad (List src) (List g) (List tgt)
      Nothing -> do
        f' <- go (Pi src (List tgt), f)
        return (Hom f')
  quad (List src) (List f) (List tgt) = do
    eq <- mandy (checkEquality Ty src tgt) (checkEquality (Pi src tgt) f (Lam (E (V 0))))
    if eq then return Idapter else do
      f' <- go (Pi src tgt, f)
      return (List f')
  quad (Thinning src ga de) (List f) (Thinning tgt ga' de') = quad (List src) (List f) (List tgt)
  quad (Thinning src ga de) (Thinning f th ph) (Thinning tgt ga' de') = do
    lfga <- weakChkEval (List tgt, (ga ::: List src) :-: List f)
    lfde <- weakChkEval (List tgt, (de ::: List src) :-: List f)
    th <- weakChkEval (Thinning tgt ga' lfga, th)
    ph <- weakChkEval (Thinning tgt lfde de', ph)
    if isNormalIdThinning th && isNormalIdThinning ph
      then quad (List src) (List f) (List tgt)
      else return (Thinning f th ph)
  quad (AllT _X _P xs) (AllT f g th) (AllT _Y _Q ys) = do
    eq <- mandy (mandy (checkEquality Ty _Y _X) (checkEquality (Pi _Y _X) f (Lam (E (V 0)))))
                (mandy (fresh ("y", _Y) $ \ y -> checkEquality Ty (_P // y) (_Q // y))
                       (checkEquality (Pi _Y (Pi _P (_Q <^> o' mempty))) g (Lam $ Lam (E (V 0)))))
    eqTh <- checkEquality (List _X) xs ((ys ::: List _Y) :-: List f) -- if so, th must be id
    if eqTh && eq then return Idapter
      else do
        f' <- go (Pi _Y _X, f)
        g' <- go (Pi _Y (Pi (_P // ((f ::: Pi _Y _X) :$ (E (V 0)))) (_Q <^> o' mempty)), g)
        th' <- if eqTh then return Th1 else snd <$> quoth _X th xs
        return (AllT f' g' th')

  stop :: SynTm -> TCM (SynTm, Type)
  stop (V i) = error "normalise: applied to non-closed term"
  stop (P n ty) = (,) <$> vP n ty <*> weakChkEval (Ty, unHide ty)
  stop ((e :-: a) ::: t) = do
    (e', ty) <- stop e
    a' <- quad ty a t
    case a' of
      Idapter -> return (e', ty)
      _ -> do
        t' <- go (Ty, t)
        return ((e' :-: a') ::: t', t)
  stop (s ::: t) = error $ "normalise: failure of canonicity s = " ++ show s ++ " t = " ++ show t
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
  prem ([] :- p) | track ("prem:\n   " ++ show p) True = go p
  prem (((y, ty):hs) :- p) = fresh (y, ty) $ \ y -> prem ((hs :- p) // y)

normSyn :: SynTm -> TCM ChkTm
normSyn e = do
  (e, t) <- weakEvalSyn e
  normalise (t, upsE e)

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
  , betaRules = [(Lam (pm "t"), Ret $ M ("t" :/ si))]
  , fusionRules = []
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
  , betaRules = [(pm "s" :& pm "t", Ret $ em "s")]
  , fusionRules = []
  }

sndElim = ElimRule
  { targetType = Sg (pm "S") (pm "T")
  , eliminator = Snd
  , elimPremisses = []
  , reductType = M ("T" :/ si)
  , betaRules = [(pm "s" :& pm "t", Ret $ em "t")]
  , fusionRules = []
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

pattern Hom f = A "hom" :& f

infixr 4 :++:, ++++

(++++) :: ChkTm -> ChkTm -> ChkTm
Nil ++++ bs = bs
as ++++ Nil = as
(as :++: bs) ++++ cs =  as ++++ (bs ++++ cs)
as ++++ bs = as :++: bs

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
    [ (Nil, Ret $ em "n")
    , (Single (pm "x"), Ret $
       M ("c" :/ (B0
         :< (em "x" ::: em "X")
         :< (Nil ::: List (em "X"))
         :< (em "n" ::: M ("P" :/ (B0 :< (Nil ::: List (em "X"))))))))
    , (pm "xs" :++: pm "ys", Ret $
       E ((em "xs" ::: List (em "X")) :$ ListElim
         (M ("P" :/ (B0 :< ((E (V 0) :++: em "ys") ::: List (em "X")))))
         (E ((em "ys" ::: List (em "X")) :$ ListElim (em "P") (em "n") (em "c")))
         (M ("c" :/ (B0 :< V 2 :< ((E (V 1) :++: em "ys") ::: List (em "X")) :< V 0)))))
    ]
  , fusionRules =
    [ (List (pm "W"), List (pm "f"), ListElim (M ("P" :/ (B0 :< ((V 0 :-: List (em "f")) ::: List (em "X"))))) (em "n")
        (M ("c" :/ (B0
            :< ((em "f" ::: Pi (em "W") (em "X")) :$ E (V 2))
            :< ((V 1 :-: List (em "f")) ::: List (em "X"))
            :< V 0))))
    , (List (pm "W"), Hom (pm "f"), ListElim (M ("P" :/ (B0 :< ((V 0 :-: Hom (em "f")) ::: List (em "X"))))) (em "n")
        (E ((em "f" ::: Pi (em "W") (List (em "X"))) :$ E (V 2) :$
             ListElim (M ("P" :/ (B0 :< ((E (V 0) :++: (V 2 :-: Hom (em "f")) ::: List (em "X"))))))
                      (E (V 0))
                      (M ("c" :/ (B0
                         :< V 2
                         :< ((E (V 1) :++: (V 4 :-: Hom (em "f"))) ::: List (em "X"))
                         :< V 0))))))
    ]
  }

-- Predicate lifting of List

pattern AllT _X _P xs = A "All" :& _X :& (B _P) :& xs
-- constructors overloaded Nil, Single, :++:

pattern Only = A "only"

onlyElim = ElimRule
  { targetType = AllT (pm "X") (pm "P") (Single (pm "x"))
  , eliminator = Only
  , elimPremisses = []
  , reductType = M ("P" :/ (B0 :< (em "x" ::: em "X")))
  , betaRules =
    [ (Single (pm "p"), Ret $ em "p")
    ]
  , fusionRules =
    [ (AllT (pm "Y") (pm "Q") (pm "ys"), AllT (pm "f") (pm "g") (pm "th"),
       E ((em "g" ::: Pi (em "X") (Pi (M ("Q" :/ (B0 :< ((em "f" ::: Pi (em "X") (em "Y")) :$ em "x")))) (M ("P" :/ (B0 :< V 1))))) :$ em "x" :$ E (V 0 :$ Only)))
    ]
  }


-- what would happen if we defined All : (List Type) -> Type instead of AllT?
-- (AllT X P xs = All (map P xs) ; All Xs = AllT Type (\ x -> x) Xs )

pattern AllP _P _Acc = A "All" :& (B _P) :& _Acc

-- for now, we compute it recursively. In the long run, to take
-- advantage of structure (eg naturality of selection, that it is a
-- presheaf...), we want to use the inductive version in order to
-- expose said structure more easily

allPElim = ElimRule
  { targetType = List (pm "X")
  , eliminator = AllP (pm "P") (pm "Acc")
  , elimPremisses =
    [ [("x", em "X")] :- (Ty, "P" :/ B0)
    , [] :- (Ty, "Acc" :/ B0)
    ]
  , reductType = Ty
  , betaRules =
    [ (Nil, Ret $ em "Acc")
    , (Single (pm "x"), Ret $
       Sg (M ("P" :/ (B0 :< (em "x" ::: em "X")))) (em "Acc"))
    , (pm "xs" :++: pm "ys", Ret $
       E ((em "xs" ::: List (em "X")) :$ AllP (em "P") (E ((em "ys" ::: List (em "X")) :$ AllP (em "P") (em "Acc")))))
    ]

  , fusionRules =
    [ (List (pm "W"), List (pm "f"), AllP (M ("P" :/ (B0 :< ((em "f" ::: Pi (em "W") (em "X")) :$ E (V 0))))) (em "Acc"))
    ]
  }



-- Nat

pattern Nat = List One

pattern Z = Nil
pattern S x = Cons Void x


instance Num (Chk a) where
  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n-1))
  (+) = error "TODO"
  (*) = error "TODO"
  (-) = error "TODO"
  abs = error "TODO"
  signum = error "TODO"

-- Thinnings

pattern Thinning _X ga de = A "Th" :& _X :& ga :& de

pattern Th1 = A "1"  -- id thinning between neutral lists (also a bit)
pattern Th0 = A "0"  -- empty thinning from Nil to a neutral lists (also a bit)
pattern NoThin = Nil -- the thinning from Nil to Nil
pattern ThSemi th th' = A ";" :& th :& th'

-- Atoms

pattern Atom = A "Atom"

  -- introduced by `A s` for nonempty `s`

-- Enumerations

pattern Enum as = A "Enum" :& as -- as is a list of Atoms

pattern EnumElim _P ms = A "EnumElim" :& (B _P) :& ms

  -- introduced by a number (less than the length of as), or, also an Atom in the list (optionally paired with a number)

enumElim = ElimRule
  { targetType = Enum (pm "as")
  , eliminator = EnumElim (pm "P") (pm "ms")
  , elimPremisses =
    [ [("es", Enum (em "as"))] :- (Ty, "P" :/ B0)
    , [] :- (E ((em "as" ::: List Atom) :$ AllP (em "P") One), "ms" :/ B0)
    ]
  , reductType = M ("P" :/ (B0 :< V 0))
  , betaRules =
    [ (Z, Ret . E $ (em "ms" ::: E ((em "as" ::: List Atom) :$ AllP (em "P") One)) :$ Fst)
    , (S (pm "x"), Case (List Atom) (em "as")
                 [(Cons (pm "a") (pm "as'"), Ret . E $
                    (em "x" ::: Enum (em "as'")) :$
                        EnumElim (M ("P" :/ (B0 :< (S (E (V 0)) ::: Enum (em "as")))))
                               (E ((em "ms" ::: E ((em "as" ::: List Atom) :$ AllP (em "P") One)) :$ Snd)))])
    ]
  , fusionRules = []
  }

-- Free Abelian groups

pattern FAb _X = A "FAb" :& _X
pattern Eta x = A "Eta" :& x
pattern FOne = A "1"
pattern (:.:) x y = A "*" :& x :& y
pattern Inv x = A "Inv" :& x


-- Kit

newtype I x = I { unI :: x }
  deriving (Functor, Foldable, Traversable)

instance Applicative I where
  pure = I
  I f <*> I a = I (f a)

newtype K a x = K { unK :: a }
  deriving (Functor, Foldable, Traversable)

data (f :*: g) x = (:*:) { outL :: f x , outR :: g x }
  deriving (Functor, Foldable, Traversable)

data (f :+: g) x = InL (f x) | InR (g x)
  deriving (Functor, Foldable, Traversable)

ourSetup = Setup
  { elimRules = [piElim, fstElim, sndElim, listElim, allPElim, enumElim, onlyElim]
  , weakAnalyserSetup = \ x -> case x of
      (Ty, Enum as) -> return $ Just $ WeakAnalysis (I (List Atom, as)) (\ (I as') -> Enum as')
      (Ty, AllT _X _P xs) -> return $ Just $ WeakAnalysis (I (Ty, _X) :*: I (List _X, xs)) (\ (I _X' :*: I xs') -> AllT _X' _P xs')
      (Ty, Pi s t) -> return $ Just $ WeakAnalysis (I (Ty, s)) (\ (I s') -> Pi s' t)
      (Ty, Sg s t) -> return $ Just $ WeakAnalysis (I (Ty, s)) (\ (I s') -> Sg s' t)
      (Sg s t, x :& y) -> do
        t <- weakChkEval (Ty, t // (x ::: s))
        return $ Just $ WeakAnalysis (I (s, x) :*: I (t , y)) (\ (I x' :*: I y') -> (x' :& y'))
      _ -> return $ Nothing
  }


run :: TCM x -> Either String x
run x = runTCM x ourSetup initNameSupply

chkEval = run . weakChkEval
evalSyn = run . weakEvalSyn


-- type-directed printing

printNormSyn :: SynTm -> IO ()
printNormSyn e = putStrLn . either id id . run $ do
  (e, t) <- weakEvalSyn e
  n <- normalise (t, upsE e)
  refresh "print" $ chkPrint t n 0

chkPrint :: ChkTm -> ChkTm -> Int -> TCM String
chkPrint Ty _T p = case _T of
  Ty -> return "Ty"
  Atom -> return "Atom"
  Enum as -> do
    as' <- chkPrint (List Atom) as pArg
    return . paren p pArg $ concat ["Enum ", as']
  Pi _S _T -> do
    _S' <- chkPrint Ty _S 0
    (v, _T') <- fresh (nomo _S, _S) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_T // x) 0
    return . paren p pArg $ concat ["(", v, " : ", _S', ") -> ", _T']
  Sg _S _T ->  do
    _S' <- chkPrint Ty _S 0
    (v, _T') <- fresh (nomo _S, _S) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_T // x) 0
    return . paren p pArg $ concat ["(", v, " : ", _S', ") * ", _T']
  One -> return "1"
  Nat -> return "Nat"
  List _X -> do
    _X' <- chkPrint Ty _X pArg
    return . paren p pArg $ concat ["List ", _X']
  FAb _X -> do
    _X' <- chkPrint Ty _X pArg
    return . paren p pArg $ concat ["FAb ", _X']
  AllT _X _P xs -> do
    _X' <- chkPrint Ty _X 0
    (v, _P') <- fresh (nomo _X, _X) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_P // x) 0
    xs' <- chkPrint (List _X) xs pScope
    return $ "[" ++ _P' ++ " | (" ++ v ++ " : " ++ _X' ++ ") <- " ++ xs' ++ "]"
  Thinning _X ga de -> do
    _X' <- chkPrint Ty _X 0
    ga' <- chkPrint (List _X) ga pScope
    de' <- chkPrint (List _X) de pScope
    return . paren p pArg $ concat [ga', " <[", _X', "]= ", de']
  e :-: Idapter -> fst <$> printSyn e p
  _X -> return $ "(" ++ show _X ++ ")"
chkPrint Atom a p = case a of
  A s -> return ("'" ++ s)
  e :-: Idapter -> fst <$> printSyn e p
chkPrint (Enum as) x p = tryATag as x >>= \case
  Just (s, n) -> return ("'" ++ s ++ if n == 0 then "" else "^" ++ show n)
  Nothing -> notATag 0 x p
chkPrint _T@(Pi _ _) f p = case f of
    Lam _ -> paren p pArg <$> lams "" _T f
    e :-: Idapter -> fst <$> printSyn e p
    _ -> return $ "(" ++ show f ++ ")"
  where
    lams args (Pi _S _T) (Lam t) = fresh (nomo _S, _S) $ \ x -> do
      (v, _) <- printSyn x 0
      lams (args ++ v ++ " ") (_T // x) (t // x)
    lams args _X x = do
      body <- chkPrint _X x 0
      return . concat $ ["\\ ", args, "-> ", body]
chkPrint (Sg _S _T) (s :& t) p = do
  s' <- chkPrint _S s pElt
  _T <- weakChkEval (Ty, _T // (s ::: _S))
  t' <- chkPrint _T t pCdr
  return . paren p pElt $ concat [s', ", ", t']
chkPrint One _ _ = return "<>"
chkPrint Nat n p = either show (paren p pArg) <$> munch n where
  munch :: ChkTm -> TCM (Either Int String)
  munch Nil = return $ Left 0
  munch (Single _) = return $ Left 1
  munch (x :++: y) = do
    x <- munch x
    y <- munch y
    case (x, y) of
      (Left x, Left y) -> return . Left $ x + y
      _ -> return . Right $ concat
        [either show id x, "+", either show id y]
  munch (E e) = (Right . fst) <$> printSyn e pArg
  munch (e :-: _) = do
    (s, _) <- printSyn e pArg
    return . Right $ concat ["|", s, "|"]
  munch x = return . Right $ show x
chkPrint (List _X) xs p = blat <$> munch xs where
  munch :: ChkTm -> TCM (String, Bool, String)
  munch Nil = return ("", False, "")
  munch (Single x) = (\ s -> (s, False, "")) <$> chkPrint _X x pElt
  munch (xs :++: ys) = glom <$> munch xs <*> munch ys
  munch (E e) = (\ (s, _) -> ("", False, s)) <$> printSyn e pArg
  munch (e :-: List f) = printSyn e pArg >>= \case
    (s, List _S) -> do
      f <- chkPrint (Pi _S _X) f pArg
      return $ ("", True, concat ["List ", f, " ", s])
  munch (e :-: Hom f) = printSyn e pArg >>= \case
    (s, List _S) -> do
      f <- chkPrint (Pi _S (List _X)) f pArg
      return $ ("", True, concat [f , " =<< ", s])
  munch x = return $ ("", True, show x)
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " ++ " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " ++ ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " ++ [", ys, "] ++ ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] ++ ", ys]
chkPrint (AllT _X _Q xs) qs p = (blat . snd) <$> munch xs qs where
  munch :: ChkTm -> ChkTm -> TCM (ChkTm, (String, Bool, String))
  munch xs Nil = return (xs, ("", False, ""))
  munch xs (Single q) = do
    xs <- weakChkEval (List _X, xs)
    case consView xs of
      Cons x xs -> (\ s -> (xs, (s, False, ""))) <$> chkPrint (_Q // (x ::: _X)) q pElt
  munch xs (qs :++: rs) = do
    (xs, pqs) <- munch xs qs
    (xs, prs) <- munch xs rs
    return (xs, glom pqs prs)
  munch xs (e :-: Idapter) = printSyn e pArg >>= \case
    (e, AllT _X' _P' xs') -> do
      leftovers <- unprefix _X xs xs'
      return (leftovers, (e, False, ""))
  munch xs (e :-:  AllT f g th) = printSyn e pArg >>= \case
    (s, AllT _W _R ws) -> do
    -- f : _W -> _X
    -- g : (w : _W) -> _Q (f w) -> R w
    -- th : Thinning _X ws' ws
    ws <- weakChkEval (List _W, ws)
    (ws', th) <- weakChkThinning _W th ws
    (_, xs'') <- unmapprefix _X f _W xs ws'

    g <- chkPrint (Pi _W (Pi (_Q // ((f ::: Pi _W _X) :$ E (V 0))) (_R <^> o' mempty))) g pArg
    f <- chkPrint (Pi _W _X) f pArg
    th <- chkPrint (Thinning _W ws' ws) th pArg

    return (xs'', ("", True, concat ["All ", f, " ", g, " ", th, " ", s]))
  munch xs qs = return $ (xs, ("", True, show qs))
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " ++ " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " ++ ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " ++ [", ys, "] ++ ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] ++ ", ys]
chkPrint (FAb _X) xs p = blat <$> munch xs True where
  munch :: ChkTm -> Bool -> TCM (String, Bool, String)
  munch FOne _ = return ("", False, "")
  munch (Eta x) b = (\ s -> (s ++ (if b then "" else "^"), False, "")) <$> chkPrint _X x pElt
  munch (Inv xs) b = munch xs (not b)
  munch (xs :.: ys) b = glom <$> munch xs b <*> munch ys b
  munch (E e) b = (\ (s, _) -> ("", False, if b then s else "(" ++ s ++ ")^")) <$> printSyn e pArg
{-
  munch (e :-: List f) = do
    (s, _S) <- printSyn e pArg
    f <- chkPrint (Pi _S (List _X)) f pArg
    return $ ("", True, concat ["List ", f, " ", s])
-}
  munch x b = return $ ("", True, if b then show x else "(" ++ show x ++ ")^")
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " * " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " * ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " * [", ys, "] * ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] * ", ys]
chkPrint (Thinning _X ga de) th p = munch th where
  munch :: ChkTm -> TCM String
  munch Nil = return $ "."
  munch Th0 = return $ "0.."
  munch Th1 = return $ "1.."
  munch (Cons (A a) th) = (a ++) <$> munch th
  munch (ThSemi th ph) = do
    th <- munch th
    ph <- munch ph
    return $ concat ["(",th,";",ph,")"]
  munch (E e) = fst <$> printSyn e pArg
  munch x@(e :-: List f) = do
    (e, src) <- printSyn e pArg
    case src of
      Thinning _W _ _ -> do
        f <- chkPrint (Pi _W _X) f pArg
        return $ concat ["(List ", f, " ", e, ")"]
      _ -> return $ show x
  munch x = return $ show x
chkPrint _ (E e) p = fst <$> printSyn e p
chkPrint _ t _ = return $ "(" ++ show t ++ ")"

printSyn :: SynTm -> Int -> TCM (String, ChkTm)
printSyn (P x (Hide t)) _ = (, t) <$> pNom x
printSyn (e :$ s) p = do
  (e', _T) <- printSyn e pTarg
  case _T of
    Pi _S _T -> do
      _S <- weakChkEval (Ty, _S)
      s' <- chkPrint _S s pArg
      _T <- weakChkEval (Ty, _T // (s ::: _S))
      return . (, _T) . paren p (pTarg + 1) $ concat
        [e', " ", s']
    Sg _S _T -> case s of
        Fst -> return (paren p (pTarg + 1) (e' ++ " -fst"), _S)
        Snd -> do
          _T <- weakChkEval (Ty, _T // (e :$ Fst))
          return (paren p (pTarg + 1) (e' ++ " -snd"), _S)
        _ -> return . (, _T) . paren p (pTarg + 1) $ concat
          [e', " (", show s, ")"]
    List _X -> case s of
      AllP _P _Acc -> do
        (p', _P') <- fresh (nomo _X, _X) $ \ x ->
                     (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_P // x) 0
        acc <- case _Acc of
          One -> return ""
          _ -> ("; " ++) <$> chkPrint Ty _Acc 0
        let out = "[" ++ _P' ++ " | " ++ p' ++ " <- " ++ e' ++ acc ++ "]"
        return (out , Ty)
      ListElim _P n c -> do
        fresh ("fun", Pi (List _X) _P) $ \ fun -> do
          (funh, _) <- printSyn fun 0
          funTy <- chkPrint Ty (Pi (List _X) _P) 0
          (funNl, _N) <- printSyn (fun :$ Nil) 0
          _N <- weakChkEval (Ty, _N)
          funNr <- chkPrint _N n 0
          cq <- fresh (nomo _X, _X) $ \ x ->
                fresh (nomo (List _X), List _X) $ \ xs -> do
            (funCl, _C) <- printSyn (fun :$ Cons (E x) (E xs)) 0
            _C <- weakChkEval (Ty, _C)
            funCr <- chkPrint _C (c // (fun :$ E xs) // xs // x) 0
            return $ concat [funCl, " = ", funCr]
          (body, _T) <- printSyn (fun :$ E e) pTarg
          _T <- weakChkEval (Ty, _T)
          return . (, _T) . paren p pTarg $ concat
            [ "let ", funh, " : ", funTy, "; "
            , funNl, " = ", funNr, "; "
            , cq, " in " , body
            ]
      _ -> return . (, _T) . paren p (pTarg + 1) $ concat
        [e', " (", show s, ")"]
    _ -> return . (, _T) . paren p (pTarg + 1) $ concat
      [e', " (", show s, ")"]
printSyn e p = do
  (_, t) <- weakEvalSyn e
  return $ ("(" ++ show e ++ ")", t)

tryATag :: ChkTm -> ChkTm -> TCM (Maybe (String, Int))
tryATag as Z = (consView <$> weakChkEval (List Atom, as)) >>= \case
  Cons a _ -> weakChkEval (Atom, a) >>= \case
    A s -> return (Just (s, 0))
    _   -> return Nothing
  _ -> fail ("out of bounds as = " ++ show as)
tryATag as (S x) = (consView <$> weakChkEval (List Atom, as)) >>= \case
  Cons a as -> weakChkEval (Atom, a) >>= \case
    A a -> tryATag as x >>= \case
      Just (s, n) -> return (Just (s, if a == s then n+1 else n))
      Nothing -> return Nothing
    _   -> return Nothing
  _ -> fail ("out of bounds as = " ++ show as ++ " x = " ++ show x)
tryATag _ _ = return Nothing

notATag :: Int -> ChkTm -> Int -> TCM String
notATag acc Z p = return (show acc)
notATag acc (S x) p = notATag (acc+1) x p
notATag acc (E e) p = do
  (s, _) <- printSyn e (if acc == 0 then p else pCdr)
  if acc == 0 then return s else return (paren p pArg (show acc ++ " + " ++ s))

paren :: Int -> Int -> String -> String
paren p l x = if p >= l then concat ["(", x, ")"] else x

pArg, pTarg, pElt, pCdr, pScope :: Int
pArg = 60
pTarg = 50
pElt = 40
pCdr = 30
pScope = 10

nomo :: ChkTm -> String
nomo Ty = "X"
nomo (Pi _ _T) = if toTy _T then "F" else "f" where
  toTy Ty = True
  toTy (Pi _ _T) = toTy _T
  toTy (Sg _S _T) = toTy _S || toTy _T
  toTy _ = False
nomo (Sg _S _T) = nomo _S ++ nomo _T
nomo (List One) = "n"
nomo (List _X) = nomo _X ++ "s"
nomo (Thinning _ _ _) = "th"
nomo _ = "x"


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

funTy = Pi Nat (Pi (Thinning One Nil (E (V 0))) (Thinning One Nil (E (V 1))))

list0 = Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))

th0 = Cons Th0 (ThSemi (E $ P [("b", 0)] (Hide $ Thinning Nat list0 list0)) (E $ P [("b", 1)] (Hide $ Thinning Nat list0 list0)))
th1 = ThSemi (E $ P [("b", 2)] (Hide $ Thinning Nat list0 list0)) th0
th1Ty = Thinning Nat list0 (Cons Z list0)

list0' = (list0 ::: List Nat) :-: List (Lam (S (E (V 0))))

swap = Lam $ E (V 0 :$ Snd) :& E (V 0 :$ Fst)

swapswapper = Lam (((V 0 :-: List swap) ::: List (Sg Ty Nat)) :-: List swap) ::: Pi (List (Sg Nat Ty)) (List (Sg Nat Ty))

unitswapper = Lam (V 0 :-: List swap) ::: Pi (List (Sg One One)) (List (Sg One One))

dup = Lam (E (V 0) :& E (V 0))

adaptTh1Ty = Thinning (Sg Nat Nat) ((list0 ::: List Nat) :-: List dup) ((Cons Z list0 ::: List Nat) :-: List dup)

adaptTh1 = ((th1 ::: th1Ty) :-: List dup)
              ::: adaptTh1Ty

revMappedPartlyNeutralList = ((((E (P [("ys", 0)] (Hide (List Ty))) :++: E myTys) ::: List Ty) :-: (List (Lam (Sg (E (V 0)) (E (V 1)))))) ::: List Ty) :$ revTy :$ Nil

myEnum = Enum (Cons (A "a") (Cons (A "c") (Cons (A "c") Nil)))
myEnumNeut = Enum (Cons (A "a") (Cons (E (P [("q", 0)] (Hide Atom))) (Cons (A "c") Nil)))

listABC = (Cons (A "a") (Cons (A "b") (Cons (A "c") Nil)))

predABC = P [("P", 0)] (Hide (Pi (Enum listABC) Ty))

enumAtoms =
  ListElim (List (Enum (E (V 0)))) Nil (Cons Z (V 0 :-: List (Lam $ S (E (V 0)))))

allPabc = (listABC ::: List Atom) :$ enumAtoms :$ AllP (E (predABC :$ E (V 0))) One

allmapfusion = ((xs :-: List (Lam $  S (E (V 0)))) ::: List (Enum listABC)) :$ AllP (E (predABC :$ E (V 0))) One
  where
    xs = P [("xs", 0)] (Hide (List (Enum (Cons (A "b") (Cons (A "c") Nil)))))

enumToNat = (Lam (E (V 0 :$ EnumElim Nat (1 :& 2 :& 3 :& Void)))) ::: Pi (Enum listABC) Nat

myEnumToNat = enumToNat :$ A "a"

myG = FAb (Enum listABC)

myGelt = Inv (Eta (A "b")) :.: E (P [("x", 0)] (Hide myG)) :.: Eta (A "a") :.: Inv (E (P [("x", 0)] (Hide myG)))

stuttering = (Lam $ (V 0 :-: Hom (Lam $ (Single (E (V 0)) :++: Single (E (V 0)))))) ::: Pi (List Atom) (List (Atom))

idObfuscated = (Lam $ (V 0 :-: Hom (Lam $ Single ((E (V 0))) :++: Nil))) ::: Pi (List Atom) (List Atom)

youarehereTy = Pi Ty (Pi (List (E (V 0))) (AllT (E (V 1)) (Thinning (E (V 2)) (Single (E (V 0))) (E (V 1))) (E (V 0))))

youarehere = Lam {-X-} . Lam {-xs-} . E $ V {-xs-} 0 :$
  ListElim ({-xs'.-} AllT (E (V {-X-} 2)) ({-x.-}Thinning (E (V {-X-} 3)) (Single (E (V {-x-} 0))) (E (V {-xs'-} 1))) (E (V {-xs'-} 0)))
           Nil
           ({-x, xs', ih.-} Cons (Cons Th1 Th0) (V {-ih-} 0 :-: AllT (Lam {-y-} (E (V {-y-} 0))) (Lam {-y-} . Lam {-th-} $ Cons Th0 (E (V {-th-} 0))) Th1))

youarehereApplied = (youarehere ::: youarehereTy) :$ Atom :$ listABC

{-
TODO
1. More infrastructure towards canonical representatives
2. Additional interesting types (abelian group)
3. Typechecking
-}

