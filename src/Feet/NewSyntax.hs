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
#-}
module NewSyntax where

import Data.Void
import Data.Bits

import Control.Applicative
import Control.Monad
-- import Control.Monad.Fail

import Utils.Bwd

import Debug.Trace

data Chk
  m -- what's the meta
  = A String       -- atoms
  | Chk m :& Chk m -- pairs
  | B (Chk m)      -- binder
  | E (Syn m)      -- embedding Syn
  | M m            -- metas
  deriving (Show, Functor)

data Syn
  m -- what's the meta
  = V Int           -- variables
  | P Name Type     -- parameters
  | Syn m :$ Chk m  -- elimination
  | Chk m ::: Chk m -- radicals
  deriving (Show, Functor)

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

instantiate :: Matching -> ChkEx -> ChkTm
instantiate m (M (x :/ si)) =  substitute (fmap (instantiateSyn m) si) 0 t
  where Just t = lookup x m
instantiate m (A a) = A a
instantiate m (t :& t') = (instantiate m t) :& (instantiate m t')
instantiate m (B t) = B (instantiate m t)
instantiate m (E s) = upsE (instantiateSyn m s)

instantiateSyn :: Matching -> SynEx -> SynTm
instantiateSyn m (V i) = V i
instantiateSyn m (P n ty) = P n ty
instantiateSyn m (s :$ t) = instantiateSyn m s :$ instantiate m t
instantiateSyn m (t ::: t') = instantiate m t ::: instantiate m t'

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

instance Substitute Meta where
  substitute si i (m :/ ez) = m :/ fmap (substitute si i) ez

instance Substitute m => Substitute (Syn m) where
  substitute si i (V j) = vacuous (bwdProj si' j) where
    si' = fromi i <> fmap (<^> th) si <> toi 0
    fromi k = fromi (k+1) :< V k
    toi k = if k >= i then B0 else  toi (k+1) :< V k
    th = Th (shiftL (-1) j)
  substitute si i (P n ty) = P n ty
  substitute si i (s :$ t) = substitute si i s :$ substitute si i t
  substitute si i (t ::: t') = substitute si i t ::: substitute si i t'

data ElimRule = ElimRule
  { targetType :: ChkPa
  , eliminator :: ChkPa
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

-- instance MonadFail TCM where


weakAnalyser :: (Type, ChkTm) -> TCM (Maybe WeakAnalysis)
weakAnalyser x = TCM $ \ s ns -> runTCM (weakAnalyserSetup s x) s ns

eliminate :: Type -> ChkTm -> TCM (Maybe (Matching, ElimRule))
eliminate ty s = TCM $ \ setup ns -> case [ (mTy ++ melim, rule) | rule <- elimRules setup, mTy <- trail (match (targetType rule) ty), melim <- trail (match (eliminator rule) s) ] of
  [(m, rule)] -> Right $ Just (m, rule)
  []          -> Right $ Nothing
  x           -> Left $ "eliminator: more than one rule applies! " ++ show x


-- Assuming type is already head normalised
weakChkEval :: (Type, ChkTm) -> TCM ChkTm
-- weakChkEval x | trace ("chk: " ++ show x) False = undefined
weakChkEval x = do
  r <- weakAnalyser x
  case r of
    Just (WeakAnalysis xs recon) -> recon <$> traverse weakChkEval xs
    Nothing -> case x of
      (ty, E e) -> upsE <$> (fst <$> weakEvalSyn e)
      x         -> return (snd x)

-- Ensures that the type is head normalised
weakEvalSyn :: SynTm -> TCM (SynTm, Type)
-- weakEvalSyn x | trace ("syn: " ++ show x) False = undefined
weakEvalSyn (V i) = fail "weakEvalSyn applied to non-closed term"
weakEvalSyn (P n ty) = return (P n ty, ty)
weakEvalSyn (t ::: ty) = do
  weakChkEval (Ty, ty) >>= \case
    ty -> weakChkEval (ty, t) >>= \case
        t -> return (t ::: ty, ty)
weakEvalSyn (e :$ s) = do
  (e, ty) <- weakEvalSyn e
  eliminate ty s >>= \case
    Just (m, rule) -> do
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
-- Type
pattern Ty = A "Ty"

-- Pi
pattern Pi s t = A "Pi" :& s :& B t
pattern Lam t = A "lam" :& B t

-- Sigma
pattern Sg s t = A "Sg" :& s :& B t
-- Pair s t = s :& t
pattern Fst = A "fst"
pattern Snd = A "snd"


piElim = ElimRule
  { targetType = Pi (pm "S") (pm "T")
  , eliminator = pm "s"
  , reductType = M ("T" :/ si)
  , betaRules = [(Lam (pm "t"), M ("t" :/ si))]
  }
  where si = B0 :< (em "s" ::: em "S")

fstElim = ElimRule
  { targetType = Sg (pm "S") (pm "T")
  , eliminator = Fst
  , reductType = M ("S" :/ B0)
  , betaRules = [(pm "s" :& pm "t", M ("s" :/ B0))]
  }

sndElim = ElimRule
  { targetType = Sg (pm "S") (pm "T")
  , eliminator = Snd
  , reductType = M ("T" :/ si)
  , betaRules = [(pm "s" :& pm "t", M ("t" :/ B0))]
  }
  where si = B0 :< (V 0 :$ Fst)



newtype I x = I { unI :: x }
  deriving (Functor, Foldable, Traversable)

newtype K a x = K { unK :: a }
  deriving (Functor, Foldable, Traversable)

data (f :*: g) x = (:*:) { outL :: f x , outR :: g x }
  deriving (Functor, Foldable, Traversable)

data (f :+: g) x = InL (f x) | InR (g x)
  deriving (Functor, Foldable, Traversable)


ourSetup = Setup
  { elimRules = [piElim, fstElim, sndElim]
  , weakAnalyserSetup = \ x -> case x of
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

-- testing

idTy = Pi Ty (Pi (E (V 0)) (E (V 1)))
idTm = Lam (Lam (E (V 0)))

fam :: ChkTm -> ChkTm
fam x = Sg Ty (Pi (E (V 0)) (x <^> o' (o' mempty)))

famTytm = idTy :& Lam idTy


