{-# LANGUAGE  TypeSynonymInstances
            , FlexibleInstances
            , PatternSynonyms
            , TupleSections
#-}
module NewSyntax where

import Data.Void
import Data.Bits

import Control.Applicative
import Control.Monad

import Utils.Bwd

import Debug.Trace

data Chk
  m -- what's the meta
  = A String       -- atoms
  | Chk m :& Chk m -- pairs
  | B (Chk m)      -- binder
  | E (Syn m)      -- embedding Syn
  | M m            -- metas
  deriving Show

data Syn
  m -- what's the meta
  = V Int           -- variables
  | P Name Type     -- parameters
  | Syn m :$ Chk m  -- elimination
  | Chk m ::: Chk m -- radicals
  deriving Show

type Name = [(String, Int)] -- namespace and deBruijn level

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

type ChkEx = Chk (String, Substitution)
type SynEx = Syn (String, Substitution)

newtype Substitution = Substitution (Bwd SynEx)
  deriving Show

pm :: String -> ChkPa -- pattern metavariable
pm x = M (x, mempty)

em :: String -> ChkEx -- expression metavariable
em x = M (x, Substitution B0)

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

type Matching = [(String, ChkTm)]

match :: ChkPa -> ChkTm -> Maybe Matching
match (M (x,th)) t = ((:[]) . (x,)) <$> thicken th t
match (A a) (A a') = guard (a == a') >> return []
match (t :& t') (v :& v') = (++) <$> match t v <*> match t' v'
match (B t) (B t') = match t t'
match (E s) _ = Nothing
match _ _ = Nothing

instantiate :: Matching -> ChkEx -> ChkTm
instantiate m (M (x, Substitution si)) =  substitute (fmap (instantiateSyn m) si) 0 t
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

substitute :: Bwd SynTm -> Int -> ChkTm -> ChkTm
substitute si i (M m) = M m
substitute si i (A a) = A a
substitute si i (t :& t') = (substitute si i t :& substitute si i t')
substitute si i (B t) = B (substitute si (i+1) t)
substitute si i (E s) = upsE (substituteSyn si i s)

substituteSyn :: Bwd SynTm -> Int -> SynTm -> SynTm
substituteSyn si i (V j) = bwdProj si' j where
  si' = fromi i <> fmap (<^> th) si <> toi 0
  fromi k = fromi (k+1) :< V k
  toi k = if k >= i then B0 else  toi (k+1) :< V k
  th = Th (shiftL (-1) j)
substituteSyn si i (P n ty) = P n ty
substituteSyn si i (s :$ t) = substituteSyn si i s :$ substitute si i t
substituteSyn si i (t ::: t') = substitute si i t ::: substitute si i t'

data BetaRule = BetaRule
  { targetType :: ChkPa
  , target :: ChkPa
  , eliminator :: ChkPa
  , reduct :: ChkEx
  , reductType :: ChkEx
  }
  deriving Show

betaContract :: BetaRule -> SynTm -> Maybe SynTm
betaContract r ((t ::: ty) :$ s) = do
  mtTy <- match (targetType r) ty
  mt <- match (target r) t
  me <- match (eliminator r) s
  let m = mtTy ++ mt ++ me
  return (instantiate m (reduct r) ::: instantiate m (reductType r))
betaContract r _ = Nothing

pattern Pi s t = A "Pi" :& s :& B t
pattern Lam t = A "lam" :& B t

pattern Ty = A "Ty"

piBeta = BetaRule
  { targetType = Pi (pm "S") (pm "T")
  , target = Lam (pm "t")
  , eliminator = pm "s"
  , reduct = M ("t", si)
  , reductType = M ("T", si)
  }
  where si = Substitution $ B0 :< (em "s" ::: em "S")

idTy = Pi Ty (Pi (E (V 0)) (E (V 1)))
idTm = Lam (Lam (E (V 0)))
