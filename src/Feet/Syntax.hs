{-# LANGUAGE  PatternSynonyms
            , DeriveFunctor
            , TypeFamilies
#-}
module Feet.Syntax where

import Data.Void
import Data.Bits

import Control.Applicative
import Control.Monad
import Control.Arrow

import Utils.Utils
import Utils.Bwd

data Chk
  m -- what's the meta
  = A String       -- atoms
  | Chk m :& Chk m -- pairs
  | B (Chk m)      -- binder
  | (:-:) (Syn m) (Chk m) -- embedding Syn, with adapter
  | M m            -- metas
  deriving (Show, Functor, Eq, Ord)

type Adapter = ChkTm

pattern E e = e :-: Idapter

-- Adapters are:

pattern Idapter = A "Idapter" -- identity
-- List f, where f is an arbitrary function
-- Hom f
-- Enum f
-- Thinning f th ph
-- AllT f g th

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

initNameSupply :: NameSupply
initNameSupply = (B0, 0)

infixr 2 :&
infixl 3 :$
infix  1 :::

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


-- concrete types and terms

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

infixr 4 :++:

-- Predicate lifting of List

pattern AllT _X _P xs = A "All" :& _X :& (B _P) :& xs
-- constructors overloaded Nil, Single, :++:

pattern Only = A "only"

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

-- introduced by a number (less than the length of as), or, also an Atom in the list (optionally paired with a number)

pattern Enumerate = A "enumerate"
pattern Pose = A "pose"

-- Free Abelian groups

pattern FAb _X = A "FAb" :& _X
pattern Eta x = A "Eta" :& x
pattern FOne = A "1"
pattern (:.:) x y = A "*" :& x :& y
pattern Inv x = A "Inv" :& x

