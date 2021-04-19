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
  | (:-:) (Syn m) (Chk m) -- embedding Syn
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
