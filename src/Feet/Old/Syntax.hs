{-# LANGUAGE PatternSynonyms, GADTs #-}
module Feet.Old.Syntax where

import Utils.Bwd

infixl :$:

newtype Abs x = Abs {unAbs :: x} deriving (Ord, Eq)

instance Show x => Show (Abs x) where show (Abs x) = '\\' : show x


-- used to hide a field for deriving purposes
newtype Hide x = Hide {peek :: x}

instance Show x => Show (Hide x) where
   show = show . peek

instance Eq (Hide x) where
  _ == _ = True

instance Ord (Hide x) where
  compare _ _ = EQ

data Syn = Chk ::: Chk -- type annotation
         | Inx Int     -- variable (deBruijn index)
         | Lev Int (Hide Type) -- variable (deBruijn level)
         -- application
         | Syn :$: Chk
         -- projections (see below)
         | Fst Syn
         | Snd Syn
         -- lists
         | ListRec (Abs Chk) Chk (Abs (Abs (Abs Chk))) Syn
         -- booleans
         -- TODO: BoolRec
  deriving (Show, Eq, Ord)

data Chk = Inf Syn  -- embedding inferable
         -- types
         | Ty
         | Pi Chk (Abs Chk)
         | Sg Chk (Abs Chk)
         | List Chk
         | Unit
         | G  -- group
         | Two
         | Thinning Chk {-Elt type-} Chk {-Src list-} Chk {-Tgt list -}
         -- functions
         | Lam (Abs Chk)
         -- sigma
         | Pair Chk Chk
         -- lists
         | Nil
         | Single Chk
         | Chk :++: Chk
         | Map (Abs Chk) Syn -- chk: body of function, syn: list
         -- unit element
         | Ast
         -- Booleans
         | Bit Bool
         -- group elements
         | GUnit
         | Chk :*: Chk
         | GInv Chk
         -- thinnings
         | ThinComp Chk Chk -- diagrammatic
  deriving (Show, Eq, Ord)

pattern Cons x xs = Single x :++: xs

pattern Zero = Bit False
pattern One = Bit True

consThin :: Bool -> Chk -> Chk
consThin b Ast                  = Bit b
consThin b t@(Bit b') | b == b' = t
consThin b t                    = Pair (Bit b) t

thinComp :: Chk -> Chk -> Chk
thinComp One  t    = t
thinComp t    One  = t
thinComp Zero t    = Zero
thinComp t    Zero = Zero
thinComp Ast  t    = t
thinComp s (ThinComp t u) = thinComp (thinComp s t) u
thinComp s t = ThinComp s t

(+++) :: Chk -> Chk -> Chk
Nil +++ ys = ys
xs  +++ Nil = xs
(xs :++: ys) +++ zs = xs +++ (ys +++ zs)
xs  +++ ys = xs :++: ys

-- Values -------------------------------------

data Value
  = VTy
  | VPi Type Closure
  | VLam Closure
  | VSg Type Closure
  | VPair Value Value
  | VList Type
  | VNil
  | VCons Value Value
--  | VAppend (Closure, Neutral) Value
  | VUnit
  | VAst
  | VTwo
  | VBit Bool
  | VG
  | VGrp [(Bool, GGenerator)]
  | VThinning Type Value Value
  | VThinComp Value Value
  | VNeutral Neutral
  deriving (Show)

pattern VZero = VBit False
pattern VOne = VBit True

data Closure = Clo { env :: Env, varType :: Type, bodyType :: Closure, body :: Abs Chk }
             | CloK { constantBody :: Value }
  deriving (Show)

type Type = Value

data Cell x = x :::: Type
  deriving (Show)

type Env = Bwd (Cell Value)

data Neutral = NVar Int Type -- deBruijn level
             | NApp Neutral Value
             | NFst Neutral
             | NSnd Neutral
  deriving (Show)

type GGenerator = Neutral
