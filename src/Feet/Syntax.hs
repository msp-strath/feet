{-# LANGUAGE PatternSynonyms #-}
module Feet.Syntax where

infixl :$:

newtype Abs x = Abs {unAbs :: x} deriving (Ord, Eq)

instance Show x => Show (Abs x) where show (Abs x) = '\\' : show x

data Syn = Chk ::: Chk -- type annotation
         | Var Int     -- deBruijn index
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
