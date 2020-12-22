module Feet.Old.Thinning where

import Feet.Old.Syntax

class Thin t where
  (<^>) :: t -> Integer -> t

instance Thin Int where
  i <^> th = case (th `mod` 2, th `div` 2) of
    (0, th) -> 1 + (i <^> th)
    (1, th) -> case i of
      0 -> 0
      _ -> 1 + ((i - 1) <^> th)
instance Thin x => Thin (Abs x) where
  Abs t <^> th = Abs (t <^> (2 * th + 1))

instance Thin Chk where
  Inf e <^> th = Inf (e <^> th)
  Pi s t <^> th = Pi (s <^> th) (t <^> th)
  Sg s t <^> th = Pi (s <^> th) (t <^> th)
  List t <^> th = List (t <^> th)
  Thinning a b c <^> th = Thinning (a <^> th) (b <^> th) (c <^> th)
  Lam t <^> th = Lam (t <^> th)
  Pair s t <^> th = Pair (s <^> th) (t <^> th)
  Single t <^> th = Single (t <^> th)
  (s :++: t) <^> th = (s <^> th) :++: (t <^> th)
  Map f t <^> th = Map (f <^> th) (t <^> th)
  (s :*: t) <^> th = (s <^> th) :*: (t <^> th)
  GInv t <^> th = GInv (t <^> th)
  t <^> th = t -- should only be used at arity 0

instance Thin Syn where
  (t ::: y) <^> th = (t <^> th) ::: (y <^> th)
  Var i <^> th = Var (i <^> th)
  (f :$: s) <^> th = (f <^> th) :$: (s <^> th)
  ListRec p n c e <^> th = ListRec (p <^> th) (n <^> th) (c <^> th) (e <^> th)
