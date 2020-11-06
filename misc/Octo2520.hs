module Octo2520 where

data Chk
  s -- what's embedded in the place of synth terms
  b -- what's the baggage on a binder
  = A String
  | Chk s b :& Chk s b
  | B b (Chk s ())
  | E s
  deriving Show

data Syn
  b -- what's the baggage on a binder
  = V Int
  | Syn b :$ Chk (Syn b) b
  | Chk (Syn b) b ::: Chk (Syn b) b
  deriving Show

type ChkTm = Chk SynTm ()
type SynTm = Syn ()

type Value = Chk Neutral Env
type Neutral = Syn Env
newtype Env = Env [(Value, Value)]

type ChkPa = Chk (String, Thinning) ()





newtype Thinning = Th Integer