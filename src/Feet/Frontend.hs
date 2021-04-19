module Feet.Frontend where

import Data.List

import Feet.Syntax
import Feet.Semantics

data Tel = T0 | ChkTm :\: Tel
  deriving Show

data Task
  = Tel :|- Task
  | (String, SynTm) :&& Task
  | Done
  deriving Show


{-
runTask :: Task -> TCM [(String, ChkTm)]
runTask Done = return []
runTask ((x, e) :&& k) = do
  t <- synth e
  (v, ty) <- evalSyn e
  c <- getQuote t v
  ((x, c) :) <$> define (v, t) k runTask
runTask (ga :|- k) = go ga where
  go T0 = runTask k
  go (s :\: t) = do
    check VTy s
    s <- withEnv $ evalChk s
    under s t $ \ _ -> go

prettyResult :: [(String, ChkTm)] -> String
prettyResult = concat . intersperse "\n\n" . map (\ (name, body) -> name ++ " = " ++ show body)
-}
