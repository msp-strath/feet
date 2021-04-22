{-# LANGUAGE LambdaCase #-}
module Feet.Frontend where

import Data.List

import Utils.Bwd

import Feet.Syntax
import Feet.Semantics
import Feet.Print

import Debug.Trace

data Tel = T0 | (String, ChkTm) :\: Tel
  deriving (Show, Eq)

data Task
  = Tel :|- Task
  | (String, SynTm) :&& Task
  | Done
  deriving (Show, Eq)

instance Substitute Task where
  substitute si i (ga :|- t) = case ga of
    T0 -> T0 :|- substitute si i t
    ((x,s) :\: ga) -> let (ga' :|- t') = substitute si (i+1) (ga :|- t) in ((x, substitute si i s) :\: ga') :|- t'
  substitute si i ((f,s) :&& t) = (f, substitute si i s) :&& substitute si (i+1) t
  substitute si i Done = Done

runTask :: Task -> TCM [(String, SynTm)]
runTask Done = return []
runTask ((x, e) :&& k) = do
  -- t <- synth e
  (e, ty) <- weakEvalSyn e
  ((x, e) :) <$> runTask (k // e)
runTask (ga :|- k) = case ga of
  T0 -> runTask k
  ((x,s) :\: t) -> do
    -- check (Ty, s)
    s <- weakChkEval (Ty, s)
    fresh (x,s) $ \ y -> runTask ((t :|- k) // y)


printTask :: Task -> IO ()
printTask t = putStrLn . either ("FEET error: "++) concat . run $ do
  o <- runTask t
  clauses <- mapM (\ (name, body) -> (\ x -> name ++ " = " ++ x) <$> prettyNormSyn body) o
  return $ intersperse "\n\n" $ clauses
