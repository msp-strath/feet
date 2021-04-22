module Main where

import System.Environment

import Data.List

import Feet.Syntax
import Feet.Semantics
import Feet.Parser
import Feet.Frontend

main = do
  args <- getArgs
  case args of
    [file] -> do
      prg <- readFile file
      case nub [t | (t, "") <- dbp pTask [] prg] of -- why is nub needed?
        [t] -> printTask t
        r -> putStrLn $ "FEET syntax error" ++ show r
    _ -> do
      progName <- getProgName
      putStrLn $ "Usage: " ++ progName ++ " [FILE]"
