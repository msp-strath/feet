module Main where

import System.Environment

import Feet.Syntax
import Feet.Semantics
import Feet.Parser
import Feet.Frontend


test :: String -> Either String [(String, Chk)]
test x = case [t | (t, "") <- dbp pTask [] x] of
  [t] -> topl $ runTask t
  _ -> Left "syntax error"

main = do
  args <- getArgs
  case args of
    [file] -> do
      prg <- readFile file
      case test prg of
        Left err -> putStrLn $ "FEET ERROR: " ++ err
        Right r -> putStrLn $ prettyResult r
    _ -> do
      progName <- getProgName
      putStrLn $ "Usage: " ++ progName ++ " [FILE]"
