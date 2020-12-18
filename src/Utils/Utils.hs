module Utils.Utils where

miffy :: Monad m => m Bool -> m x -> m x -> m x
miffy mb mt mf = do
  b <- mb
  if b then mt else mf

mandy :: Monad m => m Bool -> m Bool -> m Bool
mandy ma mb = miffy ma {- then -} mb {- else -} (return False)
