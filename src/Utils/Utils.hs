{-# LANGUAGE  TypeOperators
            , DeriveFunctor
            , DeriveFoldable
            , DeriveTraversable
 #-}
module Utils.Utils where

miffy :: Monad m => m Bool -> m x -> m x -> m x
miffy mb mt mf = do
  b <- mb
  if b then mt else mf

mandy :: Monad m => m Bool -> m Bool -> m Bool
mandy ma mb = miffy ma {- then -} mb {- else -} (return False)

-- Functor Kit

newtype I x = I { unI :: x }
  deriving (Functor, Foldable, Traversable)

instance Applicative I where
  pure = I
  I f <*> I a = I (f a)

newtype K a x = K { unK :: a }
  deriving (Functor, Foldable, Traversable)

data (f :*: g) x = (:*:) { outL :: f x , outR :: g x }
  deriving (Functor, Foldable, Traversable)

data (f :+: g) x = InL (f x) | InR (g x)
  deriving (Functor, Foldable, Traversable)
