{-# LANGUAGE FlexibleContexts, DeriveTraversable #-}

{-
This is the "in context"-style solver which Adam Gundry
cooked up for constraints in a free Abelian group.
-}

module Frag where

import Control.Monad
import Control.Arrow ((***))
import Control.Monad.State
import Control.Monad.Except

type Chk = StateT Integer Maybe

fresh :: Chk Integer
fresh = do
  x <- get
  put (x + 1)
  return x

data Thing
  = Var Integer
  | Gen String
  deriving (Show, Eq, Ord)

data Bwd x = B0 | Bwd x :< x
  deriving (Show, Eq, Functor, Foldable, Traversable)

infixl 4 :<

instance Monoid (Bwd x) where
  mempty = B0
  mappend xz B0        = xz
  mappend xz (yz :< y) = mappend xz yz :< y

instance Semigroup (Bwd x) where (<>) = mappend

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

infixl 4 <><

data Entry
  = All Integer
  | Exi Integer
  | Def Integer Frag
  deriving Show

type Cx = Bwd Entry

newtype Frag = Frag {frag :: [(Thing, Integer)]}
  deriving (Show, Eq)
  -- the Things are in order, the Integers are nonzero

var :: Integer -> Frag
var x = Frag [(Var x, 1)]

gen :: String -> Frag
gen g = Frag [(Gen g, 1)]

instance Monoid Frag where
  mempty = Frag []
  mappend (Frag xis) (Frag yjs) = Frag (go xis yjs) where
    go xis yjs = case xis of
      [] -> yjs
      xi@(x, i) : xis' -> case yjs of
        [] -> xis
        yj@(y, j) : yjs' -> case compare x y of
          LT -> xi : go xis' yjs
          GT -> yj : go xis yjs'
          EQ -> case i + j of
            0 -> go xis' yjs'
            k -> (x, k) : go xis' yjs'

instance Semigroup Frag where (<>) = mappend

inv :: Frag -> Frag
inv (Frag xis) = Frag [(x, negate i) | (x, i) <- xis]

pow :: Frag -> Integer -> Frag
pow _ 0 = mempty
pow (Frag xis) j = Frag [(x, i * j) | (x, i) <- xis]

factor :: Thing -> Frag -> (Integer, Frag)
factor y (Frag xis) = (j, Frag yjs) where
  (j, yjs) = go xis
  go [] = (0, [])
  go ((x, i) : xis) | x == y = (i, xis)
  go (xi : xis) = (id *** (xi :)) (go xis)

quo :: Integer -> Integer -> Maybe Integer
quo d x = (x `div` d) <$ guard (x `mod` d == 0)

root :: Integer -> Frag -> Maybe Frag
root n (Frag xis) = Frag <$> traverse go xis where
  go (x, i) = (,) x <$> quo n i

maxabspow :: Frag -> Integer
maxabspow (Frag xis) = case [abs i | (Var _, i) <- xis] of
  [] -> 0
  is -> maximum is

queer :: Integer -> Integer -> (Integer, Integer)
queer d y = (q, r) where
  q = signum d * signum y * (abs y `div` abs d)
  r = y - d * q

quorem :: Integer  --   n /= 0
       -> Frag     --   g
       -> ( Frag   --   q
          , Frag   --   r
          )        --   g = q^n*r
                   -- all powers in r below abs n
quorem n (Frag xis) = (Frag qjs, Frag rks) where
  (qjs, rks) = foldMap grok xis
  grok (x, i) = case queer n i of
    (q, r) ->
      ( if q == 0 then [] else [(x, q)]
      , if r == 0 then [] else [(x, r)]
      )

solve :: Cx         -- starting from here
      -> ([Entry], Frag)
      -- (de, g) where de are existentials used in g
      -- the problem is to make g 1
      -> Chk Cx   -- by minimal context extension

solve B0 (de, g) = B0 <$ guard (g == mempty)
solve (ga :< e) (de, g) = case e of
  Def x h -> case factor (Var x) g of
    (i, g) -> (:< e) <$> solve ga (de, g <> pow h i)
  All x -> case factor (Var x) g of
    (0, _) -> (:< e) <$> solve ga (de, g)
    _      -> throwError ()
  Exi x -> case factor (Var x) g of
    (0, _) -> (:< e) <$> solve ga (de, g)
    (i, g') -> -- x^i * g' = g, = 1 ?
      case root i g' of
        Just h -> pure (ga <>< de :< Def x (inv h))
        Nothing -> case maxabspow g' of
          0 -> throwError () -- no vars, no freedom
          j -> case abs i <= j of
            True -> do
              y <- fresh
              let (q, r) = quorem i g'
              ga <- solve (ga <>< de :< Exi y)
                      ([], pow (var y) i <> r)
              return (ga :< Def x (var y <> inv q))
            False -> solve ga (e : de, g)

start :: Cx -> Frag -> Maybe Cx
start ga g = evalStateT (solve ga ([], g)) fr where
  fr = execState (traverse bid ga) 0
  bid e = case e of
    All _ -> return ()
    Exi x   -> see x
    Def x _ -> see x
  see x = do
    i <- get
    if x >= i then put (x + 1) else return ()
