{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
module Nbe where

import Prelude hiding (fail)

import Data.Maybe
import Data.List
import Control.Arrow ((***))
import Control.Monad.Fail

import Debug.Trace

data Bwd x = B0 | Bwd x :< x
  deriving (Show, Eq, Functor, Foldable, Traversable)

infixl 4 :<

instance Monoid (Bwd x) where
  mempty = B0
  mappend xz B0        = xz
  mappend xz (yz :< y) = mappend xz yz :< y

instance Semigroup (Bwd x) where (<>) = mappend

infixl 4 <><

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

(<>>) ::  Bwd x -> [x] -> [x]
B0 <>> xs = xs
(xz :< x) <>> xs = xz <>> (x:xs)

mapzss :: (a -> b) -> Bwd a -> [b] -> [b]
mapzss f B0 xs = xs
mapzss f (xz :< x) xs = mapzss f xz (f x : xs)

mapzs :: (a -> b) -> Bwd a -> [b]
mapzs f xz = mapzss f xz []

infixl :$:

newtype Abs x = Abs {unAbs :: x} deriving (Ord, Eq)

instance Show x => Show (Abs x) where show (Abs x) = '\\' : show x

data Syn = Chk ::: Chk -- type annotation
         | Var Int     -- deBruijn index
         -- application
         | Syn :$: Chk
         -- projections
         | Fst Syn
         | Snd Syn
         -- naturals
         | ListRec (Abs Chk) Chk (Abs (Abs (Abs Chk))) Syn
         -- group
  deriving (Show, Eq, Ord)

data Chk = Inf Syn  -- embedding inferable
         -- types
         | Ty
         | Pi Chk (Abs Chk)
         | Sg Chk (Abs Chk)
         | List Chk
         | Unit
         | G  -- group
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
         -- group elements
         | GUnit
         | Chk :*: Chk
         | GInv Chk
  deriving (Show, Eq, Ord)

(+++) :: Chk -> Chk -> Chk
Nil +++ ys = ys
xs  +++ Nil = xs
(xs :++: ys) +++ zs = xs +++ (ys +++ zs)
xs  +++ ys = xs :++: ys

type Env = [Value]

data Closure = Cl (Abs Chk) Env
             | ClId
             | ClComp Closure Closure -- neither ClId, left arg not ClComp
  deriving Show

clComp :: Closure -> Closure -> Closure
clComp ClId cl' = cl'
clComp cl ClId = cl
-- clComp (ClComp cl cl') cl'' = clComp cl (clComp cl' cl'')
clComp cl cl' = ClComp cl cl'


data Closure3 = Cl3 (Abs (Abs (Abs Chk))) Env -- closure with three free variables
              | ClComp3 Closure3 Closure Closure Closure
  deriving Show

type Type = Value

data Value = VNeutral Type Neutral -- type is not list
           -- types
           | VTy
           | VPi Type Closure
           | VSg Type Closure
           | VList Type
           | VUnit
           | VG
           -- functions
           | VLam Closure
           -- sigma
           | VPair Value Value
           -- lists
           | VNil
           | VCons Value Value
           | VAppend (Closure, Neutral) Value -- closure: function being mapped over elements
           -- unit element
           | VAst
           -- group elements
           | VGrp [(Bool, GGenerator)] -- Boolean: is it inverted?
  deriving Show

type GGenerator = Neutral

data Neutral = NVar Int Type -- deBruijn level
             | NApp Neutral Value
             | NFst Neutral
             | NSnd Neutral
             | NLRec Closure Value Closure3 Neutral
  deriving Show

evalSyn :: Syn -> Env -> Value
evalSyn (s ::: _) rho = evalChk s rho
evalSyn (Var x) rho = rho !! x
evalSyn (f :$: s) rho = vapp (evalSyn f rho) (evalChk s rho)
evalSyn (Fst e) rho = vfst (evalSyn e rho)
evalSyn (Snd e) rho = vsnd (evalSyn e rho)
evalSyn (ListRec t bas step n) rho = vlistrec (Cl t rho) (evalChk bas rho) (Cl3 step rho) (evalSyn n rho)

evalChk :: Chk -> Env -> Value
evalChk (Inf e) rho = evalSyn e rho
evalChk Ty rho = VTy
evalChk (Pi a b) rho = VPi (evalChk a rho) (Cl b rho)
evalChk (Sg a b) rho = VSg (evalChk a rho) (Cl b rho)
evalChk (List a) rho = VList (evalChk a rho)
evalChk Unit rho = VUnit
evalChk G rho = VG
evalChk (Lam s) rho = VLam (Cl s rho)
evalChk (Pair s t) rho = VPair (evalChk s rho) (evalChk t rho)
evalChk Nil rho = VNil
evalChk (Single s) rho = VCons (evalChk s rho) VNil
evalChk (s :++: t) rho = vappend (evalChk s rho) (evalChk t rho)
evalChk (Map body e) rho = vmap (Cl body rho) (evalSyn e rho)
evalChk Ast rho = VAst
-- Group
evalChk GUnit rho = vgunit
evalChk (GInv s) rho = vginv (evalChk s rho)
evalChk (s :*: t) rho = vgmult (evalChk s rho) (evalChk t rho)

clapp :: Closure -> Value -> Value
clapp (Cl (Abs s) rho) v = evalChk s (v:rho)
clapp ClId             v = v
clapp (ClComp cl cl')  v = clapp cl (clapp cl' v)

clapp3 :: Closure3 -> Value -> Value -> Value -> Value
clapp3 (Cl3 (Abs (Abs (Abs s))) rho) a b c = evalChk s (c:b:a:rho)
clapp3 (ClComp3 f a b c) x y z = clapp3 f (clapp a x) (clapp b y) (clapp c z)

vneutral :: Type -> Neutral -> Value
vneutral VUnit     n = VAst
vneutral (VList a) n = VAppend (ClId, n) VNil
vneutral VG        n = VGrp [(False, n)]
vneutral ty        n = VNeutral ty n

vapp :: Value -> Value -> Value
vapp (VLam cl)              t = clapp cl t
vapp (VNeutral (VPi a b) n) t = vneutral (clapp b t) (NApp n a)
vapp s t = error $ "vapp of " ++ show s

vfst :: Value -> Value
vfst (VPair a b)            = a
vfst (VNeutral (VSg a b) n) = vneutral a (NFst n)
vfst x           = error $ "vfst applied to non-pair " ++ show x

vsnd :: Value -> Value
vsnd (VPair a b)              = b
vsnd p@(VNeutral (VSg a b) n) = vneutral (clapp b (vfst p)) (NSnd n)
vsnd x           = error $ "vsnd applied to non-pair " ++ show x

vlistrec :: Closure -> Value -> Closure3 -> Value -> Value
-- vlistrec t base step v | trace ("\n===listrec===\nt: " ++ show t ++ "\nbase: " ++ show base ++ "\nstep: " ++ show step ++ "\nv: " ++ show v ++ "\n=============\n") False = undefined
vlistrec t base step VNil = base
vlistrec t base step (VCons x xs) = clapp3 step x xs (vlistrec t base step xs)
vlistrec t base step v@(VAppend (cl, xs) ys) =
  vneutral (clapp t v) (NLRec (clComp t appCl) (vlistrec t base step ys)
                              (ClComp3 step cl appCl ClId) xs)
  where appCl = Cl (Abs (Inf (Var 0) :++: Inf (Var 1))) [ys]
-- vlistrec t base step n@(VNeutral ty e) = vneutral (clapp t n) (NLRec t base step e)

vappend :: Value -> Value -> Value
vappend VNil              ys = ys
vappend (VCons x xs)      ys = VCons x (vappend xs ys)
vappend (VAppend clxs zs) ys = VAppend clxs (vappend zs ys)
vappend xs ys = error $ "vappend applied to " ++ show xs

vmap :: Closure -> Value -> Value
vmap cl VNil                 = VNil
vmap cl (VCons x xs)         = VCons (clapp cl x) (vmap cl xs)
vmap cl (VAppend (ncl, n) v) = VAppend (clComp cl ncl, n) (vmap cl v)

vgroup :: Value -> Value
vgroup v@(VGrp as)     = v
vgroup (VNeutral VG n) = VGrp [(False,n)]
vgroup z = error $ "vgroup: " ++ show z ++ " ?!?"

unvgrp :: Value -> [(Bool, GGenerator)]
unvgrp v = case vgroup v of
  (VGrp as) -> as

vgunit :: Value
vgunit = VGrp []

vginv :: Value -> Value
vginv v = VGrp $ reverse $ map (not *** id) (unvgrp v)

vgmult :: Value -> Value -> Value
vgmult v v' = VGrp $ unvgrp v ++ unvgrp v'

vvar :: Type -> Int -> Value
vvar a i = vneutral a $ NVar i a

equalType :: Int -> Type -> Type -> Maybe (Value -> Value -> Bool)
equalType i a b = case quote VTy a i == quote VTy b i of
  False -> Nothing
  True -> Just (\ x y -> quote a x i == quote b y i)

qunder :: Type -> Closure -> (Value -> Value -> Int -> x) -> Int -> (Abs x)
qunder ty body op i = Abs $ op x (clapp body x) (i + 1)
  where x = vvar ty i

qunder3 :: Closure3 -> Type -> (Value -> (Type, Value -> (Type, Value -> Value -> Int -> x))) ->
           Int -> Abs (Abs (Abs x))
qunder3 body3 ty0 op0 i = Abs . Abs . Abs $ op2 z (clapp3 body3 x y z) (i + 3) where
  x = vvar ty0 i
  (ty1, op1) = op0 x
  y = vvar ty1 (i + 1)
  (ty2, op2) = op1 y
  z = vvar ty2 (i + 2)

quote :: Type -> Value -> Int -> Chk
-- quote i ty v | trace ("quote ty: " ++ show ty ++ " v: " ++ show v) False = undefined
quote (VPi a b) f = (Lam <$>) $ qunder a b $ \ x b -> quote b (vapp f x)
quote (VSg a b) p = let p1 = vfst p; p2 = vsnd p in
  Pair <$> quote a p1 <*> quote (clapp b p1) p2
quote (VList a) v = quoteList a v
quote VUnit v = pure Ast
quote VTy v = case v of
  VTy -> pure Ty
  (VPi a b) -> Pi <$> quote VTy a <*> qunder a b (\ x b -> quote VTy b)
  (VSg a b) -> Sg <$> quote VTy a <*> qunder a b (\ x b -> quote VTy b)
  VList a -> List <$> quote VTy a
  VUnit -> pure Unit
  VG -> pure  G
  VNeutral _ e -> Inf <$> quoteNeutral e
  z -> error $ "unexpected " ++ show z
quote (VNeutral _ _) (VNeutral _ e) = Inf <$> quoteNeutral e
quote VG v = quoteGroup <$> traverse (\ (b, n) -> (b,) <$> quoteNeutral n) (unvgrp v)

quoteNeutralTy :: Neutral -> Int -> (Syn, Type)
quoteNeutralTy (NVar x ty) = \ i -> (Var (i - (x + 1)), ty) -- convert from levels to indices
quoteNeutralTy (NApp f a) = do
  (f', VPi s t) <- quoteNeutralTy f
  (, clapp t a) <$> ((f' :$:) <$> quote s a)
quoteNeutralTy (NFst e) = do
  (e', VSg s t) <- quoteNeutralTy e
  return (Fst e', s)
quoteNeutralTy (NSnd e) = do
  (e', VSg s t) <- quoteNeutralTy e
  return (Snd e', clapp t (vfst (vneutral (VSg s t) e)))
quoteNeutralTy (NLRec t base step e) = do
  (e', VList a) <- quoteNeutralTy e
  ((, clapp t (vneutral (VList a) e)) <$>) $ ListRec
    <$> qunder (VList a) t (\ x t -> quote VTy t)
    <*> quote (clapp t VNil) base
    <*> (qunder3 step a $ \ x -> (VList a,) $ \ xs -> (clapp t xs,) $ \ _ step ->
         quote (clapp t (VCons x xs)) step)
    <*> pure e'

quoteNeutral :: Neutral -> Int -> Syn
quoteNeutral n = fst <$> quoteNeutralTy n

quoteList :: {- Element -} Type -> Value -> Int -> Chk
quoteList ty VNil = pure Nil
quoteList ty (VCons x xs) = (+++) <$> (Single <$> quote ty x) <*> quoteList ty xs
quoteList b (VAppend (f, ns) ys) = do
  (xs, VList a) <- quoteNeutralTy ns
  a' <- quote VTy a
  b' <- quote VTy b
  rest <- quoteList b ys
  Abs (x', t') <- qunder a f $ \ x t -> (,) <$> quote a x <*> quote b t
  if a' == b' && x' == t'
    then return $ Inf xs +++ rest
    else return $ Map (Abs t') xs +++ rest
-- no case for VNeutral, because of our invariant
quoteList ty x = error $ "quoteList applied to " ++ show x

quoteGroup :: [(Bool, Syn)] -> Chk
quoteGroup as = foldr mult GUnit $ cancel B0 $ sortOn snd as -- sort to make it Abelian
    where
      -- slide elements from right to left, and cancel if we look at two inverses
      cancel :: Bwd (Bool, Syn) -> [(Bool,Syn)] -> [Chk]
      cancel gz [] = mapzs invert gz
        where
          invert (b, x) = (if b then GInv else id) (Inf x)
      cancel B0 (g:gs) = cancel (B0 :< g) gs
      cancel (gz :< g) (g':gs) = if inverse g g' then cancel gz gs else cancel (gz :< g :< g') gs
        where inverse (ig, eg) (ih, eh) = ig == not ih && eg == eh

      -- smart constructor
      mult x GUnit = x
      mult GUnit y = y
      mult x y     = x :*: y

norm :: Env -> Type -> Chk -> Chk
norm rho ty t = quote ty (evalChk t rho) (length rho)

normSyntax :: Chk -> Chk -> Chk
normSyntax t ty = norm [] (evalChk ty []) t

type Context = [(Value,Type)]

newtype TC m x = TC {tc :: Int -> Context -> m x}

instance Monad m => Monad (TC m) where
  return x = TC $ \ _ _ -> return x
  TC a >>= k = TC $ \ i g -> do
    x <- a i g
    tc (k x) i g

instance Applicative m => Applicative (TC m) where
  pure x = TC $ \ _ _ -> pure x
  TC f <*> TC a = TC $ \ i g -> f i g <*> a i g

instance Functor m => Functor (TC m) where
  fmap f (TC k) = TC $ \ i g -> fmap f (k i g)

instance MonadFail m => MonadFail (TC m) where
  fail s = TC $ \ _ _ -> fail s

under :: Type -> Abs x -> (Value -> x -> TC m r) -> TC m r
under ty (Abs body) op = TC $ \ i g ->
  let v = vvar ty i
  in  tc (op v body) (i + 1) ((v, ty): g)

type Get = TC (Either String)

instance MonadFail (Either String) where
  fail = Left

typeof :: Int -> Get Type
typeof i = TC $ \ _ g -> pure $ snd $ g !! i

withEnv :: (Env -> t) -> Get t
withEnv f = TC $ \ _ g -> return (f (ctxtToEnv g))

closeAbs :: Abs Chk -> Get Closure
closeAbs s = withEnv $ Cl s

ctxtToEnv :: Context -> Env
ctxtToEnv = map fst

synth :: Syn -> Get Type
synth (s ::: t) = do
  isType t
  t' <- withEnv $ evalChk t
  check t' s
  pure t'
synth (Var x) = typeof x
synth (f :$: s) = do
  t <- synth f
  case t of
    VPi a b -> do
      check a s
      clapp b <$> (withEnv $ evalChk s)
    y -> fail $ "expected Pi, got " ++ show y
synth (Fst s) = do
  t <- synth s
  case t of
    VSg a b -> pure a
    y -> fail $ "expected Sg, got " ++ show y
synth (Snd s) = do
  t <- synth s
  case t of
    VSg a b -> clapp b <$> (withEnv $ evalSyn (Fst s))
    y -> fail $ "expected Sg, got " ++ show y
synth (ListRec p base step e) = do
  te <- synth e
  e <- withEnv (evalSyn e)
  case te of
    VList a -> do
      under te p $ \ x p -> isType p
      mo <- clapp <$> closeAbs p
      check (mo VNil) base
      under a step $ \ x step ->
        under te step $ \ xs step ->
          under (mo xs) step $ \ xsh step ->
            check (mo (VCons x xs)) step
      pure $ mo e
    z    -> fail $ "expected List, got " ++ show z

eqTy :: Type -> Type -> Get ()
eqTy ty ty' = TC $ \ i _ -> case equalType i ty ty' of
    Just _ -> pure ()
    Nothing -> fail $ "expected " ++ show ty ++ "\ngot      " ++ show ty'

check :: Type -> Chk -> Get ()
check ty (Inf e) = do
  ty' <- synth e
  eqTy ty' ty
check ty Ty = case ty of
  VTy -> pure ()
  z   -> fail $ "expected Ty, got " ++ show z
check ty (Pi a b) = case ty of
  VTy -> do
    isType a
    a <- withEnv $ evalChk a
    under a b $ \ x b -> isType b
  z   -> fail $ "expected Ty, got " ++ show z
check ty (Sg a b) = case ty of
  VTy -> do
    isType a
    a <- withEnv $ evalChk a
    under a b $ \ x b -> isType b
  z   -> fail $ "expected Ty, got " ++ show z
check ty Unit = case ty of
  VTy -> pure ()
  z   -> fail $ "expected Ty, got " ++ show z
check ty G = case ty of
  VTy -> pure ()
  z   -> fail $ "expected Ty, got " ++ show z
check ty (List a) = case ty of
  VTy -> pure ()
  z   -> fail $ "expected Ty, got " ++ show z
check ty (Lam s) = case ty of
  VPi a b -> under a s $ \ x s -> check (clapp b x) s
  z   -> fail $ "expected Pi, got " ++ show z
check ty (Pair s t) = case ty of
  VSg a b -> do
    check a s
    s <- withEnv $ evalChk s
    check (clapp b s) t
  z   -> fail $ "expected Sg, got " ++ show z
check ty Ast = case ty of
  VUnit -> pure ()
  z   -> fail $ "expected Unit, got " ++ show z
check ty Nil = case ty of
  VList a -> pure ()
  z   -> fail $ "expected List, got " ++ show z
check ty (Single s) = case ty of
  VList a -> check a s
  z   -> fail $ "expected List, got " ++ show z
check ty (s :++: t) = case ty of
  VList a -> do
    check (VList a) s
    check (VList a) t
  z   -> fail $ "expected List, got " ++ show z
check ty (Map s e) = case ty of
  VList b -> synth e >>= \ z -> case z of
    VList a -> under a s $ \ x s -> check b s
    z -> fail $ "expected List, got " ++ show z
  z   -> fail $ "expected List, got " ++ show z
check ty GUnit = case ty of
  VG -> pure ()
  z   -> fail $ "expected G, got " ++ show z
check ty (GInv s) = case ty of
  VG -> check VG s
  z   -> fail $ "expected G, got " ++ show z
check ty (s :*: t) = case ty of
  VG -> do
    check VG s
    check VG t
  z   -> fail $ "expected G, got " ++ show z
{-
check i gamma ty t =
  error $ "check: untreated type " ++ show ty ++ " and term " ++ show t
-}

isType :: Chk -> Get ()
isType = check VTy


topl :: TC m x -> m x
topl op = tc op 0 []


-- tests



f = (Lam . Abs $ Lam . Abs $ body) ::: (Pi G . Abs $ Pi G . Abs $ G) where
    body = x :*: x :*: x :*: y :*: GInv (y :*: y :*: x)
    x = Inf $ Var 0
    y = Inf $ Var 1

nat = List Unit
zero = Nil
suc = Lam . Abs $ Single Ast :++: Inf (Var 0)

sucTy = Pi nat . Abs $ nat

append = (Lam . Abs $ Lam . Abs $ Lam . Abs $ Inf $
  ListRec (Abs $ List (Inf $ Var 3))
    (Inf $ Var 0)
    (Abs . Abs . Abs $ Single (Inf $ Var 2) :++: Inf (Var 0))
    (Var 1)
  ) :::
  (Pi Ty . Abs $
   Pi (List (Inf $ Var 0)) . Abs $
   Pi (List (Inf $ Var 1)) . Abs $
   List (Inf $ Var 2))

two = append :$: Unit :$: Inf ((suc ::: sucTy) :$: zero) :$: Inf ((suc ::: sucTy) :$: zero)

two' = Lam . Abs $ Inf $
  append
  :$: Unit
  :$: Inf ((suc ::: sucTy) :$: Inf (Var 0))
  :$: Inf ((suc ::: sucTy) :$: zero)

two'' = Map (Abs $ Inf $ Var 0) two

mapswap = Lam . Abs $ Map (Abs $ Pair (Inf $ Snd $ Var 0) (Inf $ Fst $ Var 0)) (Var 0)

mapswapTy = Pi (List (Sg Unit . Abs $ Unit)) . Abs $ (List (Sg Unit . Abs $ Unit))

mapswapTy' = Pi (List (Sg nat . Abs $ nat)) . Abs $ (List (Sg nat . Abs $ nat))

mapswapmapswap = Lam . Abs $ Inf $
  (mapswap ::: mapswapTy') :$: (Inf $ (mapswap ::: mapswapTy') :$: (Inf $ Var 0))

toTuples = Lam . Abs $ Inf $
  ListRec (Abs Ty) Unit (Abs . Abs . Abs $ Sg (Inf $ Var 2) . Abs $ (Inf $ Var 1)) (Var 0)

toTuplesTy = Pi (List Ty) . Abs $ Ty

allList' = Lam . Abs{-A-} $ Lam . Abs{-P-} $ Lam . Abs{-xs-} $ Inf $
  (toTuples ::: toTuplesTy) :$: (Map (Abs . Inf $ Var 2 :$: (Inf $ Var 0)) (Var 0))

allList = Lam . Abs{-A-} $ Lam . Abs{-P-} $ Lam . Abs{-xs-} $ Inf $
  ListRec
    (Abs Ty)
    Unit
    (Abs . Abs . Abs $ Sg (Inf $ (Var 4) :$: Inf (Var 2)) . Abs $ (Inf $ Var 1))
    (Var 0)

allListTy =
  Pi Ty . Abs $
  Pi (Pi (Inf $ Var 0) . Abs $ Ty) . Abs $
  Pi (List (Inf $ Var 1)) . Abs $
  Ty

r = Lam . Abs $ Lam . Abs $ Inf $
  (allList ::: allListTy) :$: Unit :$: (Lam . Abs $ Ty) :$: (Inf (Var 1) :++: Inf (Var 0))

r' = Lam . Abs $ Lam . Abs $ Inf $
  (allList' ::: allListTy) :$: Unit :$: (Lam . Abs $ Ty) :$: (Inf (Var 1) :++: Inf (Var 0))

rTy = Pi nat (Abs (Pi nat (Abs Ty)))

{-

plus = Lam (Lam $ Inf $ NatRec Nat (Inf $ Var 0) (Succ $ Inf $ Var 0) (Var 1))
       :::
       Pi Nat (Pi Nat Nat)

num 0 = Zero
num k = Succ (num $ k - 1)

v i = Inf $ Var i

a i = vvar VG i

g = Inf ((Lam (GUnit :*: GInv (Inf $ Var 0)) ::: Pi G G) :$: GInv (v 0)) :*: GInv (v 0)

test = norm [a 0] g VG

-}

instance MonadFail ((->) a) where
  fail = error
  
