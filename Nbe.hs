{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Nbe where

import Data.Maybe
import Data.List
import Control.Arrow ((***))

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

data Syn = Chk ::: Chk -- type annotation
         | Var Int     -- deBruijn index
         -- application
         | Syn :$: Chk
         -- projections
         | Fst Syn
         | Snd Syn
         -- naturals
         | NatRec Chk Chk Chk Syn
         -- group
  deriving (Show, Eq, Ord)

data Chk = Inf Syn  -- embedding inferable
         -- types
         | Ty
         | Pi Chk Chk
         | Sg Chk Chk
         | Nat
         | Unit
         | G  -- group
         -- functions
         | Lam Chk
         -- sigma
         | Pair Chk Chk
         -- naturals
         | Zero
         | Succ Chk
         -- unit element
         | Ast
         -- group elements
         | GUnit
         | Chk :*: Chk
         | GInv Chk
  deriving (Show, Eq, Ord)

type Env = [Value]

data Closure = Cl Chk Env
  deriving Show

data Closure2 = Cl2 Chk Env -- closure with two free variables
  deriving Show

type Type = Value

data Value = VNeutral Type Neutral
           -- types
           | VTy
           | VPi Type Closure
           | VSg Type Closure
           | VNat
           | VUnit
           | VG
           -- functions
           | VLam Closure
           -- sigma
           | VPair Value Value
           -- nats
           | VZero
           | VSucc Value
           -- unit element
           | VAst
           -- group elements
           | VGrp [(Bool, GGenerator)] -- Boolean: is it inverted?
  deriving Show

type GGenerator = Neutral

data Neutral = NVar Int -- deBruijn level
             | NApp Neutral Normal
             | NFst Neutral
             | NSnd Neutral
             | NNRec Closure Normal Closure2 Neutral
  deriving Show

data Normal = No Value Type
  deriving Show

evalSyn :: Syn -> Env -> Value
evalSyn (s ::: _) rho = evalChk s rho
evalSyn (Var x) rho = rho !! x
evalSyn (f :$: s) rho = vapp (evalSyn f rho) (evalChk s rho)
evalSyn (Fst e) rho = vfst (evalSyn e rho)
evalSyn (Snd e) rho = vsnd (evalSyn e rho)
evalSyn (NatRec t bas step n) rho = vnatrec (Cl t rho) (evalChk bas rho) (Cl2 step rho) (evalSyn n rho)

evalChk :: Chk -> Env -> Value
evalChk (Inf e) rho = evalSyn e rho
evalChk Ty rho = VTy
evalChk (Pi a b) rho = VPi (evalChk a rho) (Cl b rho)
evalChk (Sg a b) rho = VSg (evalChk a rho) (Cl b rho)
evalChk Nat rho = VNat
evalChk Unit rho = VUnit
evalChk G rho = VG
evalChk (Lam s) rho = VLam (Cl s rho)
evalChk (Pair s t) rho = VPair (evalChk s rho) (evalChk t rho)
evalChk Zero rho = VZero
evalChk (Succ s) rho = VSucc (evalChk s rho)
evalChk Ast rho = VAst
-- Group
evalChk GUnit rho = vgunit
evalChk (GInv s) rho = vginv (evalChk s rho)
evalChk (s :*: t) rho = vgmult (evalChk s rho) (evalChk t rho)

clapp :: Closure -> Value -> Value
clapp (Cl s rho) a = evalChk s (a:rho)

clapp2 :: Closure2 -> Value -> Value -> Value
clapp2 (Cl2 s rho) a b = evalChk s (b:a:rho)

vapp :: Value -> Value -> Value
vapp (VLam cl) t = clapp cl t
vapp (VNeutral (VPi a b) n) t = VNeutral (clapp b t) (NApp n (No a t))
vapp s t = error $ "vapp of " ++ show s

vfst :: Value -> Value
vfst (VPair a b) = a
vfst (VNeutral (VSg a b) n) = VNeutral a (NFst n)
vfst x           = error $ "vfst applied to non-pair " ++ show x

vsnd :: Value -> Value
vsnd (VPair a b) = b
vsnd p@(VNeutral (VSg a b) n) = VNeutral (clapp b (vfst p)) (NSnd n)
vsnd x           = error $ "vsnd applied to non-pair " ++ show x

vnatrec :: Closure -> Value -> Closure2 -> Value -> Value
vnatrec t base step VZero = base
vnatrec t base step (VSucc n) = clapp2 step n (vnatrec t base step n)
vnatrec t base step n@(VNeutral ty e) = VNeutral (clapp t n) (NNRec t (No base (clapp t VZero)) step e)

vgroup :: Value -> Value
vgroup v@(VGrp as) = v
vgroup (VNeutral VG n) = VGrp [(False,n)]
vgroup z = error $ "vgroup: " ++ show z ++ " ?!?"

vgunit :: Value
vgunit = VGrp []

unvgrp :: Value -> [(Bool, GGenerator)]
unvgrp v = case vgroup v of
  (VGrp as) -> as


vginv :: Value -> Value
vginv v = VGrp $ reverse $ map (not *** id) (unvgrp v)

vgmult :: Value -> Value -> Value
vgmult v v' = VGrp $ unvgrp v ++ unvgrp v'

vvar :: Type -> Int -> Value
vvar a i = VNeutral a (NVar i)

quote :: Int -> Type -> Value -> Chk
quote i (VPi a b) f = let x = vvar a i in
  Lam (quote (i + 1) (clapp b x) (vapp f x))
quote i (VSg a b) p = let p1 = vfst p; p2 = vsnd p in
  Pair (quote i a p1) (quote i (clapp b p1) p2)
quote i VNat v = case v of
  VZero        -> Zero
  VSucc n      -> Succ (quote i VNat n)
  VNeutral _ e -> Inf $ quoteNeutral i e
  x            -> error $ show x
quote i VUnit v = Ast
quote i VTy v = case v of
  VTy -> Ty
  (VPi a b) -> let x = vvar a i in
    Pi (quote i VTy a) (quote (i + 1) VTy (clapp b x))
  (VSg a b) -> let x = vvar a i in
    Sg (quote i VTy a) (quote (i + 1) VTy (clapp b x))
  VNat -> Nat
  VUnit -> Unit
  VG -> G
  VNeutral _ e -> Inf $ quoteNeutral i e
  z -> error $ "unexpected " ++ show z
quote i (VNeutral _ _) (VNeutral _ e) = Inf $ quoteNeutral i e
quote i VG v = quoteGroup $ map (id *** quoteNeutral i) (unvgrp v)

quoteNeutral :: Int -> Neutral -> Syn
quoteNeutral i (NVar x) = Var (i - (x + 1)) -- convert from levels to indices
quoteNeutral i (NApp e (No ty n)) = quoteNeutral i e :$: quote i ty n
quoteNeutral i (NFst e) = Fst (quoteNeutral i e)
quoteNeutral i (NSnd e) = Snd (quoteNeutral i e)
quoteNeutral i (NNRec t (No base tb) step e) =
  let x  = vvar VNat i
      tx = clapp t x
      y  = vvar tx (i + 1)
  in
  NatRec (quote (i + 1) VTy tx)
         (quote i tb base)
         (quote (i + 2) (clapp t (VSucc x)) (clapp2 step x y))
         (quoteNeutral i e)

quoteGroup :: [(Bool, Syn)] -> Chk
quoteGroup as = foldr mult GUnit $ cancel B0 $ sortOn snd as -- sort to make it Abelian; is it this easy?
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

norm :: Env -> Chk -> Type -> Chk
norm rho t ty = quote (length rho) ty (evalChk t rho)

type Context = [(Value,Type)]

typeof :: Int -> Context -> Maybe Type
typeof i gamma = pure $ snd $ gamma !! i

ctxtToEnv :: Context -> Env
ctxtToEnv = map fst

synth :: Int -> Context -> Syn -> Maybe Type
synth i gamma (s ::: t) = do
  isType i gamma t
  let t' = evalChk t (ctxtToEnv gamma)
  check i gamma t' s
  pure t'
synth i gamma (Var x) = typeof x gamma
synth i gamma (f :$: s) = do
  t <- synth i gamma f
  case t of
    VPi a b -> do
      check i gamma a s
      pure (clapp b (evalChk s (ctxtToEnv gamma)))
    y -> error $ "expected Pi, got " ++ show y
synth i gamma (Fst s) = do
  t <- synth i gamma s
  case t of
    VSg a b -> pure a
    y -> error $ "expected Sg, got " ++ show y
synth i gamma (Snd s) = do
  t <- synth i gamma s
  case t of
    VSg a b -> pure $ clapp b (evalSyn (Fst s) (ctxtToEnv gamma))
    y -> error $ "expected Sg, got " ++ show y
synth i gamma (NatRec t base step e) = do
  te <- synth i gamma e
  case te of
    VNat -> do
      let x = vvar VNat i
      let rho = ctxtToEnv gamma
      isType (i+1) ((x,VNat):gamma) t
      check i gamma (evalChk t (VZero:rho)) base
      let ty = evalChk t (x:rho)
      let y = vvar ty (i + 1)
      let tsucx = evalChk t (VSucc x:rho)
      check (i + 2) ((y, ty):(x,VNat):gamma) tsucx step
      pure $ evalChk t ((evalSyn e rho):rho)
    z    -> error $ "expected Nat, got " ++ show z

check :: Int -> Context -> Type -> Chk -> Maybe ()
check i gamma ty (Inf e) = do
  ty' <- synth i gamma e
  if quote i VTy ty == quote i VTy ty' then pure ()
  else error $ "expected " ++ show ty ++ "\ngot      " ++ show ty'
check i gamma ty Ty = case ty of
  VTy -> pure ()
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty (Pi a b) = case ty of
  VTy -> do
    isType i gamma a
    let a' = evalChk a (ctxtToEnv gamma)
    let x = vvar a' i
    isType (i + 1) ((x,a'):gamma) b
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty (Sg a b) = case ty of
  VTy -> do
    isType i gamma a
    let a' = evalChk a (ctxtToEnv gamma)
    let x = vvar a' i
    isType (i + 1) ((x,a'):gamma) b
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty G = case ty of
  VTy -> pure ()
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty Nat = case ty of
  VTy -> pure ()
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty (Lam s) = case ty of
  VPi a b -> do
    let x = vvar a i
    check (i+1) ((x,a):gamma) (clapp b x) s
  z   -> error $ "expected Pi, got " ++ show z
check i gamma ty (Pair s t) = case ty of
  VSg a b -> do
    check i gamma a s
    let s' = evalChk s (ctxtToEnv gamma)
    check i ((s', a):gamma) (clapp b s') t
  z   -> error $ "expected Sg, got " ++ show z
check i gamma ty Zero = case ty of
  VNat -> pure ()
  z   -> error $ "expected Nat, got " ++ show z
check i gamma ty (Succ s) = case ty of
  VNat -> check i gamma VNat s
  z   -> error $ "expected Nat, got " ++ show z
check i gamma ty GUnit = case ty of
  VG -> pure ()
  z   -> error $ "expected G, got " ++ show z
check i gamma ty (GInv s) = case ty of
  VG -> check i gamma VG s
  z   -> error $ "expected G, got " ++ show z
check i gamma ty (s :*: t) = case ty of
  VG -> do
    check i gamma VG s
    check i gamma VG t
  z   -> error $ "expected G, got " ++ show z
{-
check i gamma ty t =
  error $ "check: untreated type " ++ show ty ++ " and term " ++ show t
-}

isType :: Int -> Context -> Chk -> Maybe ()
isType i gamma t = check i gamma VTy t

-- tests

f = (Lam $ Lam $ body) ::: Pi G (Pi G G) where
    body = x :*: x :*: x :*: y :*: GInv (y :*: y :*: x)
    x = Inf $ Var 0
    y = Inf $ Var 1

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
