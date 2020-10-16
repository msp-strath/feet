{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Feet.NewSemantics where

import Prelude hiding (fail)

import Data.Char
import Data.Maybe
import Data.List
import Control.Arrow ((***))
import Control.Applicative
import Control.Monad hiding (fail)
import Control.Monad.Fail

import Utils.Bwd

import Feet.Syntax



clapp :: Closure -> Value -> Eval Value
clapp (Clo env s t body) v = do
  tv <- clapp t v
  withEnv (env :< (v :::: s)) $ chkEval tv (unAbs body)
clapp (CloK v) _ = return v

type NameSupply = Int

withEnv :: Env -> Eval a -> Eval a
withEnv env x = Eval (\ (ns, _) -> runEval x (ns, env))

envProj :: Int -> Eval (Cell Value)
envProj i = Eval (\ (_,env) -> bwdProj env i)

newtype Eval a = Eval { runEval :: (NameSupply, Env) -> a }
  deriving (Functor, Applicative, Monad)

getNameSupply :: Eval NameSupply
getNameSupply = Eval (\ (ns,_) -> ns)

closure :: Type -> Closure -> Abs Chk -> Eval Closure
closure s t b = Eval (\ (ns, env) -> Clo env s t b)

suppose :: Type -> (Value -> Eval x) -> Eval x
suppose t f = Eval (\ (ns, env) -> let x = VNeutral (NVar ns t) in runEval (f x) (ns+1,env))

instance MonadFail Eval where
  fail = error

normSyn :: NameSupply -> Syn -> Chk
normSyn b e = runEval go (b, B0)  where
  go = do
    (v :::: t) <- evalSyn e
    chkQuote t v b

normSyn0 :: Syn -> Chk
normSyn0 = normSyn 0

---------- Eval is abstract from here on ----------------------------------------


-- Evaluation --------------------

chkEval :: Type -> Chk -> Eval Value
chkEval VTy Ty = return VTy
chkEval VTy (Pi s t) = do
  s <- chkEval VTy s
  t <- closure s (CloK VTy) t
  return (VPi s t)
chkEval (VPi s t) (Lam u) = VLam <$> closure s t u
chkEval VTy (Sg s t) = do
  s <- chkEval VTy s
  t <- closure s (CloK VTy) t
  return (VSg s t)
chkEval (VSg s t) (Pair u w) = do
  u <- chkEval s u
  t <- clapp t u
  w <- chkEval t w
  return (VPair u w)
chkEval VTy (List s) = VList <$> chkEval VTy s
chkEval (VList s) Nil = return VNil
chkEval (VList s) (Single u) = do
  u <- chkEval s u
  return (VCons u VNil)
chkEval (VList s) (u :++: w) = do
  u <- chkEval (VList s) u
  w <- chkEval (VList s) w
  vappend u w
chkEval (VList s) (Map t e) = undefined
chkEval VTy Unit = return VUnit
chkEval VUnit Ast = return VAst
chkEval VTy Two = return VTwo
chkEval VTwo (Bit b) = return (VBit b)
chkEval VTy G = return VG
chkEval VG GUnit = undefined
chkEval VG (s :*: t) = undefined
chkEval VG (GInv s) = undefined
chkEval VTy (Thinning s xs ys) = do
  s <- chkEval VTy s
  xs <- chkEval (VList s) xs
  ys <- chkEval (VList s) ys
  return (VThinning s xs ys)
chkEval (VThinning s xs ys) x = undefined
chkEval s (Inf e) = do
  (v :::: _) <- evalSyn e
  return v


evalSyn :: Syn -> Eval (Cell Value)
evalSyn (s ::: t) = do
  t <- chkEval VTy t
  s <- chkEval t s
  return (s :::: t)
evalSyn (Inx i) = envProj i
evalSyn (Lev i (Hide t)) = return (VNeutral (NVar i t) :::: t)
evalSyn (e :$: a) = do
  (v :::: VPi s t) <- evalSyn e
  a <- chkEval s a
  ta <- clapp t a
  va <- vapp v a
  return (va :::: ta)
evalSyn (Fst e) = do
  (e :::: VSg s t) <- evalSyn e
  e1 <- vfst e
  return (e1 :::: s)
evalSyn (Snd e) = do
  (e :::: VSg s t) <- evalSyn e
  e1 <- vfst e
  e2 <- vsnd e
  tfst <- clapp t e1
  return (e2 :::: tfst)
evalSyn (ListRec mot base step e) = undefined

-- Semantic operations --------------------

vapp :: Value -> Value -> Eval Value
vapp (VLam b) v = clapp b v
vapp (VNeutral n) v = return (VNeutral (NApp n v))
vapp s t = error $ "vapp of " ++ show s

vfst :: Value -> Eval Value
vfst (VPair a b)  = return a
vfst (VNeutral n) = return (VNeutral (NFst n))
vfst x            = error $ "vfst applied to non-pair " ++ show x

vsnd :: Value -> Eval Value
vsnd (VPair a b)  = return b
vsnd (VNeutral n) = return (VNeutral (NSnd n))
vsnd x            = error $ "vsnd applied to non-pair " ++ show x

vappend :: Value -> Value -> Eval Value
vappend VNil              ys = return ys
vappend (VCons x xs)      ys = VCons x <$> vappend xs ys
-- vappend (VAppend clxs zs) ys = VAppend clxs (vappend zs ys)
-- vappend (VNeutral n)      ys = VAppend (ClId, n) ys
vappend xs ys = error $ "vappend applied to " ++ show xs

{-
vthinComp :: Value -> Value -> Eval Value
vthinComp v     VOne             = return v
vthinComp VOne  v'               = return v'
vthinComp v     VZero            = VZero
vthinComp VZero v'               = VZero
vthinComp v     (VPair VZero v') = VPair VZero (vthinComp v v')
vthinComp (VPair b v) (VPair VOne v') = VPair b (vthinComp v v')
vthinComp v (VThinComp v' v'') = vthinComp (vthinComp v v') v''
vthinComp v v' = VThinComp v v'
-}

-- Quotation --------------------

quote :: Type -> Value -> Eval Chk
quote t v = do
  ns <- getNameSupply
  chkQuote t v ns

-- b is base level, ie the name supply is >= b, and every level >= b
-- should be converted to an index
chkQuote :: Type -> Value -> Int -> Eval Chk
chkQuote VTy VTy b = return Ty
chkQuote VTy (VPi s t) b = do
  s' <- chkQuote VTy s b
  t' <- suppose s $ \ x -> do
    t <- clapp t x
    chkQuote VTy t b
  return (Pi s' (Abs t'))
chkQuote (VPi s t) f b = do
  fx' <- suppose s $ \ x -> do
    tx <- clapp t x
    fx <- vapp f x
    chkQuote tx fx b
  return (Lam (Abs fx'))
chkQuote VTy (VSg s t) b = do
  s' <- chkQuote VTy s b
  t' <- suppose s $ \ x -> do
    t <- clapp t x
    chkQuote VTy t b
  return (Sg s' (Abs t'))
chkQuote (VSg s t) u b = do
  u1 <- vfst u
  u2 <- vsnd u
  tu1 <- clapp t u1
  u1' <- chkQuote s u1 b
  u2' <- chkQuote tu1 u2 b
  return (Pair u1' u2')
chkQuote _ (VNeutral n) b = do
  (e :::: _) <- quoteSyn n b
  return (Inf e)

quoteSyn :: Neutral -> Int -> Eval (Cell Syn)
quoteSyn (NVar i t) b
  | i >= b = do
      ns <- getNameSupply
      return (Inx (ns - i - 1) :::: t)
  | otherwise = return (Lev i (Hide t) :::: t)
quoteSyn (NApp n v) b = do
  (f' :::: VPi s t) <- quoteSyn n b
  v' <- chkQuote s v b
  tv <- clapp t v
  return (f' :$: v' :::: tv)
quoteSyn (NFst n) b = do
  (n' :::: VSg s t) <- quoteSyn n b
  return (Fst n' :::: s)
quoteSyn (NSnd n) b = do
  (n' :::: VSg s t) <- quoteSyn n b
  n1 <- vfst (VNeutral n)
  tn1 <- clapp t n1
  return (Snd n' :::: tn1)
