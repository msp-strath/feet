{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
module Nbe where

import Data.Maybe
import Data.List
import Control.Arrow ((***))

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

data Syn = Chk ::: Chk -- type annotation
         | Var Int     -- deBruijn index
         -- application
         | Syn :$: Chk
         -- projections
         | Fst Syn
         | Snd Syn
         -- naturals
         | ListRec Chk Chk Chk Syn
         -- group
  deriving (Show, Eq, Ord)

data Chk = Inf Syn  -- embedding inferable
         -- types
         | Ty
         | Pi Chk Chk
         | Sg Chk Chk
         | List Chk
         | Unit
         | G  -- group
         -- functions
         | Lam Chk
         -- sigma
         | Pair Chk Chk
         -- lists
         | Nil
         | Single Chk
         | Chk :++: Chk
         | Map Chk Syn -- chk: body of function, syn: list
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

data Closure = Cl Chk Env
             | ClId
             | ClComp Closure Closure -- neither ClId, left arg not ClComp
  deriving Show

clComp :: Closure -> Closure -> Closure
clComp ClId cl' = cl'
clComp cl ClId = cl
-- clComp (ClComp cl cl') cl'' = clComp cl (clComp cl' cl'')
clComp cl cl' = ClComp cl cl'


data Closure3 = Cl3 Chk Env -- closure with three free variables
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

{-
data Cell = Cell Value Type
  deriving Show
-}

evalSyn :: Syn -> Env -> Value
evalSyn (s ::: _) rho = evalChk s rho
evalSyn (Var x) rho = rho !! x
evalSyn (f :$: s) rho = vapp (evalSyn f rho) (evalChk s rho)
evalSyn (Fst e) rho = vfst (evalSyn e rho)
evalSyn (Snd e) rho = vsnd (evalSyn e rho)
evalSyn (ListRec t bas step n) rho = vlistrec (Cl t rho) (evalChk bas rho) (Cl3 step rho) (evalSyn n rho)

{-
vlistrecT a b c d =
  trace ("\n=====vlistrec=====\nt: " ++ show a ++ "\nbase: " ++ show b ++ "\nstep: " ++ show c ++ "\nv: " ++ show d ++ "\n==> " ++ show t ++ "\n==============") $ t
  where t = vlistrec a b c d
-}

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
clapp (Cl s rho) v      = evalChk s (v:rho)
clapp ClId v            = v
clapp (ClComp cl cl') v = clapp cl (clapp cl' v)

clapp3 :: Closure3 -> Value -> Value -> Value -> Value
clapp3 (Cl3 s rho) a b c = evalChk s (c:b:a:rho)
clapp3 (ClComp3 f a b c) x y z = clapp3 f (clapp a x) (clapp b y) (clapp c z)

vneutral :: Type -> Neutral -> Value
vneutral VUnit n = VAst
vneutral (VList a) n = VAppend (ClId, n) VNil
vneutral VG n = VGrp [(False, n)]
vneutral ty n = VNeutral ty n

vapp :: Value -> Value -> Value
vapp (VLam cl) t = clapp cl t
vapp (VNeutral (VPi a b) n) t = vneutral (clapp b t) (NApp n a)
vapp s t = error $ "vapp of " ++ show s

vfst :: Value -> Value
vfst (VPair a b) = a
vfst (VNeutral (VSg a b) n) = vneutral a (NFst n)
vfst x           = error $ "vfst applied to non-pair " ++ show x

vsnd :: Value -> Value
vsnd (VPair a b) = b
vsnd p@(VNeutral (VSg a b) n) = vneutral (clapp b (vfst p)) (NSnd n)
vsnd x           = error $ "vsnd applied to non-pair " ++ show x

vlistrec :: Closure -> Value -> Closure3 -> Value -> Value
-- vlistrec t base step v | trace ("\n===listrec===\nt: " ++ show t ++ "\nbase: " ++ show base ++ "\nstep: " ++ show step ++ "\nv: " ++ show v ++ "\n=============\n") False = undefined
vlistrec t base step VNil = base
vlistrec t base step (VCons x xs) = clapp3 step x xs (vlistrec t base step xs)
vlistrec t base step v@(VAppend (cl, xs) ys) =
  vneutral (clapp t v) (NLRec (clComp t appCl) (vlistrec t base step ys)
                              (ClComp3 step cl appCl ClId) xs)
  where appCl = Cl (Inf (Var 0) :++: Inf (Var 1)) [ys]
-- vlistrec t base step n@(VNeutral ty e) = vneutral (clapp t n) (NLRec t base step e)

vappend :: Value -> Value -> Value
vappend VNil ys = ys
vappend (VCons x xs) ys = VCons x (vappend xs ys)
vappend (VAppend clxs zs) ys = VAppend clxs (vappend zs ys)
vappend xs ys = error $ "vappend applied to " ++ show xs

vmap :: Closure -> Value -> Value
vmap cl VNil = VNil
vmap cl (VCons x xs) = VCons (clapp cl x) (vmap cl xs)
vmap cl (VAppend (ncl, n) v) = VAppend (clComp cl ncl, n) (vmap cl v)

vgroup :: Value -> Value
vgroup v@(VGrp as) = v
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
vvar a i = vneutral a (NVar i a)

equalType :: Int -> Type -> Type -> Maybe (Value -> Value -> Bool)
equalType i a b = case quote i VTy a == quote i VTy b of
  False -> Nothing
  True -> Just (\ x y -> quote i a x == quote i b y)

quote :: Int -> Type -> Value -> Chk
-- quote i ty v | trace ("quote ty: " ++ show ty ++ " v: " ++ show v) False = undefined
quote i (VPi a b) f = let x = vvar a i in
  Lam (quote (i + 1) (clapp b x) (vapp f x))
quote i (VSg a b) p = let p1 = vfst p; p2 = vsnd p in
  Pair (quote i a p1) (quote i (clapp b p1) p2)
quote i (VList a) v = quoteList i a v
quote i VUnit v = Ast
quote i VTy v = case v of
  VTy -> Ty
  (VPi a b) -> let x = vvar a i in
    Pi (quote i VTy a) (quote (i + 1) VTy (clapp b x))
  (VSg a b) -> let x = vvar a i in
    Sg (quote i VTy a) (quote (i + 1) VTy (clapp b x))
  VList a -> List (quote i VTy a)
  VUnit -> Unit
  VG -> G
  VNeutral _ e -> Inf (quoteNeutral i e)
  z -> error $ "unexpected " ++ show z
quote i (VNeutral _ _) (VNeutral _ e) = Inf (quoteNeutral i e)
quote i VG v = quoteGroup $ map (id *** quoteNeutral i) (unvgrp v)

quoteNeutralTy :: Int -> Neutral -> (Syn, Type)
quoteNeutralTy i (NVar x ty) = (Var (i - (x + 1)), ty) -- convert from levels to indices
quoteNeutralTy i (NApp f a) = case quoteNeutralTy i f of
 (f', VPi s t) -> (f' :$: quote i s a, clapp t a)
 x  -> error $ "quoteNeutralTy: app of " ++ show x
quoteNeutralTy i (NFst e) = case quoteNeutralTy i e of
  (e', VSg s t) -> (Fst e', s)
  x -> error $ "quoteNeutralTy: fst of " ++ show x
quoteNeutralTy i (NSnd e) = case quoteNeutralTy i e of
  (e', VSg s t) -> (Snd e', clapp t (vfst (vneutral (VSg s t) e)))
  x -> error $ "quoteNeutralTy: snd of " ++ show x
quoteNeutralTy i (NLRec t base step e) = case quoteNeutralTy i e of
  (e', VList a) ->
    let
      xs = vvar (VList a) i
      txs = clapp t xs
      y = vvar a i
      ys = vvar (VList a) (i + 1)
      ysh = vvar (clapp t ys) (i + 2)
    in
      (ListRec (quote (i + 1) VTy txs)
               (quote i (clapp t VNil) base)
               (quote (i + 3) (clapp t (VCons y ys)) (clapp3 step y ys ysh))
               e', clapp t (vneutral (VList a) e))
  x -> error $ "quoteNeutralTy: listrec of " ++ show x

quoteNeutral :: Int -> Neutral -> Syn
quoteNeutral i = fst . quoteNeutralTy i

quoteList :: Int -> {- Element -} Type -> Value -> Chk
quoteList i ty VNil = Nil
quoteList i ty (VCons x xs) = Single (quote i ty x) +++ quoteList i ty xs
quoteList i b (VAppend (f, ns) ys) = case quoteNeutralTy i ns of
  (xs, VList a) -> let
      rest = quoteList i b ys
      x = vvar a i
      fx = clapp f x
      xisfx = case equalType (i + 1) a b of
            Nothing -> False
            Just eq -> eq x fx
      in
        if xisfx then Inf xs +++ rest
        else Map (quote (i + 1) b fx) xs +++ rest
-- no case for VNeutral, because of our invariant
quoteList i ty x = error $ "quoteList applied to " ++ show x

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
synth i gamma (ListRec t base step e) = do
  te <- synth i gamma e
  case te of
    VList a -> do
      let xs = vvar (VList a) i
      let rho = ctxtToEnv gamma
      isType (i+1) ((xs,VList a):gamma) t
      check i gamma (evalChk t (VNil:rho)) base
      let y   = vvar a i
      let ys  = vvar (VList a) (i + 1)
      let tys = evalChk t (ys:rho)
      let ysh = vvar tys (i + 2)
      let tyys = evalChk t (VCons y ys:rho)
      check (i + 3) ((ysh, tys):(ys, VList a):(y,a):gamma) tyys step
      pure $ evalChk t ((evalSyn e rho):rho)
    z    -> error $ "expected List, got " ++ show z

check :: Int -> Context -> Type -> Chk -> Maybe ()
check i gamma ty (Inf e) = do
  ty' <- synth i gamma e
  case equalType i ty ty' of
    Just _ -> pure ()
    Nothing -> error $ "expected " ++ show ty ++ "\ngot      " ++ show ty'
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
check i gamma ty Unit = case ty of
  VTy -> pure ()
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty G = case ty of
  VTy -> pure ()
  z   -> error $ "expected Ty, got " ++ show z
check i gamma ty (List a) = case ty of
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
    check i gamma (clapp b s') t
  z   -> error $ "expected Sg, got " ++ show z
check i gamma ty Ast = case ty of
  VUnit -> pure ()
  z   -> error $ "expected Unit, got " ++ show z
check i gamma ty Nil = case ty of
  VList a -> pure ()
  z   -> error $ "expected List, got " ++ show z
check i gamma ty (Single s) = case ty of
  VList a -> check i gamma a s
  z   -> error $ "expected List, got " ++ show z
check i gamma ty (s :++: t) = case ty of
  VList a -> do
    check i gamma (VList a) s
    check i gamma (VList a) t
  z   -> error $ "expected List, got " ++ show z
check i gamma ty (Map s e) = case ty of
  VList b -> case synth i gamma e of
      Just (VList a) -> do
        let x = vvar a i
        check (i + 1) ((x, a):gamma) b s
      z -> error $ "expected List, got " ++ show z
  z   -> error $ "expected List, got " ++ show z
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

nat = List Unit
zero = Nil
suc = Lam $ Single Ast :++: Inf (Var 0)

sucTy = Pi nat nat

append = (Lam $ Lam $ Lam $ Inf $ ListRec (List (Inf $ Var 3)) (Inf $ Var 0) (Single (Inf $ Var 2) :++: Inf (Var 0)) (Var 1))
         :::
         Pi Ty (Pi (List (Inf $ Var 0)) (Pi (List (Inf $ Var 1)) (List (Inf $ Var 2))))

two = ((append :$: Unit) :$: Inf ((suc ::: sucTy) :$: zero)) :$: Inf ((suc ::: sucTy) :$: zero)

two' = Lam (Inf $ ((append :$: Unit) :$: Inf ((suc ::: sucTy) :$: Inf (Var 0))) :$: Inf ((suc ::: sucTy) :$: zero))

two'' = Map (Inf $ Var 0) two

mapswap = Lam $ Map (Pair (Inf $ Snd $ Var 0) (Inf $ Fst $ Var 0)) (Var 0)

mapswapTy = Pi (List (Sg Unit Unit)) (List (Sg Unit Unit))

mapswapTy' = Pi (List (Sg nat nat)) (List (Sg nat nat))

mapswapmapswap = Lam $ Inf $ (mapswap ::: mapswapTy') :$: (Inf $ (mapswap ::: mapswapTy') :$: (Inf $ Var 0))

toTuples = Lam $ Inf $ ListRec Ty Unit (Sg (Inf $ Var 2) (Inf $ Var 1)) (Var 0)

toTuplesTy = Pi (List Ty) Ty

allList' = Lam {-A-} $ Lam {-P-} $ Lam {-xs-} $ Inf $ (toTuples ::: toTuplesTy) :$: (Map (Inf $ Var 2 :$: (Inf $ Var 0)) (Var 0))

allList = Lam {-A-} $ Lam {-P-} $ Lam {-xs-} $ Inf $
  ListRec Ty Unit (Sg (Inf $ (Var 4) :$: Inf (Var 2)) (Inf $ Var 1)) (Var 0)

allListTy = Pi Ty (Pi (Pi (Inf $ Var 0) Ty) (Pi (List (Inf $ Var 1)) Ty))

r = Lam $ Lam $ Inf $
  (allList ::: allListTy) :$: Unit :$: (Lam Ty) :$: (Inf (Var 1) :++: Inf (Var 0))

r' = Lam $ Lam $ Inf $
  (allList' ::: allListTy) :$: Unit :$: (Lam Ty) :$: (Inf (Var 1) :++: Inf (Var 0))

rTy = Pi nat (Pi nat Ty)

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
