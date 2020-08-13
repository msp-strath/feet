module Tests where

import Feet.Syntax
import Feet.Semantics

-- tests

thin1 = Lam . Abs $ One

thin2 = Lam . Abs $ Inf $ ListRec (Abs $ Thinning Unit (Single Ast :++: Inf (Var 0)) (Single Ast :++: Inf (Var 0))) (Pair One Ast) (Abs . Abs . Abs $ Pair One (Inf $ Var 0)) (Var 0)

thin12Ty = Pi nat . Abs $ Thinning Unit (Single Ast :++: Inf (Var 0)) (Single Ast :++: Inf (Var 0))

thin3 = ThinComp (Inf $ (thin2 ::: thin12Ty) :$: two'') (Inf $ (thin2 ::: thin12Ty) :$: two'')

thin3Ty = Thinning Unit (Inf $ (suc ::: sucTy) :$: Inf two) (Inf $ (suc ::: sucTy) :$: Inf two)

thinType = Lam {-xs-}. Abs . Lam {-x-}. Abs $ Thinning Two (Inf $ Var 1) ((Single $ Inf $ Var 0) :++: (Inf $ Var 1))

thinTypeTy = Pi (List Two) (Abs $ Pi Two (Abs Ty))

tz = Lam . Abs $ Pair Zero One

tzTy = Pi (List Two) (Abs $ Thinning Two (Inf $ Var 0) (Cons Zero (Inf $ Var 0)))
tszTy = Pi (List Two) (Abs $ Thinning Two (Cons Zero (Inf $ Var 0)) (Cons One (Cons Zero (Inf $ Var 0))))
tsszTy = Pi (List Two) (Abs $ Thinning Two (Cons One (Cons Zero (Inf $ Var 0))) (Cons Zero (Cons One (Cons Zero (Inf $ Var 0)))))

tzcomp = Lam . Abs $
  ThinComp
    (Inf $ (tz ::: tzTy) :$: (Inf $ Var 0))
    (ThinComp
      (Inf $ (tz ::: tszTy) :$: (Inf $ Var 0))
      (Inf $ (tz ::: tsszTy) :$: (Inf $ Var 0)))

tzcomp' = Lam . Abs $
  ThinComp
    (ThinComp
     (Inf $ (tz ::: tzTy) :$: (Inf $ Var 0))
     (Inf $ (tz ::: tszTy) :$: (Inf $ Var 0)))
    (Inf $ (tz ::: tsszTy) :$: (Inf $ Var 0))

tzcompTy = Pi (List Two) (Abs $ Thinning Two (Inf $ Var 0) (Cons Zero (Cons One (Cons Zero (Inf $ Var 0)))))

tzcompNilTy = Thinning Two Nil (Cons Zero (Cons One (Cons Zero Nil)))

tzcompNil = Inf $ (tzcomp' ::: tzcompTy) :$: Cons One Nil

f = Lam . Abs $ Lam . Abs $ body where
    body = x :*: x :*: x :*: y :*: GInv (y :*: y :*: x)
    x = Inf $ Var 0
    y = Inf $ Var 1

fTy = Pi G . Abs $ Pi G . Abs $ G

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

