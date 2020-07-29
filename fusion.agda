module fusion where

open import Data.List
open import Relation.Binary.PropositionalEquality

listrec : {A : Set} -> (P : List A -> Set) -> P [] -> ((y : A) ->  (ys : List A) -> (ysh : P ys) -> P (y ∷ ys)) ->
          (xs : List A) -> P xs
listrec P base step [] = base
listrec P base step (x ∷ xs) = step x xs (listrec P base step xs)

fusion : {A : Set} -> (P : List A -> Set) -> (base : P []) -> (step : (y : A) ->  (ys : List A) -> (ysh : P ys) -> P (y ∷ ys)) ->
         (xs ys : List A) ->
         listrec P base step (xs ++ ys) ≡ listrec (λ xs → P (xs ++ ys)) (listrec P base step ys) (λ z zs zsh → step z (zs ++ ys) zsh) xs
fusion P base step [] ys = refl
fusion P base step (x ∷ xs) ys rewrite fusion P base step xs ys = refl
