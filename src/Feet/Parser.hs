{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Feet.Parser where

import Control.Applicative
import Control.Monad hiding (fail)
import Control.Arrow ((***))
import Data.List
import Data.Char

import Feet.Syntax
import Feet.Frontend

newtype DBP x = DBP {dbp :: [String] -> String -> [(x, String)]} deriving (Semigroup, Monoid)

instance Monad DBP where
  return x = DBP $ \ is s -> return (x, s)
  DBP a >>= k = DBP $ \ is s -> do
    (a, s) <- a is s
    dbp (k a) is s
instance Applicative DBP where
  pure = return
  f <*> a = f >>= \ f -> a >>= \ a -> return (f a)
instance Functor DBP where
  fmap = (<*>) . pure
instance Alternative DBP where empty = mempty ; (<|>) = (<>)

push :: String -> DBP x -> DBP (Abs x)
push i (DBP p) = DBP $ \ is s -> (Abs *** id) <$> p (i : is) s

dbix :: String -> DBP Int
dbix j = DBP $ \ is s -> case findIndex (j ==) is of
  Just i  -> [(i, s)]
  Nothing -> []

get :: (Char -> Bool) -> DBP Char
get p = DBP $ \ is s -> case s of
  c : s | p c -> [(c, s)]
  _ -> []

punc :: String -> DBP ()
punc s = () <$ traverse (get . (==)) s

spc :: DBP ()
spc = () <$ many (get isSpace)

pId :: DBP String
pId = (:) <$> get isAlpha <*> many (get more) where
  more c = isAlphaNum c || elem c "'_$"

pTel :: (Tel -> DBP x) -> DBP x
pTel k = pIds >>= \ xs -> id <$ spc <* punc ":" <* spc <*> (pChk 0 >>= bind k xs)
  where
  pIds = (:) <$> pId <*> go where go = id <$ get isSpace <* spc <*> pIds <|> pure []
  pMore k =
     (id <$ spc <* punc "," <* spc <*>
        (pIds >>= \ xs -> id <$ spc <* punc ":" <* spc <*> (pChk 0 >>= bind k xs))
      <|> k T0)
  bind k [] s = pMore k
  bind k (x : xs) s = unAbs <$> push x (bind (k . (s :\:) . Abs) xs (s <^> negate 2))

pChk :: Int -> DBP Chk
pChk l =
  id <$ guard (l == 0) <*>
    (     Lam <$ punc "\\" <* spc <*>
            (pId >>= \ x -> push x (id <$ spc <*> pChk 0))
     <|>  id <$ punc "(" <* spc <*> pTel pPiSg
     <|>  (pId >>= \ x ->
            flip Map <$ spc <* punc "<-" <* spc <*> pSyn 0
              <* spc <* punc "|" <* spc <*> push x (pChk 0))
    )
  <|> (pHead >>= pMore l) where
  pHead = 
    Inf <$> pSyn l
    <|> Ty <$ punc "Ty"
    <|> List <$ punc "List" <* spc <*> pChk 2
    <|> Unit <$ punc "Unit"
    <|> List Unit <$ punc "Nat"
    <|> Two <$ punc "Two" <|> Zero <$ punc "0" <|> One <$ punc "1"
    <|> G <$ punc "G" <|> GUnit <$ punc "@" <|> GInv <$ punc "!" <* spc <*> pHead
    <|> id <$ punc "[" <* spc <*> pList <* spc <* punc "]"
    <|> tuple <$ punc "(" <* spc <*> pList <* spc <* punc ")"
  pMore l s =
    id <$ guard (l == 0) <* spc <*>
      (    Pi s <$ punc "->" <* spc <*> push "" (pChk 0)
      <|>  Sg s <$ punc "><" <* spc <*> push "" (pChk 0)
      <|>  (s :++:) <$ punc "++" <* spc <*> pChk 0
      <|>  (s :*:) <$ punc "." <* spc <*> pChk 0
      <|>  flip Thinning s <$ punc "`-" <* spc <*>
             pChk 0 <* spc <* punc ">" <* spc <*> pChk 0
      <|>  ((ThinComp s <$ punc "`;" <* spc <*> pHead) >>= pMore l)
      )
    <|> pure s
  tuple (Single t) = t
  tuple Nil = Ast
  tuple (s :++: t) = Pair (tuple s) (tuple t)
  tuple z = error "it has to be a list to be tupled"
  pPiSg :: Tel -> DBP Chk
  pPiSg t = go t <$ spc <* punc ")" <* spc
      <*> (Pi <$ punc "->" <|> Sg <$ punc "><") <* spc <*> pChk 0
    where
    go :: Tel -> (Chk -> Abs Chk -> Chk) -> Chk -> Chk
    go T0 bi body = body
    go (s :\: Abs t) bi body = bi s . Abs $ go t bi body

pSyn :: Int -> DBP Syn
pSyn l = pHead >>= pMore l where

  pHead :: DBP Syn
  pHead = Var <$> (pId >>= dbix)
      <|> (:::) <$ punc "(" <* spc <*> (pChk 0 >>= novar)
            <* spc <* punc ":" <* spc
            <*> pChk 0 <* spc <* punc ")"

  -- We avoid ambiguity between telescopes and radicals by disallowing
  -- radical variables (for there is never need to annotate a variable).
  novar :: Chk -> DBP Chk
  novar (Inf (Var _)) = empty
  novar t = pure t

  pMore :: Int -> Syn -> DBP Syn
  pMore l e =
    ((id <$ guard (l < 2) <* spc <*> (
     (e :$:) <$> pChk 2
     <|>
     mklr e <$ punc "{" <* spc
       <*> (pId >>= \ x -> push x (id <$ spc <*> pChk 0))
       <* spc <* punc ";" <* spc
       <*> (id <$ punc "[" <* spc <* punc "]" <* spc <* punc "->" <* spc <*> pChk 0)
       <* spc <* punc ";" <* spc
       <*> (id <$ punc "[" <* spc <*> (pId >>= \ x ->
            id <$ spc <* punc "]" <* spc <* punc "++" <* spc <*> (pId >>= \ xs ->
             id <$ spc <* punc "->" <* spc <*>
               push x (push xs (push (xs ++ "$") (pChk 0)))
            )))
        <* spc <* punc "}"
      <|>
      Fst e <$ punc ".-" <|> Snd e <$ punc "-."
      )) >>= pMore l)
    <|> pure e

  mklr e t b s = ListRec t b s e


pList :: DBP Chk
pList = pSome <|> pure Nil where
  pSome = ((Single <$> pChk 0) >>= pMore)
  pMore xs = (xs :++:) <$ spc <* punc "," <* spc <*> pSome <|> pure xs

pTask :: DBP Task
pTask = (pTel $ \ ga -> (ga :|-) <$ spc <* punc "|-" <* spc <*> pTask)
    <|> (pId >>= \ x ->
         (:&) <$ spc <* punc "=" <* spc <*> ((x,) <$> pSyn 0)
         <* spc <* punc ";" <* spc
         <*> push x pTask)
    <|> pure Done

pGo :: DBP x -> String -> [x]
pGo p s = do
  (x, "") <- dbp p [] s
  return x

class Thin t where
  (<^>) :: t -> Integer -> t

instance Thin Int where
  i <^> th = case (th `mod` 2, th `div` 2) of
    (0, th) -> 1 + (i <^> th)
    (1, th) -> case i of
      0 -> 0
      _ -> 1 + ((i - 1) <^> th)

instance Thin x => Thin (Abs x) where
  Abs t <^> th = Abs (t <^> (2 * th + 1))

instance Thin Chk where
  Inf e <^> th = Inf (e <^> th)
  Pi s t <^> th = Pi (s <^> th) (t <^> th)
  Sg s t <^> th = Pi (s <^> th) (t <^> th)
  List t <^> th = List (t <^> th)
  Thinning a b c <^> th = Thinning (a <^> th) (b <^> th) (c <^> th)
  Lam t <^> th = Lam (t <^> th)
  Pair s t <^> th = Pair (s <^> th) (t <^> th)
  Single t <^> th = Single (t <^> th)
  (s :++: t) <^> th = (s <^> th) :++: (t <^> th)
  Map f t <^> th = Map (f <^> th) (t <^> th)
  (s :*: t) <^> th = (s <^> th) :*: (t <^> th)
  GInv t <^> th = GInv (t <^> th)
  t <^> th = t -- should only be used at arity 0  
  
instance Thin Syn where
  (t ::: y) <^> th = (t <^> th) ::: (y <^> th)
  Var i <^> th = Var (i <^> th)
  (f :$: s) <^> th = (f <^> th) :$: (s <^> th)
  ListRec p n c e <^> th = ListRec (p <^> th) (n <^> th) (c <^> th) (e <^> th)
