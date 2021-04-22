{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Feet.Parser where

import Control.Applicative
import Control.Monad hiding (fail)
import Control.Arrow ((***))
import Data.List
import Data.Char
import Text.Read (readMaybe)

import Feet.Syntax
import Feet.Frontend

newtype DBP x = DBP {dbp :: [String] -> String -> [(x, String)]}
  deriving (Semigroup, Monoid)

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

instance Alternative DBP where
  empty = mempty
  (<|>) = (<>)

push :: String -> DBP x -> DBP x
push i (DBP p) = DBP $ \ is s -> p (i : is) s


dbix :: String -> DBP Int
dbix j = DBP $ \ is s -> case findIndex (j ==) is of
  Just i  -> [(i, s)]
  Nothing -> []

get :: (Char -> Bool) -> DBP Char
get p = DBP $ \ is s -> case s of
  c : s | p c -> [(c, s)]
  _ -> []

string :: String -> DBP String
string = traverse (get . (==))

punc :: String -> DBP ()
punc s = () <$ string s

spc :: DBP ()
spc = () <$ many (get isSpace)

spaced :: DBP x -> DBP x
spaced p = spc *> p <* spc

pId :: DBP String
pId = (:) <$> get isAlpha <*> many (get $ \ c -> isAlphaNum c || elem c "'_$")

pTel :: (Tel -> DBP x) -> DBP x
pTel k = do
  xs <- pIds
  spaced $ punc ":"
  pChk 0 >>= bind k xs
  where
    pIds = (:) <$> pId <*> (id <$ get isSpace <* spc <*> pIds <|> pure [])
    pMore k = (do
      spaced $ punc ","
      xs <- pIds
      spaced $ punc ":"
      pChk 0 >>= bind k xs)
      <|> k T0
    bind k [] s = pMore k
    bind k (x : xs) s = push x (bind (k . ((x,s) :\:)) xs (s <^> Th (negate 2)))

pChk :: Int -> DBP ChkTm
pChk l =
  id <$ guard (l == 0) <*>
    (     (do
              punc "\\"
              x <- spaced pId
              t <- push x (pChk 0)
              return $ Lam t)
     <|>  id <$ punc "(" <* spc <*> pTel pPiSg
    )
  <|> (pHead >>= pMore l) where
  pHead =
    (do
        a <- pAdapter 0
        spc
        e <- pSyn l
        return (e :-: a)
    )
    <|> Ty <$ punc "Ty"
    <|> List <$ punc "List" <* spc <*> pChk 2
    <|> Enum <$ punc "Enum" <* spc <*> pChk 2
    -- TODO: [ _P' | (v : _X') <- xs ]"
    <|> (do
            punc "AllT"
            spc
            _X <- pChk 0
            spaced $ punc "("
            x <- spaced pId
            _P <- push x (pChk 0)
            spaced $ punc ")"
            xs <- pChk 0
            return (AllT _X _P xs))
    <|> One <$ punc "One"
    <|> Nat <$ punc "Nat"
    <|> Atom <$ punc "Atom"
    <|> pNat
    <|> Void <$ punc "<>"
    <|> Nil <$ punc "."
    <|> Th1 <$ punc "1.."
    <|> Th0 <$ punc "0.."
    <|> (\ x -> Cons (A [x])) <$> get (\ x -> x == '0' || x == '1') <*> pChk 2
    <|> A <$ punc "'" <*> pId
    <|> FAb <$ punc "FAb" <* spc <*> pChk 2
    <|> FOne <$ punc "@"
    <|> Inv <$ punc "!" <* spc <*> pHead
    <|> id <$ punc "[" <* spc <*> pList <* spc <* punc "]"
    <|> tuple <$ punc "(" <* spc <*> pList <* spc <* punc ")"
  pMore l s =
    id <$ guard (l == 0) <* spc <*>
      (    Pi s <$ punc "->" <* spc <*> push "" (pChk 0)
      <|>  Sg s <$ punc "*" <* spc <*> push "" (pChk 0)
      <|>  (s :++:) <$ punc "++" <* spc <*> pChk 0
      <|>  (s :.:) <$ punc "." <* spc <*> (pChk 2 >>= noNil)
      <|>  (do
               spaced $ punc "<["
               _X <- pChk 0
               spaced $ punc "]="
               de <- pChk 0
               return (Thinning _X s de))
      <|>  ((ThSemi s <$ punc "`;" <* spc <*> pHead) >>= pMore l)
      )
    <|> pure s
  noNil :: ChkTm -> DBP ChkTm
  noNil Nil = empty
  noNil t = pure t
  tuple (Single t) = t
  tuple Nil = Void
  tuple (s :++: t) = (tuple s) :& (tuple t)
  tuple z = error "it has to be a list to be tupled"
  pPiSg :: Tel -> DBP ChkTm
  pPiSg t = go t <$ spc <* punc ")" <* spc
      <*> (Pi <$ punc "->" <|> Sg <$ punc "*") <* spc <*> pChk 0
    where
    go :: Tel -> (ChkTm -> ChkTm -> ChkTm) -> ChkTm -> ChkTm
    go T0 bi body = body
    go ((x,s) :\: t) bi body = bi s $ go t bi body

pAdapter :: Int -> DBP Adapter
pAdapter l =
  List <$ punc "List" <* spc <*> pChk l
  <|> Hom <$ punc "Hom" <* spc <*> pChk l
  <|> Enum <$ punc "Enum" <* spc <*> pChk l
  <|> Thinning <$ punc "Th" <* spc <*> pChk l <* spc <*> pChk l <* spc <*> pChk l
  <|> AllT <$ punc "All" <* spc <*> pChk l <* spc <*> pChk l <* spc <*> pChk l
  <|> pure Idapter

pVar :: DBP SynTm
pVar = do
  x <- pId
  V <$> dbix x

pSyn :: Int -> DBP SynTm
pSyn l = pHead >>= pMore l where
  pHead :: DBP SynTm
  pHead = pVar
      <|> do
            punc "(" <* spc
            s <- pChk 0 >>= novar
            spaced $ punc ":"
            ty <- pChk 0
            spc *> punc ")"
            return (s ::: ty)

  -- We avoid ambiguity between telescopes and radicals by disallowing
  -- radical variables (for there is never need to annotate a variable).
  novar :: ChkTm -> DBP ChkTm
  novar (E (V _)) = empty
  novar t = pure t

  pMore :: Int -> SynTm -> DBP SynTm
  pMore l e =
    ((id <$ guard (l < 2) <* spc <*> (
     (e :$) <$> pChk 2
     <|>
     (do
         punc "{"
         x <- spaced pId
         t <- push x (pChk 0)
         spaced $ punc ";"
         punc "[" <* spc <* punc "]"
         spaced $ punc "->"
         b <- pChk 0
         spaced $ punc ";"
         punc "["
         x <- spaced pId
         punc "]" <* spc <* punc "++"
         xs <- spaced pId
         punc "->"
         s <- spaced $ push x (push xs (push (xs ++ "$") (pChk 0)))
         punc "}"
         return (e :$ ListElim t b s)
     )
      <|> (e :$ Fst) <$ punc "-fst"
      <|> (e :$ Snd) <$ punc "-snd"
      )) >>= pMore l)
    <|> pure e

pNat :: DBP ChkTm
pNat = do
  t <- many (get isNumber)
  case readMaybe t of
    Just n -> return (fromInteger n)
    Nothing -> empty

pList :: DBP ChkTm
pList = pSome <|> pure Nil where
  pSome = ((Single <$> pChk 0) >>= pMore)
  pMore xs = (xs :++:) <$ spc <* punc "," <* spc <*> pSome <|> pure xs

pTask :: DBP Task
pTask = (pTel $ \ ga -> (ga :|-) <$ spc <* punc "|-" <* spc <*> pTask)
    <|> (pId >>= \ x ->
         (:&&) <$ spc <* punc "=" <* spc <*> ((x,) <$> pSyn 0)
         <* spc <* punc ";" <* spc
         <*> push x pTask)
    <|> pure Done

pGo :: DBP x -> String -> [x]
pGo p s = do
  (x, "") <- dbp p mempty s
  return x
