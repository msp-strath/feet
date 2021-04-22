{-# LANGUAGE  FlexibleInstances
            , PatternSynonyms
            , TupleSections
            , GADTs
            , DeriveFunctor
            , LambdaCase
            , TypeFamilies
#-}
module Feet.Print where

import Utils.Utils
import Utils.Bwd

import Feet.Syntax
import Feet.Semantics

-- type-directed printing

printNormSyn :: SynTm -> IO ()
printNormSyn = putStrLn . either id id . run . prettyNormSyn

prettyNormSyn :: SynTm -> TCM String
prettyNormSyn e = do
  (e, t) <- weakEvalSyn e
  n <- normalise (t, upsE e)
  refresh "print" $ chkPrint t n 0


chkPrint :: ChkTm -> ChkTm -> Int -> TCM String
chkPrint Ty _T p = case _T of
  Ty -> return "Ty"
  Atom -> return "Atom"
  Enum as -> do
    as' <- chkPrint (List Atom) as pArg
    return . paren p pArg $ concat ["Enum ", as']
  Pi _S _T -> do
    _S' <- chkPrint Ty _S 0
    (v, _T') <- fresh (nomo _S, _S) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_T // x) 0
    return . paren p pArg $ concat ["(", v, " : ", _S', ") -> ", _T']
  Sg _S _T ->  do
    _S' <- chkPrint Ty _S 0
    (v, _T') <- fresh (nomo _S, _S) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_T // x) 0
    return . paren p pArg $ concat ["(", v, " : ", _S', ") * ", _T']
  One -> return "One"
  Nat -> return "Nat"
  List _X -> do
    _X' <- chkPrint Ty _X pArg
    return . paren p pArg $ concat ["List ", _X']
  FAb _X -> do
    _X' <- chkPrint Ty _X pArg
    return . paren p pArg $ concat ["FAb ", _X']
  AllT _X _P xs -> do
    _X' <- chkPrint Ty _X 0
    (v, _P') <- fresh (nomo _X, _X) $ \ x ->
      (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_P // x) 0
    xs' <- chkPrint (List _X) xs pScope
    return $ "[" ++ _P' ++ " | (" ++ v ++ " : " ++ _X' ++ ") <- " ++ xs' ++ "]"
  Thinning _X ga de -> do
    _X' <- chkPrint Ty _X 0
    ga' <- chkPrint (List _X) ga pScope
    de' <- chkPrint (List _X) de pScope
    return . paren p pArg $ concat [ga', " <[", _X', "]= ", de']
  e :-: Idapter -> fst <$> printSyn e p
  _X -> return $ "(" ++ show _X ++ ")"
chkPrint Atom a p = case a of
  A s -> return ("'" ++ s)
  e :-: Idapter -> fst <$> printSyn e p
chkPrint (Enum as) x p = tryATag as x >>= \case
  Just (s, n) -> return ("'" ++ s ++ if n == 0 then "" else "^" ++ show n)
  Nothing -> notATag 0 x p
chkPrint _T@(Pi _ _) f p = case f of
    Lam _ -> paren p pArg <$> lams "" _T f
    e :-: Idapter -> fst <$> printSyn e p
    _ -> return $ "(" ++ show f ++ ")"
  where
    lams args (Pi _S _T) (Lam t) = fresh (nomo _S, _S) $ \ x -> do
      (v, _) <- printSyn x 0
      lams (args ++ v ++ " ") (_T // x) (t // x)
    lams args _X x = do
      body <- chkPrint _X x 0
      return . concat $ ["\\ ", args, "-> ", body]
chkPrint (Sg _S _T) (s :& t) p = do
  s' <- chkPrint _S s pElt
  _T <- weakChkEval (Ty, _T // (s ::: _S))
  t' <- chkPrint _T t pCdr
  return . paren p pElt $ concat [s', ", ", t']
chkPrint One _ _ = return "<>"
chkPrint Nat n p = either show (paren p pArg) <$> munch n where
  munch :: ChkTm -> TCM (Either Int String)
  munch Nil = return $ Left 0
  munch (Single _) = return $ Left 1
  munch (x :++: y) = do
    x <- munch x
    y <- munch y
    case (x, y) of
      (Left x, Left y) -> return . Left $ x + y
      _ -> return . Right $ concat
        [either show id x, "+", either show id y]
  munch (E e) = (Right . fst) <$> printSyn e pArg
  munch (e :-: _) = do
    (s, _) <- printSyn e pArg
    return . Right $ concat ["|", s, "|"]
  munch x = return . Right $ show x
chkPrint (List _X) xs p = blat <$> munch xs where
  munch :: ChkTm -> TCM (String, Bool, String)
  munch Nil = return ("", False, "")
  munch (Single x) = (\ s -> (s, False, "")) <$> chkPrint _X x pElt
  munch (xs :++: ys) = glom <$> munch xs <*> munch ys
  munch (E e) = (\ (s, _) -> ("", False, s)) <$> printSyn e pArg
  munch (e :-: List f) = printSyn e pArg >>= \case
    (s, List _S) -> do
      f <- chkPrint (Pi _S _X) f pArg
      return $ ("", True, concat ["List ", f, " ", s])
  munch (e :-: Hom f) = printSyn e pArg >>= \case
    (s, List _S) -> do
      f <- chkPrint (Pi _S (List _X)) f pArg
      return $ ("", True, concat [f , " =<< ", s])
  munch x = return $ ("", True, show x)
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " ++ " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " ++ ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " ++ [", ys, "] ++ ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] ++ ", ys]
chkPrint (AllT _X _Q xs) qs p = (blat . snd) <$> munch xs qs where
  munch :: ChkTm -> ChkTm -> TCM (ChkTm, (String, Bool, String))
  munch xs Nil = return (xs, ("", False, ""))
  munch xs (Single q) = do
    xs <- weakChkEval (List _X, xs)
    case consView xs of
      Cons x xs -> (\ s -> (xs, (s, False, ""))) <$> chkPrint (_Q // (x ::: _X)) q pElt
  munch xs (qs :++: rs) = do
    (xs, pqs) <- munch xs qs
    (xs, prs) <- munch xs rs
    return (xs, glom pqs prs)
  munch xs (e :-: Idapter) = printSyn e pArg >>= \case
    (e, AllT _X' _P' xs') -> do
      leftovers <- unprefix _X xs xs'
      return (leftovers, (e, False, ""))
  munch xs (e :-:  AllT f g th) = printSyn e pArg >>= \case
    (s, AllT _W _R ws) -> do
    -- f : _W -> _X
    -- g : (w : _W) -> _Q (f w) -> R w
    -- th : Thinning _X ws' ws
    ws <- weakChkEval (List _W, ws)
    (ws', th) <- weakChkThinning _W th ws
    (_, xs'') <- unmapprefix _X f _W xs ws'

    g <- chkPrint (Pi _W (Pi (_Q // ((f ::: Pi _W _X) :$ E (V 0))) (_R <^> o' mempty))) g pArg
    f <- chkPrint (Pi _W _X) f pArg
    th <- chkPrint (Thinning _W ws' ws) th pArg

    return (xs'', ("", True, concat ["All ", f, " ", g, " ", th, " ", s]))
  munch xs qs = return $ (xs, ("", True, show qs))
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " ++ " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " ++ ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " ++ [", ys, "] ++ ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] ++ ", ys]
chkPrint (FAb _X) xs p = blat <$> munch xs True where
  munch :: ChkTm -> Bool -> TCM (String, Bool, String)
  munch FOne _ = return ("", False, "")
  munch (Eta x) b = (\ s -> (s ++ (if b then "" else "^"), False, "")) <$> chkPrint _X x pElt
  munch (Inv xs) b = munch xs (not b)
  munch (xs :.: ys) b = glom <$> munch xs b <*> munch ys b
  munch (E e) b = (\ (s, _) -> ("", False, if b then s else "(" ++ s ++ ")^")) <$> printSyn e pArg
{-
  munch (e :-: List f) = do
    (s, _S) <- printSyn e pArg
    f <- chkPrint (Pi _S (List _X)) f pArg
    return $ ("", True, concat ["List ", f, " ", s])
-}
  munch x b = return $ ("", True, if b then show x else "(" ++ show x ++ ")^")
  brk s = concat ["[", s, "]"]
  glom ("", _, "") ys = ys
  glom xs ("", _, "") = xs
  glom (xs, _, "") ("", b, ys) = (xs, b, ys)
  glom (xs, _, "") (ys, b, zs) = (xs ++ ", " ++ ys, b, zs)
  glom ("", _, xs) ("", _, zs) = ("", True, xs ++ " * " ++ zs)
  glom (ws, _, xs) ("", _, zs) = (ws, True, concat [xs, " * ", zs])
  glom (ws, _, xs) (ys, _, zs) = (ws, True, concat [xs, " * [", ys, "] * ", zs])
  blat (xs, _, "") = "[" ++ xs ++ "]"
  blat ("", b, ys) = (if b then paren p pArg else id) ys
  blat (xs, _ ,  ys) = paren p pArg $ concat ["[", xs, "] * ", ys]
chkPrint (Thinning _X ga de) th p = munch th where
  munch :: ChkTm -> TCM String
  munch Nil = return $ "."
  munch Th0 = return $ "0.."
  munch Th1 = return $ "1.."
  munch (Cons (A a) th) = (a ++) <$> munch th
  munch (ThSemi th ph) = do
    th <- munch th
    ph <- munch ph
    return $ concat ["(",th,";",ph,")"]
  munch (E e) = fst <$> printSyn e pArg
  munch x@(e :-: List f) = do
    (e, src) <- printSyn e pArg
    case src of
      Thinning _W _ _ -> do
        f <- chkPrint (Pi _W _X) f pArg
        return $ concat ["(List ", f, " ", e, ")"]
      _ -> return $ show x
  munch x = return $ show x
chkPrint _ (E e) p = fst <$> printSyn e p
chkPrint _ t _ = return $ "(" ++ show t ++ ")"

printSyn :: SynTm -> Int -> TCM (String, ChkTm)
printSyn (P x (Hide t)) _ = (, t) <$> pNom x
printSyn (e :$ s) p = do
  (e', _T) <- printSyn e pTarg
  case _T of
    Pi _S _T -> do
      _S <- weakChkEval (Ty, _S)
      s' <- chkPrint _S s pArg
      _T <- weakChkEval (Ty, _T // (s ::: _S))
      return . (, _T) . paren p (pTarg + 1) $ concat
        [e', " ", s']
    Sg _S _T -> case s of
        Fst -> return (paren p (pTarg + 1) (e' ++ " -fst"), _S)
        Snd -> do
          _T <- weakChkEval (Ty, _T // (e :$ Fst))
          return (paren p (pTarg + 1) (e' ++ " -snd"), _S)
        _ -> return . (, _T) . paren p (pTarg + 1) $ concat
          [e', " (", show s, ")"]
    List _X -> case s of
      AllP _P _Acc -> do
        (p', _P') <- fresh (nomo _X, _X) $ \ x ->
                     (,) <$> (fst <$> printSyn x 0) <*> chkPrint Ty (_P // x) 0
        acc <- case _Acc of
          One -> return ""
          _ -> ("; " ++) <$> chkPrint Ty _Acc 0
        let out = "[" ++ _P' ++ " | " ++ p' ++ " <- " ++ e' ++ acc ++ "]"
        return (out , Ty)
      ListElim _P n c -> do
        fresh ("fun", Pi (List _X) _P) $ \ fun -> do
          (funh, _) <- printSyn fun 0
          funTy <- chkPrint Ty (Pi (List _X) _P) 0
          (funNl, _N) <- printSyn (fun :$ Nil) 0
          _N <- weakChkEval (Ty, _N)
          funNr <- chkPrint _N n 0
          cq <- fresh (nomo _X, _X) $ \ x ->
                fresh (nomo (List _X), List _X) $ \ xs -> do
            (funCl, _C) <- printSyn (fun :$ Cons (E x) (E xs)) 0
            _C <- weakChkEval (Ty, _C)
            funCr <- chkPrint _C (c // (fun :$ E xs) // xs // x) 0
            return $ concat [funCl, " = ", funCr]
          (body, _T) <- printSyn (fun :$ E e) pTarg
          _T <- weakChkEval (Ty, _T)
          return . (, _T) . paren p pTarg $ concat
            [ "let ", funh, " : ", funTy, "; "
            , funNl, " = ", funNr, "; "
            , cq, " in " , body
            ]
      _ -> return . (, _T) . paren p (pTarg + 1) $ concat
        [e', " (", show s, ")"]
    _ -> return . (, _T) . paren p (pTarg + 1) $ concat
      [e', " (", show s, ")"]
printSyn e p = do
  (_, t) <- weakEvalSyn e
  return $ ("(" ++ show e ++ ")", t)

tryATag :: ChkTm -> ChkTm -> TCM (Maybe (String, Int))
tryATag as Z = (consView <$> weakChkEval (List Atom, as)) >>= \case
  Cons a _ -> weakChkEval (Atom, a) >>= \case
    A s -> return (Just (s, 0))
    _   -> return Nothing
  _ -> fail ("out of bounds as = " ++ show as)
tryATag as (S x) = (consView <$> weakChkEval (List Atom, as)) >>= \case
  Cons a as -> weakChkEval (Atom, a) >>= \case
    A a -> tryATag as x >>= \case
      Just (s, n) -> return (Just (s, if a == s then n+1 else n))
      Nothing -> return Nothing
    _   -> return Nothing
  _ -> fail ("out of bounds as = " ++ show as ++ " x = " ++ show x)
tryATag _ _ = return Nothing

notATag :: Int -> ChkTm -> Int -> TCM String
notATag acc Z p = return (show acc)
notATag acc (S x) p = notATag (acc+1) x p
notATag acc (E e) p = do
  (s, _) <- printSyn e (if acc == 0 then p else pCdr)
  if acc == 0 then return s else return (paren p pArg (show acc ++ " + " ++ s))

paren :: Int -> Int -> String -> String
paren p l x = if p >= l then concat ["(", x, ")"] else x

pArg, pTarg, pElt, pCdr, pScope :: Int
pArg = 60
pTarg = 50
pElt = 40
pCdr = 30
pScope = 10

nomo :: ChkTm -> String
nomo Ty = "X"
nomo (Pi _ _T) = if toTy _T then "F" else "f" where
  toTy Ty = True
  toTy (Pi _ _T) = toTy _T
  toTy (Sg _S _T) = toTy _S || toTy _T
  toTy _ = False
nomo (Sg _S _T) = nomo _S ++ nomo _T
nomo (List One) = "n"
nomo (List _X) = nomo _X ++ "s"
nomo (Thinning _ _ _) = "th"
nomo _ = "x"

-- testing

idTy = Pi Ty (Pi (E (V 0)) (E (V 1)))
idTm = Lam (Lam (E (V 0)))

fam :: ChkTm -> ChkTm
fam x = Sg Ty (Pi (E (V 0)) (x <^> o' (o' mempty)))

famTytm = idTy :& Lam idTy

pairTy = Sg Ty Ty

revTy = ListElim
  (Pi (List Ty) (List Ty))
  (Lam (E (V 0)))
  (Lam (E (V 1 :$ Cons (E (V 3)) (E (V 0)))))

myTys = Cons Ty (Cons (Pi Ty Ty) (Cons (Sg Ty Ty) Nil)) ::: List Ty

funTy = Pi Nat (Pi (Thinning One Nil (E (V 0))) (Thinning One Nil (E (V 1))))

list0 = Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))

th0 = Cons Th0 (ThSemi (E $ P [("b", 0)] (Hide $ Thinning Nat list0 list0)) (E $ P [("b", 1)] (Hide $ Thinning Nat list0 list0)))
th1 = ThSemi (E $ P [("b", 2)] (Hide $ Thinning Nat list0 list0)) th0
th1Ty = Thinning Nat list0 (Cons Z list0)

list0' = (list0 ::: List Nat) :-: List (Lam (S (E (V 0))))

swap = Lam $ E (V 0 :$ Snd) :& E (V 0 :$ Fst)

swapswapper = Lam (((V 0 :-: List swap) ::: List (Sg Ty Nat)) :-: List swap) ::: Pi (List (Sg Nat Ty)) (List (Sg Nat Ty))

unitswapper = Lam (V 0 :-: List swap) ::: Pi (List (Sg One One)) (List (Sg One One))

dup = Lam (E (V 0) :& E (V 0))

adaptTh1Ty = Thinning (Sg Nat Nat) ((list0 ::: List Nat) :-: List dup) ((Cons Z list0 ::: List Nat) :-: List dup)

adaptTh1 = ((th1 ::: th1Ty) :-: List dup)
              ::: adaptTh1Ty

revMappedPartlyNeutralList = ((((E (P [("ys", 0)] (Hide (List Ty))) :++: E myTys) ::: List Ty) :-: (List (Lam (Sg (E (V 0)) (E (V 1)))))) ::: List Ty) :$ revTy :$ Nil

myEnum = Enum (Cons (A "a") (Cons (A "c") (Cons (A "c") Nil)))
myEnumNeut = Enum (Cons (A "a") (Cons (E (P [("q", 0)] (Hide Atom))) (Cons (A "c") Nil)))

listABC = (Cons (A "a") (Cons (A "b") (Cons (A "c") Nil)))
listAB = (Cons (A "a") (Cons (A "b") Nil))

predABC = P [("P", 0)] (Hide (Pi (Enum listABC) Ty))

enumAtoms =
  ListElim (List (Enum (E (V 0)))) Nil (Cons Z (V 0 :-: List (Lam $ S (E (V 0)))))

allPabc = (listABC ::: List Atom) :$ enumAtoms :$ AllP (E (predABC :$ E (V 0))) One

allmapfusion = ((xs :-: List (Lam $  S (E (V 0)))) ::: List (Enum listABC)) :$ AllP (E (predABC :$ E (V 0))) One
  where
    xs = P [("xs", 0)] (Hide (List (Enum (Cons (A "b") (Cons (A "c") Nil)))))

enumToNat = (Lam (E (V 0 :$ EnumElim Nat (1 :& 2 :& 3 :& Void)))) ::: Pi (Enum listABC) Nat

myEnumToNat = enumToNat :$ A "a"

myG = FAb (Enum listABC)

myGelt = Inv (Eta (A "b")) :.: E (P [("x", 0)] (Hide myG)) :.: Eta (A "a") :.: Inv (E (P [("x", 0)] (Hide myG)))

stuttering = (Lam $ (V 0 :-: Hom (Lam $ (Single (E (V 0)) :++: Single (E (V 0)))))) ::: Pi (List Atom) (List (Atom))

idObfuscated = (Lam $ (V 0 :-: Hom (Lam $ Single ((E (V 0))) :++: Nil))) ::: Pi (List Atom) (List Atom)

youarehereTy = Pi Ty (Pi (List (E (V 0))) (AllT (E (V 1)) (Thinning (E (V 2)) (Single (E (V 0))) (E (V 1))) (E (V 0))))

youarehere = Lam {-X-} . Lam {-xs-} . E $ V {-xs-} 0 :$
  ListElim ({-xs'.-} AllT (E (V {-X-} 2)) ({-x.-}Thinning (E (V {-X-} 3)) (Single (E (V {-x-} 0))) (E (V {-xs'-} 1))) (E (V {-xs'-} 0)))
           Nil
           ({-x, xs', ih.-} Cons (Cons Th1 Th0) (V {-ih-} 0 :-: AllT (Lam {-y-} (E (V {-y-} 0))) (Lam {-y-} . Lam {-th-} $ Cons Th0 (E (V {-th-} 0))) Th1))

youarehereApplied = (youarehere ::: youarehereTy) :$ Atom :$ listABC
