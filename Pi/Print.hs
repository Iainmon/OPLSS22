{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE GADTs, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for Pi.
--   Generated by the BNF converter.

module Pi.Print where

import qualified Pi.Abs
import Data.Char

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    [";"]        -> showChar ';'
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i     = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Pi.Abs.Ident where
  prt _ (Pi.Abs.Ident i) = doc $ showString $ i

instance Print Pi.Abs.Expr where
  prt i e = case e of
    Pi.Abs.E_Var id -> prPrec i 0 (concatD [prt 0 id])
    Pi.Abs.E_Abs id expr -> prPrec i 0 (concatD [doc (showString "\\"), prt 0 id, doc (showString "."), prt 0 expr])
    Pi.Abs.E_App expr1 expr2 -> prPrec i 0 (concatD [prt 0 expr1, prt 0 expr2])
    Pi.Abs.E_Pi id expr1 expr2 -> prPrec i 0 (concatD [doc (showString "("), prt 0 id, doc (showString ":"), prt 0 expr1, doc (showString ")"), doc (showString "->"), prt 0 expr2])
    Pi.Abs.E_Type -> prPrec i 0 (concatD [doc (showString "Type")])
    Pi.Abs.E_Anno expr1 expr2 -> prPrec i 0 (concatD [doc (showString "("), prt 0 expr1, doc (showString ":"), prt 0 expr2, doc (showString ")")])
