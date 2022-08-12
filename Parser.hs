{-# LANGUAGE InstanceSigs #-}

import Debug.Trace (traceShowId)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.List (intercalate)

-- Parser from strings of `c` to things of type `a`
data Parser c a = P ([c] -> [(a,[c])])

papply :: Parser c a -> [c] -> [(a,[c])]
papply (P p) s = p s

(<<<) = papply

instance Functor (Parser c) where
  fmap f (P p) = P $ \s-> map (\(x,s) -> (f x,s)) (p s)

instance Applicative (Parser c) where
  pure x = P $ \s->[(x,s)]
  (<*>) :: Parser c (a -> b) -> Parser c a -> Parser c b
  P f <*> p = P $ \s -> concat [papply (fmap g p) r | (g,r) <- f s]

instance Monad (Parser c) where
  return :: a -> Parser c a
  return x = P (\s->[(x,s)])
  (>>=) :: Parser c a -> (a -> Parser c b) -> Parser c b
  P p >>= f = P (\s-> concat [papply (f v) r | (v,r) <- p s])

item :: Parser a a
item = P (\s -> if null s then [] else [(head s,tail s)])

zero :: Parser c a
zero = P (\s -> [])

sat :: (a -> Bool) -> Parser a a
sat p = do { c <- item; if p c then return c else zero }

alt :: Parser c a -> Parser c a -> Parser c a
alt (P p) (P q) = P (\s -> p s ++ q s)

(+++) :: Parser c a -> Parser c a -> Parser c a
p +++ q = first (p `alt` q)
(<|>) = (+++)

first :: Parser c a -> Parser c a
first (P p) = P (\s -> case p s of [] -> []; (x:xs) -> [x])

char :: Char -> Parser Char Char
char c = sat (==c)

seq :: [Parser c a] -> Parser c [a]
seq = sequence 

choice :: [Parser c a] -> Parser c a
choice = foldr (<|>) zero

-- couple :: Parser c a -> Parser c b -> (a -> b -> d) -> Parser c d

-- newtype NT = NT String
-- data CFG' a = G [(NT,[Either NT a])] 

-- Nonterminals ['A'..'Z']
type NT = Char 

-- Production, string of terminals of type `a` or nonterminals
type Production a = [Either NT a]

-- Context Free Grammar over alphabet of type `a`
type CFG a = Map NT [Production a]

prods :: NT -> CFG a -> [Production a]
prods = Map.findWithDefault []


data ParseTree a = Rule NT [ParseTree a] | Sym a deriving (Show)


symbol :: Eq a => a -> Parser a (ParseTree a)
symbol a = sat (==a) >>= return . Sym


parseProd :: Eq a => CFG a -> Production a -> Parser a [(ParseTree a)]
parseProd g r = sequence compiled
  where compiled = map compileP r
        compileP (Left nt) = consParser g nt
        compileP (Right a) = symbol a

validRule :: Eq a => CFG a -> NT -> Production a -> Bool
validRule g nt r = r `elem` prods nt g

parseRule :: Eq a => CFG a -> NT -> Production a -> Parser a (ParseTree a)
parseRule g s r = do leaves <- parseProd g r
                     return $ Rule s leaves
-- parseRule g s r = do chlds <- parseProd g r
--                      let roots = map roots chlds in
--                      if (s,roots) `elem` Map.toList g then return $ Rule s leaves
--                                                       else void


consParser :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
consParser g s = choice [parseRule g s prd | prd <- prods s g]

consGrammar :: [(NT,String)] -> CFG Char
consGrammar g = Map.fromListWith (++) [(nt,return $ map f prd) | (nt,prd) <- g]
  where f c | c `elem` ['A'..'Z'] = Left  c
            | otherwise           = Right c

g1 = consGrammar [('S',"aSb"),('S',"ab")]
g1P = consParser g1 'S'

sRule1 = [Right 'a',Left 'S',Left 'b']
sRule2 = [Right 'a',Right 'b']

g1SRuleP = parseProd g1 sRule2
{--
ghci> parseProd g1 sRule2 <<< "ab"
[([Sym 'a',Sym 'b'],"")]
--}

{--
ghci> prodRule g1 'S' sRule2 <<< "ab"
[(Rule 'S' [Sym 'a',Sym 'b'],"")]
--}

(-->) :: NT -> [a] -> [(NT,a)]
nt --> []     = []
nt --> (a:as) = (nt,a) : (nt --> as)


-- palG = consGrammar [ 'S' --> [ c:'S':c:"" | c <- ['a'..'z']] ]
-- palP = consParser palG

ordLeaves :: ParseTree a -> [a]
ordLeaves (Sym a)           = [a]
ordLeaves (Rule _ children) = concatMap ordLeaves children

pstr = fst . head $ consParser g1 'S' <<< "aabb"

-- ppCFG :: Show a => CFG a -> String
-- ppCFG g = 
--   where ppRule r = (r:"") ++ " -> " ++ intercalate " | " (map ppProd )

-- Lazy/infinite representation
-- data Gram a = NonTer [Either (Gram a) a]

sequence' :: Monad m => [m a] -> m [a]
-- sequence' []     = return []
sequence' (m:ms) = do a <- m
                      as <- sequence' ms
                      return (a:as)

g3 = consGrammar [('S',"a"),('S',"Sa")]
g3P = consParser g3 'S'
