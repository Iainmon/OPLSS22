{-# LANGUAGE InstanceSigs #-}

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
(<|>) = alt -- (+++) -- alt

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


-- Generates a parser for terminal symbols
terminal :: Eq a => a -> Parser a (ParseTree a)
terminal a = sat (==a) >>= return . Sym

-- Generates a parser for any derivation of a non-terminal
nonTerminal :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
nonTerminal g nt = choice (productions g nt) >>= return . Rule nt

-- Generates a parser for a production rule
production :: Eq a => CFG a -> Production a -> Parser a [ParseTree a]
production g = sequence . map (symbol g)

-- Generates a parser for each production rule of a non-terminal
productions :: Eq a => CFG a -> NT -> [Parser a [ParseTree a]]
productions g = map (production g) . flip prods g

-- Generates a parser for a terminal or non-terminal symbol
symbol :: Eq a => CFG a -> Either NT a -> Parser a (ParseTree a)
symbol g (Left nt) = nonTerminal g nt 
symbol _ (Right a) = terminal a

-- Generates a parser for rules of a grammar and a non-terminal
makeParser :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
makeParser = nonTerminal


-- The type of a grammar and a specified non-terminal
type Grammar a = (CFG a,NT)

-- Generate a parser, given a pair of a grammar and initial non-terminal
grammarParser :: Eq a => Grammar a -> Parser a (ParseTree a)
grammarParser (g,nt) = makeParser g nt


parseTrees :: Parser c (ParseTree a) -> [c] -> [ParseTree a]
parseTrees p w = map fst $ filter (null . snd) $ p <<< w


derivations :: Eq a => Grammar a -> [a] -> [ParseTree a]
derivations = parseTrees . grammarParser



consParser :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
consParser = makeParser

consGrammar :: [(NT,String)] -> CFG Char
consGrammar g = Map.fromListWith (++) [(nt,return $ map f prd) | (nt,prd) <- g]
  where f c | c `elem` ['A'..'Z'] = Left  c
            | otherwise           = Right c

g1 = consGrammar [('S',"aSb"),('S',"ab"),('S',"T"),('T',"aSb")]
g1P = makeParser g1 'S'

sRule1 = [Right 'a',Left 'S',Left 'b']
sRule2 = [Right 'a',Right 'b']

g1SRuleP = production g1 sRule2
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
