{-# LANGUAGE InstanceSigs #-}

import Data.Map (Map)
import qualified Data.Map as Map

import Data.List (intercalate,find)
import Data.Maybe (maybeToList)

import Debug.Trace (traceStack,traceShowId)

-- Parser from strings of `c` to things of type `a`
data Parser c a = P ([c] -> [(a,[c])])

parse :: Parser c a -> [c] -> [(a,[c])]
parse (P p) = p

(<<<) = parse

instance Functor (Parser c) where
  fmap f (P p) = P $ \s-> map (\(x,s) -> (f x,s)) (p s)

instance Applicative (Parser c) where
  pure x = P $ \s  -> [(x,s)]
  (<*>) :: Parser c (a -> b) -> Parser c a -> Parser c b
  P f <*> p = P $ \s -> concat [parse (fmap g p) r | (g,r) <- f s]

instance Monad (Parser c) where
  return :: a -> Parser c a
  return x = P (\s->[(x,s)])
  (>>=) :: Parser c a -> (a -> Parser c b) -> Parser c b
  P p >>= f = P (\s-> concat [parse (f v) r | (v,r) <- p s])

item :: Parser a a
item = P (\s -> if null s then [] else [(head s,tail s)])

zero :: Parser c a
zero = P (\s -> [])

sat :: (a -> Bool) -> Parser a a
sat p = do { c <- item; if p c then return c else zero }

alt :: Parser c a -> Parser c a -> Parser c a
alt p q = P (\s -> parse p s ++ parse q s)

(+++) :: Parser c a -> Parser c a -> Parser c a
p +++ q = first (p `alt` q)
-- (<|>) = (+++) -- alt

(<|>) :: Parser c a -> Parser c a -> Parser c a
-- p <|> q = alt p q -- p +++ q
p <|> q = alt p q -- p +++ q



finished :: Parser c a -> Parser c a
finished p = P (\s -> maybeToList $ find (null . snd) (p <<< s))

first :: Parser c a -> Parser c a
first p = P (\s -> case p <<< s of [] -> []; (x:xs) -> [x])

char :: Char -> Parser Char Char
char c = sat (==c)

seq :: [Parser c a] -> Parser c [a]
seq = sequence 

choice :: [Parser c a] -> Parser c a
choice = foldr (<|>) zero

-- Nonterminals ['A'..'Z']
type NT = Char 

-- Production, string of terminals of type `a` or nonterminals
type Production a = [Either NT a]

-- Context Free Grammar over alphabet of type `a`
type CFG a = Map NT [Production a]

prods :: NT -> CFG a -> [Production a]
prods = Map.findWithDefault []

rotate :: [a] -> [a]
rotate []     = []
rotate (x:xs) = xs ++ [x]

shuffleProds :: NT -> CFG a -> CFG a
shuffleProds = Map.update (return . rotate)


data ParseTree a = Rule NT [ParseTree a] | Sym a deriving (Show)


-- Generates a parser for terminal symbols
terminal :: Eq a => a -> Parser a (ParseTree a)
terminal a = sat (==a) >>= return . Sym

-- Generates a parser for any derivation of a non-terminal
nonTerminal :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
nonTerminal g nt = choice (productions g' nt) >>= return . Rule nt
  where g' = shuffleProds nt g

-- Generates a parser for a production rule
production :: Eq a => CFG a -> Production a -> Parser a [ParseTree a]
production g = mapM (symbol g)
-- production g = sequence . map (symbol g)

-- Generates a parser for each production rule of a non-terminal
productions :: Eq a => CFG a -> NT -> [Parser a [ParseTree a]]
productions g = map (production g) . flip prods g

-- Generates a parser for a terminal or non-terminal symbol
symbol :: Eq a => CFG a -> Either NT a -> Parser a (ParseTree a)
symbol g (Left nt) = nonTerminal (shuffleProds nt g) nt 
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

-- Picks the first derivation that is found
derivations1 :: Eq a => Grammar a -> [a] -> [ParseTree a]
derivations1 = parseTrees . finished . grammarParser


consParser :: Eq a => CFG a -> NT -> Parser a (ParseTree a)
consParser = makeParser


level :: Int -> ParseTree Char -> [Char]
level _ (Sym a)     = [a]
level 0 (Rule nt _) = [nt]
level n (Rule _ cs) = concatMap (level (n-1)) cs

leaves :: ParseTree a -> [a]
leaves (Sym a)     = [a]
leaves (Rule _ cs) = concatMap leaves cs


type Derivation a = [[a]]

derivationList :: ParseTree Char -> Derivation Char
derivationList tr = go $ map (flip level tr) [0..]
  where go (s:ss) | s == leaves tr = [s]
                  | otherwise      = s : go ss


derive :: Grammar Char -> String -> [Derivation Char]
derive g w = map derivationList (derivations g w)

derive1 :: Grammar Char -> String -> [Derivation Char]
derive1 g w = map derivationList (derivations1 g w)

-- derivationList tr = (return . same . root) tr : concatMap derivationList (children tr)


consCFG :: [(NT,String)] -> CFG Char
consCFG g = Map.fromListWith (++) [(nt,return $ map f prd) | (nt,prd) <- g]
  where f c | c `elem` ['A'..'Z'] = Left  c
            | otherwise           = Right c

makeGrammar :: [(NT,String)] -> NT -> Grammar Char
makeGrammar g s = (consCFG g,s)

g = makeGrammar (concat rules) 'E'
  where rules = [ 'E' --> ["N","D","FOF"]
                , 'F' --> ["(E)","E"]
                -- , 'F' --> ["N","D","(E)"]
                , 'O' --> ["+","-","*"," O "]
                , 'N' --> [return c | c <- ['a'..'z']]
                , 'D' --> [show n | n <- [0..9]]
                ]

gas = makeGrammar (concat rules) 'S'
  where rules = [ 'S' --> ["a","SS"] ]

g1 = consCFG [('S',"aSb"),('S',"ab"),('S',"T"),('T',"aSb")]
g1P = makeParser g1 'S'

tr = head $ derivations (g1,'S') "aabb"

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