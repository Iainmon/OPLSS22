

import Data.Set (Set)
import qualified Data.Set as Set

data RS a = RS { axioms :: a -> Bool
               , rules :: [Set a -> Maybe a]
               }


inf :: Ord a => RS a -> Set a -> Set a
inf rs g = Set.unions $ Set.map ded subs
  where subs   = Set.powerSet g
        ded g' = Set.fromList $ map unjust $ filter (not . null) [i g' | i <- rules rs]
        unjust (Just x) = x

infn :: Ord a => Int -> RS a -> Set a -> Set a
infn 0 rs g = g
infn n rs g = inf rs (infn (n-1) rs g)

infs :: Ord a => RS a -> Set a -> [a]
infs rs g | inf rs g `Set.isSubsetOf` g = Set.toList g -- concatMap (\n -> Set.toList $ infn n rs g) [0..]
          | otherwise = infs rs (Set.union g (inf rs g))
data F2 a = Lit a | And (F2 a) (F2 a) | Imp (F2 a) (F2 a) deriving (Eq,Ord)

instance Show a => Show (F2 a) where
  show (Lit a) = show a
  show (And a b) = show a ++ " & " ++ show b
  show (Imp a b) = show a ++ " -> " ++ show b

stripImp :: F2 a -> Maybe ([a],a)
stripImp (Imp p (Lit q)) = strip p >>= \ps -> return (ps,q)
  where strip (Lit a)   = return [a]
        strip (And a b) = do { as <- strip a; bs <- strip b; return (as ++ bs)}
        strip _ = Nothing

s2rule1 g | [Imp p q,p'] <- Set.toList g, p == p' = Just q
          | [p',Imp p q] <- Set.toList g, p == p' = Just q
          | otherwise = Nothing
s2rule2 g | [Imp p q,Imp q' r] <- Set.toList g, q == q' = Just (Imp p r)
          | [Imp q' r,Imp p q] <- Set.toList g, q == q' = Just (Imp p r)
          | otherwise = Nothing
          
embed :: Ord a => RS a -> RS (F2 a)
embed rs = RS { axioms=axioms2, rules=rules2 }
  where axioms2 (Lit a) = axioms rs a
        axioms2 imp@(Imp p q) | Just (ps,q') <- stripImp imp = Set.member q' (inf rs (Set.fromList ps))
        axioms2 _       = False
        rules2 = [s2rule1]


data JEven = Even Int deriving (Show,Eq,Ord)

evenAxioms (Even 0) = True
evenAxioms _ = False

evenRule1 premises | [Even n] <- Set.toList premises = return $ Even (n + 2)
                   | otherwise = Nothing


evenSys = RS { axioms=evenAxioms, rules=[evenRule1] }

evenSys' = embed evenSys