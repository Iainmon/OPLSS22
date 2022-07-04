


{-

M : A    N : B
--------------
⟨M, N⟩ : A * B


M : A * B
---------
fst M : A


N : A * B
---------
snd N : B


fst ⟨M, N⟩ ---> M
snd ⟨M, N⟩ ---> N



------x
x : A
  .
  .
  .
M : B
------------
λx.M : A ⊃ B


M : A ⊃ B    N : A
------------------
M N : B

(λx.M) N ---> M[x := N]



M : A
-------------
inl M : A + B


N : B
-------------
inr N : A + B



             -----x    -----y
             x : A     y : B
               .         .
               .         .
               .         .
M : A + B    N : C     O : C
----------------------------------------
case M of { inl x => N | inr y => O } : C

case (inl M) { inl x => N | inr y => P } ---> N[x := M]
case (inr M) { inl x => N | inr y => P } ---> P[y := M]


-}

import Data.List (intercalate)

data RoseTree a = Branch a [RoseTree a] 

instance Show a => Show (RoseTree a) where
  show (Branch a tr) = "{ " ++ intercalate "  ;  " (map show tr) ++ " } | " ++ show a

leaf a = Branch a []

type Name = String

data Proof
  = Var Name
  | Fst Proof
  | Snd Proof
  | InL Proof
  | InR Proof
  | Pair [Proof]
  | Abs Name Proof
  | App Proof Proof
  | Case Proof [(Proof,Proof)]
  deriving (Show,Eq)

data Prop
  = Lit Name
  | Conj Prop Prop
  | Disj Prop Prop
  | Impl Prop Prop
  deriving Eq

instance Show Prop where
  show (Lit x) = x
  show (Conj a b) = show a ++ " ∧ " ++ show b
  show (Disj a b) = show a ++ " ∨ " ++ show b
  show (Impl a b) = show a ++ " ⊃ " ++ show b

hole = Lit "?"

type Judge = (Proof,Prop)

(.:.) a b = (a,b)



type Deduction = RoseTree Judge


type DeductionStep = Judge -> [Deduction]

stepper :: DeductionStep
stepper jdg@(term,type')
  = stepper' term type'
  where stepper' :: Proof -> Prop -> [Deduction]
        stepper' (Pair [a,b]) (Conj at bt) 
          = return $ Branch jdg [leaf (a,at),leaf (b,bt)]
        stepper' (Fst m) a
          = return $ Branch jdg [leaf (m,Conj a hole)]



data Sequent jdg = Sq [jdg] jdg

instance Show jdg => Show (Sequent jdg) where
  show (Sq hypo conc) = intercalate "," (map show hypo) ++ " ⊢ " ++ show conc

class Eq jdg => RuleSystem jdg where
  premises' :: Sequent jdg -> [[Sequent jdg]]
  check :: [jdg] -> jdg -> Bool

instance RuleSystem Prop where
  premises' (Sq hypos (Lit x)) = [[Sq hypos (Lit x)]] ++ [[Sq ((Impl y (Lit x)):hypos) (Lit x)] | y <- hypos]
  premises' (Sq hypos (Conj a b)) = return $ map (Sq hypos) [a,b]
  premises' (Sq hypos (Disj a b)) = [[Sq hypos a], [Sq hypos b]]
  premises' (Sq hypos (Impl a b)) = return $ [Sq (a:hypos) b]

  check hypos conc =  conc `elem` hypos -- || or [and [check h c | (Sq h c) <- prems] | prems <- premises' (Sq hypos conc)]


-- ghci> premises' (Sq [] (Conj (Lit "A") (Lit "B")))
-- ghci> derives (Sq (map Lit ["A","B"]) (Conj (Lit "A") (Lit "B")))

derives :: (Eq jdg,RuleSystem jdg) => Sequent jdg -> Bool
derives (Sq hypos conc) | check hypos conc = True
                        | otherwise = or [and (map derives prems) | prems <- premises' (Sq hypos conc)]


derivation :: (Eq jdg,RuleSystem jdg) => Sequent jdg -> RoseTree (Sequent jdg)
derivation sq@(Sq hypos conc) | check hypos conc = Branch sq []
                              | derives sq       = Branch sq $ concat [ map derivation prems | prems <- premises' sq, and (map derives prems)]
                              | otherwise        = Branch sq []


testSq1 = Sq [Lit "A",Lit "B"] (Conj (Lit "A") (Lit "B"))
testSq2 = Sq [Lit "B"] (Impl (Lit "A") (Lit "B"))
testSq3 = Sq [(Impl (Conj (Lit "A") (Lit "B")) (Lit "C")), (Lit "A"), (Lit "B")] (Lit "C")
testSq4 = Sq [Lit "A",Lit "B"] (Disj (Lit "A") (Lit "B"))



type Context judgement = [judgement]

class Eq jdg => SequentCalculus jdg where
  premises :: Context jdg -> jdg -> [[Sequent jdg]]

instance SequentCalculus Prop where
  premises hypos (Lit x) = [[Sq hypos (Lit x)]]
  premises hypos (Conj a b) = [[Sq hypos a, Sq hypos b]]
  premises hypos (Disj a b) = [[Sq hypos a],[Sq hypos b]]

instance Functor RoseTree where
  fmap f (Branch x trs) = Branch (f x) (map (fmap f) trs)

instance Applicative RoseTree where
  pure x = Branch x []
  (<*>) (Branch f fs) (Branch a as) = Branch (f a) [f' <*> a' | f' <- fs, a' <- as]

instance Monad RoseTree where
  return = pure
  (>>=) (Branch x trs) f = let Branch y trs' = f x in Branch y ((map (>>=f) trs) ++ trs')


expand :: SequentCalculus jdg => Sequent jdg -> [RoseTree (Sequent jdg)]
expand (Sq hypos conc) = do 
                            prems <- premises hypos conc
                            return $ Branch (Sq hypos conc) (map return prems)

-- testSq1 = Sq [Lit "A",Lit "B"] (Conj (Lit "A") (Lit "B"))
-- testSq4 = Sq [Lit "A",Lit "B"] (Disj (Lit "A") (Lit "B"))

