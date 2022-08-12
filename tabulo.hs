import Data.List (nub, union)


type Name = String

data Formula
  = Var Name
  | Not Formula
  | And Formula Formula
  | Or  Formula Formula
  deriving (Show,Eq,Ord)

impl a b = (Not a) `Or` b
iff a b = impl a b `And` impl b a


type Resolve = (Bool,Name)

consistent' :: Resolve -> Resolve -> Bool
consistent' (b1,n1) (b2,n2) = b1 == b2 || n1 /= n2

(-|-) :: Resolve -> Resolve -> Bool
(-|-) = consistent'

consistent :: [Resolve] -> Bool
consistent []     = False
consistent [_]    = True
consistent (x:xs) = all (-|-x) xs && consistent xs


-- data Tableau = RoseTree 

solve :: Formula -> [[Resolve]]
solve (Var n)       = [[(True,n)]]
solve (Not (Var n)) = [[(False,n)]]
solve (Or a b)      = clear $ union (solve a) (solve b)
solve (And a b)     = clear $ concat [[rs] | r1 <- solve a, r2 <- solve b, let rs = union r1 r2, consistent rs] -- clear $ solve a >>= (\r1 -> solve b >>= return . union r1)-- [union r1 r2 | r1 <- solve a, r2 <- solve b]
solve a = clear $ solve (normalize a)

clear :: Eq a => [[a]] -> [[a]]
clear = nub . map nub . nub

normalize :: Formula -> Formula
normalize (Var n)       = Var n
normalize (Not (Var n)) = Not $ Var n
normalize (Not (Not e)) = normalize e
normalize (Not (And a b)) = normalize (Or (Not a) (Not b))
normalize (Not (Or a b))  = normalize (And (Not a) (Not b))
normalize (Or a b)  = normalize a `Or` normalize b
normalize (And a b) = normalize a `And` normalize b

sat :: Formula -> [[Resolve]]
sat = solve . normalize

satisfy :: Formula -> Bool
satisfy = any (/=[]) . solve . normalize

validity :: Formula -> Bool
validity = not . satisfy . Not

entails :: [Formula] -> Formula -> Bool
entails ps c = not . satisfy $ foldr (And . normalize) (Not c) ps

(|=) :: [Formula] -> Formula -> Bool
(|=) = entails

f1 = And (Or (Var "A") (Not (Var "B"))) (And (Var "B") (Not (Var "A")))
f2 = And (And (Or (Var "A") (Not (Var "B"))) (Var "B")) (Not (Var "A"))
cn = Var "A"

