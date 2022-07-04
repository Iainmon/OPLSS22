
type Name = String

data Expr
  = Var Name
  | Abs Name Expr
  | App Expr Expr
  | Pi (Name,Expr) Expr
  | Type
  | Anno (Expr,Expr)
  deriving Eq

instance Show Expr where
  show (Var x) = x
  show (Abs x a) = "(λ" ++ x ++ "." ++ show a ++ ")"
  show (App a b) = show a ++ " " ++ show b 
  show (Pi ("",Pi (x,a) b) b') = "(" ++ show (Pi (x,a) b) ++ ")" ++ " -> " ++ show b'
  show (Pi ("",a) b) = show a ++ " -> " ++ show b
  show (Pi (x,a) b) = "(" ++ x ++ " : " ++ show a ++ ") -> " ++ show b
  show Type = "Type"
  show (Anno (x,a)) = "(" ++ show x ++ " : " ++ show a ++ ")"

type Context = [(Name,Expr)]

sub :: Expr -> (Expr,Name) -> Expr
sub (Var x) (e,x') | x == x' = e
sub (Abs x a) (e,x') | x /= x' = Abs x (a `sub` (e,x'))
sub (App a b) re = App (a `sub` re) (b `sub` re)
sub (Pi (x,a) b) (e,x') | x /= x' = Pi (x,a `sub` (e,x')) (b `sub` (e,x'))
sub e _ = e

normalForm :: Expr -> Bool
normalForm Type                         = True
normalForm (Var _)                      = True
normalForm (App (Abs _ _) _)            = False
normalForm (App (Anno ((Abs _ _),_)) _) = False
normalForm (Abs _ a)     = normalForm a
normalForm (App a b)     = normalForm a && normalForm b
normalForm (Pi (_,a) b)  = normalForm a && normalForm b
normalForm (Anno (a,at)) = normalForm a && normalForm at


reduce :: Expr -> Expr
reduce e | normalForm e = e
         | otherwise    = reduce (reduce' e)
  where reduce' :: Expr -> Expr
        reduce' (Abs x a)         = Abs x (reduce a)
        reduce' (App (Abs x a) b) = a `sub` (b,x) 
        reduce' (App a b)         = App (reduce a) (reduce b)
        reduce' (Pi (x,a) b)      = Pi (x,reduce a) (reduce b)
        reduce' (Anno (a,at))     = Anno (reduce a, reduce at)
        reduce' e                 = e


infer :: Context -> Expr -> Expr 
infer _ Type = Type
infer g (Var x) | (Just a) <- lookup x g = a
infer g (App a b) | (Pi (x,ta) tb) <- infer g a, check g b ta = tb `sub` (b,x)
infer g (Pi (x,a) b) | check g a Type && check ((x,a):g) b Type = Type -- infer g (Pi (x,a) b) | infer g a == Type && infer ((x,a):g) b == Type = Type
infer g (Anno (a,at)) | check g a at = at
infer g (App a b) | (Pi (x,ta) tb) <- infer g a, not $ check g b ta 
  = error $ "Type Error:     " 
    ++ show (Anno (a,infer g a)) 
    ++ "    but    " 
    ++ show (Anno (b,infer g b)) 
    ++ "    in    " 
    ++ show (App a b)
infer g e = error $ "Cannot infer " ++ show g ++ " ⊢ " ++ show e ++ " : ?"

check :: Context -> Expr -> Expr -> Bool
-- check g (Var x) Type | Nothing <- lookup x g = True -- This makes it easier, but is not correct for the system.
check g (Abs x a) (Pi (x',at) b) = check ((x,at):g) a b && check g at Type
check g a at = infer g a == at


e2e = (Anno (Abs "x" (Var "x"),Pi ("",Var "Bool") (Var "Bool")))

e3 = App e2e (Var "True")
 
e4  = (Abs "x" (Abs "y" (Var "y")))
e4' = (Abs "x" (Abs "y" (Anno (Var "y",Var "x"))))
e4'' = (Abs "x" (Abs "y" (Anno (Var "y",(Anno (Var "x",Type))))))
e4''' = Anno (e4,Pi ("x",Type) (Pi ("",Var "x") (Var "x")))

e5 = App e4''' (Var "Bool")

e6 = App (Abs "x" (Var "x")) (Var "True")

e7g = [("1",Var "Nat"),("2",Var "Nat"),("(+)",Pi ("",Var "Nat") (Pi ("",Var "Nat") (Var "Nat")))]
e7 = App (App (Var "(+)") (Var "1")) (Var "2")


e8g = [("1",Var "Nat"),("True",Var "Bool"),("(+)",Pi ("",Var "Nat") (Pi ("",Var "Nat") (Var "Nat")))]
e8 = App (App (Var "(+)") (Var "1")) (Var "True")


e1e = Abs "x" (Abs "y" (Var "y"))
e1e' = Abs "x" (Anno ((Abs "y" (Var "y")),Pi ("y",(Var "x")) (Var "x")))

e1t = Pi ("x",Type) (Pi ("y",(Var "x")) (Var "x"))

e2e' = (Anno (Abs "x" (Var "x"),Pi ("x",(Anno (Var "Bool",Type))) (Anno (Var "Bool",Type))))

-- e2e = (App (App (Anno (Abs "z" (Anno (Abs "x" (Var "x"),Pi ("x"))),Pi ("z",Type) (Pi ("x",Var "z") (Var "z")))) (Anno (Var "Bool",Type))) (Anno (Var "True",Var "Bool")))

-- tc :: Context -> Expr -> Maybe Expr
-- tc g (Var x) = lookup x g
-- tc g (Abs x a) = 

-- typeJudge :: Context -> Expr -> Expr -> Bool
-- typeJudge g (Var x) t = (x,t) `elem` g
-- typeJudge g (Abs x a) (Pi (x',a) b) | x == x' = typeJudge ((x,a):g) a b && typeJudge g a Type
-- typeJudge g (App )
