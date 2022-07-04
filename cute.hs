


data State s a = State (s -> (a,s))

instance Functor (State s) where
  fmap f (State st) = State $ \s->let (x,s') = st s in (f x,s')

instance Applicative (State s) where
  pure x = State (\s->(x,s))
  State st_f <*> State st_s =
      State (\s->let (f,s') = st_f s
                     (x,s'') = st_s s'
                  in (f x,s''))

instance Monad (State s) where
  -- return = pure
  State c >>= f = State (\s->let (x,s') = c s
                                 State d = f x
                              in d s')
run :: State s a -> s -> (a,s)
run (State f) = f

initState :: s -> State s ()
initState s = State $ \_-> ((),s)

onState :: (s -> s) -> State s ()
onState f = State $ \s -> ((),f s)

fromState :: (s -> a) -> State s a
fromState f = State $ \s -> (f s,s)





type Name = String


-- Our expression language
data Expr a
  = Lit a
  | Var Name
  | BinOp (a -> a -> a) (Expr a) (Expr a)
  | If (Expr a) (Expr a) (Expr a)
  | LetIn Name (Expr a) (Expr a)



type Binding a = [(Name,Expr a)]


type Context a b = State (Binding a) b

new :: Context a ()
new = initState []

bind :: Name -> Expr a -> Context a ()
bind x y = onState ((x,y):)

ref :: Name -> Context a (Expr a)
ref x = fromState (\ctx -> let (Just a) = lookup x ctx in a)

get :: State a a
get = fromState id


class ToBool a where
  tob :: a -> Bool

eval :: ToBool a => Expr a -> Context a a
eval (Lit a) = return a
eval (Var x) = do 
  e <- ref x
  eval e
eval (BinOp f a b) = do
  a' <- clean a
  b' <- clean b
  return $ f a' b'
eval (If e e1 e2) = do
  e' <- clean e
  if tob e' 
    then clean e1
    else clean e2
eval (LetIn x e1 e2) = do
  e1' <- clean e1
  bind x (Lit e1')
  clean e2

clean e = do
    ctx <- get
    e' <- eval e
    onState (const ctx)
    return e'


instance ToBool Int where
  tob 0 = False
  tob _ = True


add = BinOp (+)


prog = do 
          


