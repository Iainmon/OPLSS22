


data L a b = Nil | Cons a b
  deriving Show

data Mu f a = In (f a (Mu f a))


type List a = Mu L a

class Bifunctor f where
  bimap :: (a -> c) -> (b -> d) -> f a b -> f c d

instance Bifunctor L where
  bimap f g Nil = Nil
  bimap f g (Cons a b) = Cons (f a) (g b)

instance Bifunctor f => Functor (Mu f) where
  fmap f (In x) = In (bimap f (fmap f) x)


cata :: Bifunctor f => (f a b -> b) -> (Mu f a -> a)
cata phi (In x) = phi (bimap id (cata phi) x)

ana :: Bifunctor f => (b -> f a b) -> (b -> Nu f a)
ana phi z = Out (bimap id (ana phi) (phi z))


-- a = In (Cons 1 (In Nil))

data Nu f a = Out (f a (Nu f a))
{- data Nu f a = Out { out :: f a (Nu f a) } -}

out :: Nu f a -> f a (Nu f a)
out (Out x) = x


type Colist a = Nu L a

range :: (Int,Int) -> Colist Int
range = ana next
  where 
        next :: (Int,Int) -> L Int (Int,Int)
        next (m,n) | m == n    = Nil
                   | otherwise = Cons m (m + 1,n)




data U a b = Empty | Fork b a b

type Cotree a = Nu U a

build :: Ord a => [a] -> Cotree a
build = ana next
  where
        next :: Ord a => [a] -> U a [a]
        next []     = Empty
        next (x:xs) = Fork ys x zs
          where ys = [y | y <- xs, y < x]
                zs = [z | z <- xs, z >= x]




data Nu' f = Out' { out' :: f (Nu' f) }

ana' :: Functor f => (b -> f b) -> b -> Nu' f
ana' = undefined



type CoNat = Nu Maybe




dropWhile :: (a -> Bool) -> [a] -> [b]
dropWhile p [] = []
dropWhile p (c:cs) | p x       = dropwhile p xs 
                   | otherwise = x : xs


para :: Bifunctor f => (f a (b,Mu f a) -> b) -> Mu f a -> b
para phi (In x) = undefined


data Cofree f b = Node b (f (Cofree f b))
data Mu' f = In (f (Mu' f))

