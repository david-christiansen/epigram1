******************************************************************************
**********                                                          **********
**********     Zip.lhs --- zippers and tipped lists                 **********
**********                                                          **********
******************************************************************************

> module Zip where

> import Category
> import Monadics



******************************************************************************
Zip
******************************************************************************

> infixl 6 :<:
> data Zip s
>   = Zip
>   | Zip s :<: s
>   deriving Eq

> instance Show x => Show (Zip x) where
>   show Zip = ""
>   show (xz :<: x) = show xz ++ "< " ++ show x ++ "\n"

(base-funnel "(Zip s)")

> instance Fun f => Funnel f (Zip s) (f (Zip s)) where
>   fun    = eta
>   funnel = id

> instance Monoidal (Zip s) where
>   m0 = Zip
>   xz <+>     Zip    = xz
>   xz <+> (yz :<: y) = (xz <+> yz) :<: y

> instance Functorial Zip where
>   g <^>  Zip       = fun Zip
>   g <^> (xz :<: x) = fun (:<:) (g <^> xz) (g x)

> instance Functor Zip where
>   fmap g  Zip       = Zip
>   fmap g (xz :<: x) = (:<:) (fmap g xz) (g x)

Zip has a post-application action ...

> zOne :: x -> Zip x
> zOne = (Zip :<:)

> zPost :: (b -> a -> b) -> b -> Zip a -> b
> zPost app t Zip = t
> zPost app f (sz :<: s) = app (zPost app f sz) s

> zCache :: Zip s -> (Zip (Zip s,s))
> zCache Zip = Zip
> zCache (xz :<: x) = zCache xz :<: (xz,x)

> zosh :: Show x => String -> Zip x -> String
> zosh cap Zip = ""
> zosh cap xz = concat [cap,"[\n",show xz,"]",cap,"\n"]

> zlen :: Zip x -> Int
> zlen Zip = 0
> zlen (z :<: _) = 1 + zlen z


******************************************************************************
Tip, List
******************************************************************************

> infixr 6 :>:
> data Tip t s
>   = Tip t
>   | s :>: Tip t s
>   deriving Eq

> instance Show s => Show (Tip t s) where
>   show (Tip _) = ""
>   show (x :>: xs) = "> " ++ show x ++ "\n" ++ show xs

(base-funnel "(Tip t s)")

> instance Fun f => Funnel f (Tip t s) (f (Tip t s)) where
>   fun    = eta
>   funnel = id


> type List = Tip ()
> nil = Tip ()

> infixr 6 >>>
> (>>>) :: Tip lost s -> Tip t s -> Tip t s
> (x :>: xs) >>> ys = x :>: xs >>> ys
> _          >>> ys = ys

> instance Monoidal (List s) where
>   m0 = nil
>   (<+>) = (>>>)

> instance Functorial (Tip t) where
>   g <^> (x :>: xs) = fun (:>:) (g x) (g <^> xs)
>   g <^> Tip t      = fun (Tip t)

> instance Functor (Tip t) where
>   fmap g (x :>: xs) = (:>:) (g x) (fmap g xs)
>   fmap g (Tip t)      = Tip t

> instance Unpack (List x) [x] where
>   un = (<!>) (: [])
>   nu = (<!>) (:>: nil)

> losh :: Show x => String -> List x -> String
> losh cap (Tip _) = ""
> losh cap xs = concat [cap,"[\n",show xs,"]",cap,"\n"]


******************************************************************************
Shuffling
******************************************************************************

> infixr 6 <>>

> (<>>) :: Zip x -> Tip t x -> Tip t x
> Zip <>> xs = xs
> (xz :<: x) <>> xs = xz <>> (x :>: xs)

> infixl 6 <><.

> (<><.) :: Zip x -> Tip t x -> (Zip x,t)
> xz <><. Tip t = (xz,t)
> xz <><. (x :>: xs) = xz :<: x <><. xs

> infixl 6 <><

> (<><) :: Zip x -> Tip a x -> Zip x
> xz <>< xs = fst (xz <><. xs)

> zippy :: [x] -> Zip x
> zippy = zz Zip where
>   zz xz [] = xz
>   zz xz (x : xs) = zz (xz :<: x) xs

> yppiz :: Zip x -> [x]
> yppiz xz = yy xz [] where
>   yy Zip xs = xs
>   yy (xz :<: x) xs = yy xz (x : xs)


******************************************************************************
Unsafe stack operations
******************************************************************************

> zTop :: Zip s -> s
> zTop (_ :<: s) = s

> zPop :: Int -> Zip s -> Zip s
> zPop  0     zz        = zz
> zPop (n+1) (zz :<: _) = zPop n zz

> zCrop :: Int -> Zip s -> Zip s
> zCrop  0     zz        = Zip
> zCrop (n+1) (zz :<: z) = zCrop n zz :<: z

> tTop :: Tip t s -> s
> tTop (s :>: _) = s

> tPop :: Int -> Tip t s -> Tip t s
> tPop  0     ss        = ss
> tPop (n+1) (_ :>: ss) = tPop n ss

> lCrop :: Int -> List s -> List s
> lCrop  0     ss        = nil
> lCrop (n+1) (s :>: ss) = s :>: lCrop n ss


******************************************************************************
Search in a list
******************************************************************************

> index :: Eq x => Tip t (x,z) -> x -> Maybe (Int,z)
> index ((x,z) :>: xs) y
>   | x == y = Just (0, z)
>   | Just (i, z) <- index xs y = Just (i + 1, z)
> index _ _ = m0

******************************************************************************
Fun instances
******************************************************************************

> instance Fun Zip where
>   (fz :<: f) <$> (sz :<: s) = fz <$> sz :<: f s
>   _          <$> _          = Zip
>   eta x = eta x :<: x

> instance Fun List where
>   (f :>: fs) <$> (s :>: ss) = f s :>: fs <$> ss
>   _          <$> _          = nil
>   eta x = x :>: eta x


******************************************************************************
Lookup operations
******************************************************************************

> infixr 4 :=:
> data x :=: t = x :=: t deriving Show

> key :: (x :=: t) -> x
> key (x :=: _) = x

(base-funnel "(x :=: t)")

> instance Fun f => Funnel f (x :=: t) (f (x :=: t)) where
>   fun    = eta
>   funnel = id

> instance Functorial ((:=:) x) where
>   g <^> (x :=: t) = fun ((:=:) x) (g t)

> instance Eq x => Eq (x :=: t) where
>   (x :=: _) == (y :=: _) = x == y

> isIt :: (Fun f,Monoidal (f t),Eq x) => x -> (x :=: t) -> f t
> isIt x (x' :=: t) = when (x == x') (eta t)

> zAssoc :: Eq p => Zip (p :=: t) -> p -> Rightmost t
> zAssoc ptz p = isIt p <!> ptz

> lAssoc :: Eq p => List (p :=: t) -> p -> Maybe t
> lAssoc ptz p = isIt p <!> ptz


******************************************************************************
Prefix comparability
******************************************************************************

> commonPrefix :: Eq x => Tip t x -> Tip t x -> (Zip x,Tip t x,Tip t x)
> commonPrefix t1 t2 = cp Zip t1 t2 where
>   cp xz (x1 :>: t1) (x2 :>: t2) | x1 == x2 = cp (xz :<: x1) t1 t2
>   cp xz t1 t2 = (xz,t1,t2)

> instance Eq x => Ord (List x) where
>   compare l1 l2
>     = case commonPrefix l1 l2 of
>         (_,Tip _,Tip _) -> EQ
>         (_,Tip _,_)     -> LT
>         _               -> GT


******************************************************************************
Cursors
******************************************************************************

> type Cursor = Cross Zip List

> instance Show x => Show (Cursor x) where
>   show (xz :*: xs) = show xz ++ ":*:\n" ++ show xs

> cur0 :: Cursor x
> cur0 = Zip :*: nil

> curUp :: Trans (Cursor x)
> curUp (xz :<: y :*: zs) = eta (xz :*: y :>: zs)
> curUp _ = m0

> curDown :: Trans (Cursor x)
> curDown (xz :*: y :>: zs) = eta (xz :<: y :*: zs)
> curDown _ = m0

> curList :: Cursor x -> List x
> curList (xz :*: xs) = xz <>> xs

> instance Unpack (Cursor x) [x] where
>   un (xz :*: xs) = un (xz <>> xs)
>   nu xs      = (Zip :*: nu xs)

> curIns :: x -> Cursor x -> Cursor x
> curIns x (xz :*: es) = xz :<: x :*: es
