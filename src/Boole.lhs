******************************************************************************
**********                                                          **********
**********     Boolean expressions                                  **********
**********                                                          **********
******************************************************************************

> module Boole where

> import Name
> import Category

> data Boole x
>   = BVal Bool
>   | BVar x
>   | BAnd (Boole x) (Boole x)
>   | BOr (Boole x) (Boole x)
>   deriving Show

> bAnd :: Boole x -> Boole x -> Boole x
> bAnd (BVal False) _ = BVal False
> bAnd _ (BVal False) = BVal False
> bAnd (BVal True)  b = b
> bAnd b  (BVal True) = b
> bAnd b1          b2 = BAnd b1 b2

> bOr :: Boole x -> Boole x -> Boole x
> bOr (BVal True)  _ = BVal True
> bOr _  (BVal True) = BVal True
> bOr (BVal False) b = b
> bOr b (BVal False) = b
> bOr b1          b2 = BOr b1 b2

> instance Functorial Boole where
>   g <^> BVal b = fun (BVal b)
>   g <^> BVar x = fun BVar (g x)
>   g <^> BAnd b1 b2 = fun BAnd (g <^> b1) (g <^> b2)
>   g <^> BOr  b1 b2 = fun BOr (g <^> b1) (g <^> b2)

> instance Monad Boole where
>   return = BVar
>   BVal b >>= f = BVal b
>   BVar x >>= f = f x
>   BAnd b1 b2 >>= f = bAnd (b1 >>= f) (b2 >>= f)
>   BOr  b1 b2 >>= f = bOr (b1 >>= f) (b2 >>= f)

> instance Monoidal (Boole x) where
>   m0 = BVal True
>   (<+>) = bAnd

(base-funnel "(Boole x)")

> instance Fun f => Funnel f (Boole x) (f (Boole x)) where
>   fun    = eta
>   funnel = id

