******************************************************************************
**********                                                          **********
**********     Parser.lhs --- a library of parser gadgets           **********
**********                                                          **********
******************************************************************************

> module Parser where

> import Category
> import Monadics


******************************************************************************
Parser - via State
******************************************************************************

> type Parser m i = State m [i]


******************************************************************************
Some basic combinators
******************************************************************************

> pE :: Monad m => Parser m i ()
> pE = fun ()

> pT :: Monad m => (i -> m o) -> Parser m i o
> pT g = nu f where
>   f (i : is) =
>     do o <- g i
>        return (o,is)
>   f [] = fail ""

> pEmpty :: Monad m => Parser m i ()
> pEmpty = nu f where
>   f [] = return ((),[])
>   f _  = fail ""

> pI :: Monad m => Parser m i i
> pI = pT return

> pCon :: (Monad m,Eq i) => i -> Parser m i ()
> pCon i = pT (ensure . (i ==))

> pSeq1 :: (Monoidal (m ([x], [i])),Monad m) =>
>          Parser m i x -> Parser m i y -> Parser m i [x]
> pSeq1 p sep = fun (:) p (sep <\> pSeq1 p sep <+> fun [])

> pSeq0 :: (Monoidal (m ([x], [i])),Monad m) =>
>          Parser m i x -> Parser m i y -> Parser m i [x]
> pSeq0 p sep = pSeq1 p sep <+> fun []

> pMay :: (Monoidal (m (Maybe x, [i])),Monad m) =>
>         Parser m i x -> Parser m i (Maybe x)
> pMay p = fun Just p <+> fun Nothing

> pSkipTo :: (Eq i,Monoidal (m ()),Monoidal (m ((),[i])),Monad m) =>
>             i -> Parser m i ()
> pSkipTo i = pT noti </> pSkipTo i <+> pE where
>   noti j | i == j = m0
>   noti _ = return ()


******************************************************************************
Computing parsers from types
******************************************************************************

> class Monad m => Parse m i x where
>   blah :: Parser m i x

> instance Monad m => Parse m i () where
>   blah = pE

> instance Parse m i x => Parse m i (K x y) where
>   blah = fun K blah

> instance Parse m i x => Parse m i (Id x) where
>   blah = fun Id blah

> instance Parse m i (f (g x)) => Parse m i (Comp f g x) where
>   blah = fun Comp blah

> gimme :: Parse m i x => [i] -> m x
> gimme is =
>   do (x,_) <- un blah is
>      return x

> reading :: Monad m => Parser m i x -> [i] -> m x
> reading p is =
>   do (x,[]) <- un p is
>      return x

> class Monad m => ParseFrom m t i x | t -> i x where
>   pF :: t -> Parser m i x

> instance (Monoidal (m (t,[i])),ParseFrom m s i ()) =>
>   ParseFrom m [(s,t)] i t where
>   pF = (<!>) (\ (s,t) -> eta t </> pF s)



