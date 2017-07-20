******************************************************************************
**********                                                          **********
**********     Monadics.lhs --- monadic bits and pieces             **********
**********                                                          **********
******************************************************************************

> module Monadics where

> import Category


> infixl 9 =<<

> (=<<) :: Monad m => (s -> m t) -> m s -> m t
> (=<<) = flip (>>=)

> mmult :: Monad m => m (m x) -> m x
> mmult = (>>= id)


******************************************************************************
Monads are Fun
******************************************************************************

> monadDollar :: Monad m => m (s -> t) -> m s -> m t
> monadDollar mf ms
>   = do f <- mf
>        s <- ms
>        return (f s)

(defun monad-fun (monad) (insert (concat "\n\n"
"> instance Fun " monad " where\n"
">   eta   = return\n"
">   (<$>) = monadDollar\n"
)))



******************************************************************************
Kleisli composition
******************************************************************************

> infixr 6 <.>
> (<.>) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
> (f <.> g) a
>   = do b <- g a
>        f b



******************************************************************************
Id
******************************************************************************

> instance Monad Id where
>   return = Id
>   Id s >>= f = f s


******************************************************************************
Maybe
******************************************************************************

(monad-fun "Maybe")

> instance Fun Maybe where
>   eta   = return
>   (<$>) = monadDollar

> instance Monoidal (Maybe x) where
>   m0 = Nothing
>   Nothing    <+> x = x
>   x@(Just _) <+> _ = x

> instance Functorial Maybe where
>   f <^> Nothing = fun Nothing
>   f <^> Just x  = fun Just (f x)

> unjust :: Maybe x -> x -- very sorry folks
> unjust (Just x) = x
> unjust Nothing = error "unjust unjustified"



******************************************************************************
Rightmost
******************************************************************************

> data Rightmost x = Rightmost x | Missing

> instance Monad Rightmost where
>   return = Rightmost
>   Rightmost x >>= f = f x
>   Missing >>= f     = Missing

> instance Monoidal (Rightmost x) where
>   m0 = Missing
>   x <+> Missing         = x
>   _ <+> x@(Rightmost _) = x

> instance Functorial Rightmost where
>   f <^> Missing     = fun Missing
>   f <^> Rightmost x = fun Rightmost (f x)


(base-funnel "(Rightmost x)")

> instance Fun f => Funnel f (Rightmost x) (f (Rightmost x)) where
>   fun    = eta
>   funnel = id


(monad-fun "Rightmost")

> instance Fun Rightmost where
>   eta   = return
>   (<$>) = monadDollar


> replacement :: x -> Rightmost x -> x
> replacement x Missing = x
> replacement _ (Rightmost x) = x


******************************************************************************
Monadic testing
******************************************************************************

> ensure :: Monad m => Bool -> m ()
> ensure True  = return ()
> ensure False = fail ""

> guard :: (Monad m,Monoidal (m s)) => (s -> Bool) -> s -> m s
> guard p x | p x = return x
> guard _ _ = m0

> seek :: (Functorial g,Monad m,Monoidal (m s)) =>
>         (s -> Bool) -> g s -> m s
> seek = (<!>) . guard



******************************************************************************
Transitions
******************************************************************************

> prefer :: Maybe x -> x -> x
> prefer (Just x) _ = x
> prefer _        x = x

> try :: (x -> Maybe x) -> x -> x
> try f x = prefer (f x) x

> type Trans x = x -> Maybe x

> repeatedly :: Trans x -> x -> x
> repeatedly f = try effing
>   where effing = (effing <+> return) <.> f

> repeatUntil :: Trans x -> Trans x -> Trans x
> repeatUntil step stop = stop <+> (repeatUntil step stop <.> step)



******************************************************************************
Statey things
******************************************************************************

> newtype State m s a = State {unState :: s -> m (a,s)}

> instance Unpack (State m s a) (s -> m (a,s)) where
>   un = unState
>   nu = State

> instance Monad m => Monad (State m s) where
>   return a = State $ \ s -> return (a,s)
>   State f >>= g
>     = State $ \ s ->
>         do (a,s') <- f s
>            un (g a) s'
>   fail x = State $ \ _ -> fail x

> get :: Monad m => (s -> a) -> State m s a
> get f = State $ \ s -> return (f s,s)

> set :: Monad m => s -> State m s ()
> set s = State $ \ _ -> return ((),s)

> tweak :: Monad m => (s -> s) -> State m s ()
> tweak f =
>   do s' <- get f
>      set s'

> doo :: Monad m => m a -> State m s a
> doo ma = State $ \ s -> do a <- ma ; return (a,s)

> effect :: Monad m => s -> State m s () -> m s
> effect start prog =
>   do (_,s) <- un prog start
>      return s

> tryThis :: s -> State Maybe s () -> s
> tryThis start prog = flip prefer start $
>   do (_,s) <- un prog start
>      return $! s

> result :: Monad m => s -> State m s x -> m x
> result start prog =
>   do (x,_) <- un prog start
>      return x

> locally :: Monad m => State m s x -> State m s x
> locally this =
>   do s <- get id
>      x <- this
>      set s
>      return x

> instance (Monoidal (m (x,s)), Monad m) => Monoidal (State m s x) where
>   m0 = State $ m0
>   tx <+> ty = State $ unState tx <+> unState ty

> sequentially :: (Functorial g,Monoidal y,Monad m) =>
>   (x -> State m s y) -> g x -> State m s y
> sequentially f gx = noitca step (return m0) gx where
>   step s x = eta (<+>) <$> s <$> f x

> instance Monad m => Fun (State m s) where
>   eta = return
>   (<$>) = monadDollar

(base-funnel "(State m s a)")

> instance Fun f => Funnel f (State m s a) (f (State m s a)) where
>   fun    = eta
>   funnel = id


