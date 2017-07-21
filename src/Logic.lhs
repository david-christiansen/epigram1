******************************************************************************
**********                                                          **********
**********     Logic.lhs --- logical gizmos                         **********
**********                                                          **********
******************************************************************************

> module Logic where

> import Category
> import Monadics


> newtype Might = Might Bool deriving (Show,Eq)

> instance Unpack Might Bool where
>   un (Might p) = p
>   nu = Might

> instance Monoidal Might where
>   m0 = Might False
>   Might p <+> Might q = Might $! (p || q)


> newtype Must = Must Bool deriving (Show,Eq)

> instance Unpack Must Bool where
>   un (Must p) = p
>   nu = Must

> instance Monoidal Must where
>   m0 = Must True
>   Must p <+> Must q = Must $! (p && q)



------------------------------------------------------------------------------

(base-funnel "Might")

> instance Applicative f => Funnel f Might (f Might) where
>   fun    = pure
>   funnel = id

(base-funnel "Must")

> instance Applicative f => Funnel f Must (f Must) where
>   fun    = pure
>   funnel = id
