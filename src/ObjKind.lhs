******************************************************************************
**********                                                          **********
**********     ObjKind.lhs --- kinds of Epigram objects             **********
**********                                                          **********
******************************************************************************

> module ObjKind where

> import Name
> import Category
> import Monadics


******************************************************************************
Bind
******************************************************************************

> data Bind
>   = Lam | All | Ex
>   deriving Eq

> instance Show Bind where
>   show Lam = "lam"
>   show All = "all"
>   show Ex  = "ex"



******************************************************************************
Visibility
******************************************************************************

> data Visibility = NormV | UnifV deriving Eq

> instance Show Visibility where
>   show NormV = ""
>   show UnifV = "_"



******************************************************************************
ObjKind
******************************************************************************

> data Con = TypeCon | DataCon LName deriving (Show,Eq)

> data ObjKind
>   = ObjAbst Bind Visibility
>   | ObjWit Visibility
>   | ObjDefn
>   | ObjDecl Con
>   | ObjPar
>   | ObjBad
>   | ObjRec
>   deriving Eq

> instance Show ObjKind where
>   show (ObjAbst b v) = show b ++ show v
>   show (ObjWit v) = "wit" ++ show v
>   show ObjDefn = "let"
>   show (ObjDecl TypeCon) = "data"
>   show (ObjDecl _) = "con"
>   show ObjPar = ""
>   show ObjBad = "bad"
>   show ObjRec = "rec"


(base-funnel "Con")

> instance Fun f => Funnel f Con (f Con) where
>   fun    = eta
>   funnel = id

(base-funnel "ObjKind")

> instance Fun f => Funnel f ObjKind (f ObjKind) where
>   fun    = eta
>   funnel = id



******************************************************************************
Descriptions cached in binders
******************************************************************************

> type Desc = (UName,      -- user's preferred name
>              Visibility  -- instruction to the elaborator
>             )

> dull :: Desc
> dull = (UN "", NormV)

