******************************************************************************
**********                                                          **********
**********     Name.lhs --- names and other stuff                   **********
**********                                                          **********
******************************************************************************

> module Name where

> import Utils
> import Zip
> import Category

> -- import Debug.Trace

******************************************************************************
LName
******************************************************************************

> type Name = Zip (String,Int)

> newtype LName = Long Name deriving Eq

(base-funnel "LName")

> instance Fun f => Funnel f LName (f LName) where
>   fun    = eta
>   funnel = id


 instance Eq LName where
   Long xz == Long yz = plunk xz yz where
     plunk xz yz = plink xz yz
     plink Zip Zip = True
     plink (xz :<: (s,i)) (yz :<: (t,j))
       = i == j && plunk xz yz && s == t
     plink _ _ = False


> instance Show LName where
>   show (Long Zip) = ""
>   show (Long (siz :<: (s,i))) = show (Long siz) ++ s ++ show i

> infixl 9 ///

> class Localize x where
>   (///) :: LName -> x -> LName

> instance Localize LName where
>   Long nz1 /// Long nz2 = Long (nz1 <+> nz2)

> instance Localize (String,Int) where
>   Long nz /// si = Long (nz :<: si)

> instance Localize String where
>   Long nz /// s = Long (nz :<: (s,0))

The LName partial order

 instance Eq (String,Int) where -- a bit of an abuse
   (x,-1) ==  (y,_) = x == y
   (x,_)  == (y,-1) = x == y
   (x,i)  ==  (y,j) = x == y && i == j

 anyI :: Int
 anyI = -1

> instance Ord LName where
>   compare (Long nom) (Long nam) = compare (nom <>> nil) (nam <>> nil)


> relName :: LName -> LName -> LName
> relName (Long root) (Long nom)
>   | (_,outs,ins) <- commonPrefix (root <>> nil) (nom <>> nil)
>   = Long ((Zip <>< (up (const ("^",0)) outs)) <>< ins)


******************************************************************************
UName
******************************************************************************

> newtype UName = UN String deriving Eq

> instance Show UName where
>   show (UN s) = s

> type Alpha = [(Char,String)]

> idAlpha :: Alpha
> idAlpha = []

> coAlpha :: Alpha -> Alpha -> Alpha
> coAlpha = flip (++)

> alpha :: Alpha -> UName -> UName
> alpha css (UN s) = UN (blat s []) where
>   blat [] = id
>   blat (c : cs) | Just s <- lookup c css = (s ++) . blat cs
>                 | otherwise              = (c :) . blat cs

> mkAlpha :: UName -> UName -> Alpha
> mkAlpha (UN p) (UN t) =
>   mk (reverse (filter isAlpha p)) (reverse (filter isAlpha t)) where
>     mk _        []                   = []
>     mk []       _                    = []
>     mk (p : ps) (t : ts) | p == t    = mk ps ts
>     mk [p]      ts                   = [(p,reverse ts)]
>     mk (p : ps) (t : ts)             = (p,[t]) : mk ps ts
>     isAlpha c | 'A' <= c && c <= 'Z' = True
>     isAlpha c | 'a' <= c && c <= 'z' = True
>     isAlpha c = False

> scPrefix :: [String] -> String
> scPrefix [] = []
> scPrefix sss@(s : ss) = foldr inStep s ss where
>   inStep (c : cs) (d : ds) | c == d = c : inStep cs ds
>   inStep _        _                 = []

> rootName :: [String] -> String
> rootName [] = "x"
> rootName ss = if null ps then "" else ps where
>   pref = scPrefix ss
>   suff = scPrefix (map (reverse . drop (length pref)) ss)
>   ps = pref ++ reverse suff



******************************************************************************
Inductive Gadget Names
******************************************************************************

> data IndElim
>   = ICase | IView | IMemo | IRec | IGen
>   deriving Eq

> instance Show IndElim where
>   show ICase = "case"
>   show IView = "view"
>   show IMemo = "memo"
>   show IRec  = "rec"
>   show IGen  = "gen"
