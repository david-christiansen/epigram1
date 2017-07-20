******************************************************************************
**********                                                          **********
**********     Compute.lhs --- factota to the Epigram elaborator    **********
**********                                                          **********
******************************************************************************

> module Compute where

> import Utils
> import Category
> import Monadics
> import Zip
> import Name
> import Update
> import Logic
> import Boole
> import Emacs
> import Box
> import Doc
> import Igor
> import EditDoc
> import Parser
> import Term
> import ObjKind
> import Unify

> import Debug.Trace


******************************************************************************
FunDomRan
******************************************************************************

> data FunDomRan = FunDomRan Term deriving Show

> instance Updatable FunDomRan where
>   upd bull (FunDomRan ft) = eta FunDomRan <$> upd bull ft

> instance Displayable FunDomRan

> instance Problem FunDomRan Term where
>   refine q@(FunDomRan (TBind All uv@(_,NormV) sc@(Sem (Just dom) ran))) =
>     solved (pair dom (TBind Lam uv (Sem Nothing ran))) q
>   refine q@(FunDomRan t@(TElim (Hope _) _)) = do
>     (_,dom) <- public "fdrS" Zip $ hope star
>     (_,ran) <- public "fdrT" Zip . hope $
>         TBind All dull (Sem (Just dom) (const star))
>     u <- compute "u" . UnifyIn star t $
>         TBind All dull (Sem (Just dom) (ran @@))
>     reduced . When u $
>       Solve (pair dom (TBind Lam dull (Sem Nothing{-dom-} (ran @@)))) q
>   refine (FunDomRan t) | Might True <- unclear t =
>     stuck
>   refine q =
>     solved (TF Bot) q
>   probType _ = TBind Ex dull . Sem (Just star) $ \ d ->
>                TBind All dull . Sem (Just d) $ \ _ -> star


******************************************************************************
IWrap
******************************************************************************

> data IWrap = IWrap Term deriving Show

> instance Displayable IWrap

> instance Updatable IWrap where
>   upd bull (IWrap t) = eta IWrap <$> upd bull t

> instance Problem IWrap Term where
>   refine (IWrap (TBind All (unom,UnifV) (Sem (Just dom) ran))) = do
>     (_,x) <- public "" Zip $ lambda UnifV dom
>     reduced $ IWrap (ran x)
>   refine (IWrap (TBind Ex (unom,UnifV) (Sem (Just dom) ran))) = do
>     (_,x) <- public "" Zip $ hope dom
>     public "" Zip $ witness UnifV (x ::: dom)
>     reduced $ IWrap (ran x)
>   refine q@(IWrap t) | clearlyNotImplicit t =
>     solved t q
>   refine _ = doo m0


******************************************************************************
IComplete
******************************************************************************

> data IComplete = IComplete (Term ::: Term) deriving Show

> instance Displayable IComplete

> instance Updatable IComplete where
>   upd bull (IComplete t) = eta IComplete <$> upd bull t

> instance Problem IComplete Term where
>   refine (IComplete (f :::
>                      TBind All (UN s,UnifV) (Sem (Just dom) ran))) = do
>     (_,x) <- public s Zip $ hope dom
>     let cmpl = (f @@ u_ @@ x ::: ran x)
>     track ("ICOMPLETE: " ++ show cmpl) $ return ()
>     reduced $ IComplete cmpl
>   refine (IComplete (p ::: TBind Ex (unom,UnifV) (Sem (Just dom) ran))) =
>     reduced $ IComplete (p @@ u_ @@ pi2 ::: ran (p @@ pi1))
>   refine q@(IComplete vt@(_ ::: t)) | clearlyNotImplicit t =
>     solved (cell vt) q
>   refine _ = doo m0


******************************************************************************
Explicit
******************************************************************************

> data Explicit = Explicit (Term ::: Term) deriving Show

> instance Displayable Explicit

> instance Updatable Explicit where
>   upd bull (Explicit t) = eta Explicit <$> upd bull t

> instance Problem Explicit Term where
>   refine q@(Explicit (f ::: TBind b (unom,UnifV) (Sem dom ran))) =
>     solved (cell (f @@ u_ ::: TBind b (unom,NormV) (Sem dom ran))) q
>   refine q@(Explicit vt@(_ ::: t)) | clearlyNotImplicit t =
>     solved (cell vt) q
>   refine _ = doo m0


******************************************************************************
IsFamilyType
******************************************************************************

> data IsFamilyType = IsFamilyType Term deriving Show

> instance Displayable IsFamilyType

> instance Updatable IsFamilyType where
>   upd bull (IsFamilyType t) = eta IsFamilyType <$> upd bull t

> instance Problem IsFamilyType (Boole LName) where
>   refine q@(IsFamilyType (TF Star)) =
>     solved (BVal True) q
>   refine q@(IsFamilyType (TBind All (un,vis) (Sem (Just dom) ran))) = do
>     (_,x) <- private "x" Zip $ forAll vis dom
>     reduced (IsFamilyType (ran x))
>   refine (IsFamilyType t) | Might True <- unclear t =
>     stuck
>   refine q@(IsFamilyType _) =
>     solved (BVal False) q


******************************************************************************
IsConstructorType
******************************************************************************

> data IsConstructorType = IsConstructorType UName Term deriving Show

> instance Displayable IsConstructorType

> instance Updatable IsConstructorType where
>   upd bull (IsConstructorType ufam t) =
>     eta (IsConstructorType ufam) <$> upd bull t

> instance Problem IsConstructorType (Boole LName) where
>   refine q@(IsConstructorType ufam (TF (Con TypeCon unom _ az)))
>     | unom == ufam
>     = do
>       b <- sequentially (compute "b" . DoesNotMention ufam) az
>       solved b q
>   refine q@(IsConstructorType ufam
>             (TBind All (unom,vis) (Sem (Just dom) ran))) = do
>     bd <- compute "bd" $ IsConstructorArgType ufam dom
>     (xb,x) <- param (ObjAbst All vis) unom dom
>     (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                 IsConstructorType ufam (ran x)
>     solved (bd <+> br) q
>   refine (IsConstructorType ufam t) | Might True <- unclear t =
>     stuck
>   refine q@(IsConstructorType ufam t) =
>     solved (BVal False) q


******************************************************************************
IsConstructorArgType
******************************************************************************

> data IsConstructorArgType = IsConstructorArgType UName Term deriving Show

> instance Displayable IsConstructorArgType

> instance Updatable IsConstructorArgType where
>   upd bull (IsConstructorArgType ufam t) =
>     eta (IsConstructorArgType ufam) <$> upd bull t

> instance Problem IsConstructorArgType (Boole LName) where
>   refine q@(IsConstructorArgType ufam (TF (Con TypeCon unom _ _)))
>     | unom == ufam
>     = solved (BVal True) q
>   refine q@(IsConstructorArgType ufam
>     (TBind All (unom,vis) (Sem (Just dom) ran))) = do
>       bd <- compute "bd" $ DoesNotMention ufam dom
>       (xb,x) <- param (ObjAbst All vis) unom dom
>       (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                   IsConstructorArgType ufam (ran x)
>       solved (bd <+> br) q
>   refine (IsConstructorArgType ufam t) | Might True <- unclear t =
>     stuck
>   refine (IsConstructorArgType ufam t) =
>     reduced (DoesNotMention ufam t)


******************************************************************************
DoesNotMention
******************************************************************************

> data DoesNotMention = DoesNotMention UName Term deriving Show

> instance Displayable DoesNotMention

> instance Updatable DoesNotMention where
>   upd bull (DoesNotMention ufam t) =
>     eta (DoesNotMention ufam) <$> upd bull t

> instance Problem DoesNotMention (Boole LName) where
>   refine (DoesNotMention ufam t) | Might True <- unclear t =
>     stuck
>   refine q@(DoesNotMention ufam (TF (Con TypeCon unom _ _)))
>     | unom == ufam
>     = solved (BVal False) q
>   refine q@(DoesNotMention ufam
>     (TBind bop (unom,vis) (Sem (Just dom) ran))) = do
>       bd <- compute "bd" $ DoesNotMention ufam dom
>       (xb,x) <- param (ObjAbst bop vis) unom dom
>       (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                   DoesNotMention ufam (ran x)
>       solved (bd <+> br) q
>   refine q@(DoesNotMention ufam
>     (TBind bop (unom,vis) (Sem Nothing ran))) = do
>       (xb,x) <- param (ObjAbst bop vis) unom star --dummy for dom
>       (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                   DoesNotMention ufam (ran x)
>       solved br q
>   refine q@(DoesNotMention ufam (TF ft)) = do
>     b <- sequentially (compute "b" . DoesNotMention ufam) ft
>     solved b q
>   refine q@(DoesNotMention ufam (TElim h tez)) = do
>     b1 <- case h of
>             Blocked _ ts ->
>               sequentially (compute "b" . DoesNotMention ufam) ts
>             _ -> return m0
>     b2 <- (sequentially . sequentially)
>             (compute "b" . DoesNotMention ufam) tez
>     solved (b1 <+> b2) q


******************************************************************************
IsEliminatorType
******************************************************************************

> data IsEliminatorType = IsEliminatorType Term deriving Show

> instance Displayable IsEliminatorType

> instance Updatable IsEliminatorType where
>   upd bull (IsEliminatorType t) = eta IsEliminatorType <$> upd bull t

> instance Problem IsEliminatorType (Boole LName) where
>   refine (IsEliminatorType t) | Might True <- unclear t =
>     stuck
>   refine q@(IsEliminatorType
>             (TBind All (unom,NormV) (Sem (Just dom) ran))) = do
>     bd <- compute "bd" $ IsFamilyType dom
>     (xb@(xn :=: _),x) <- param ObjPar unom dom
>     (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                 IsEliminatorTip xn (ran x)
>     solved (bd <+> br) q
>   refine q =
>     solved (BVal False) q


******************************************************************************
IsEliminatorTip
******************************************************************************

> data IsEliminatorTip = IsEliminatorTip LName Term deriving Show

> instance Displayable IsEliminatorTip

> instance Updatable IsEliminatorTip where
>   upd bull (IsEliminatorTip nom t) = eta (IsEliminatorTip nom) <$> upd bull t

> instance Problem IsEliminatorTip (Boole LName) where
>   refine (IsEliminatorTip nom t) | Might True <- unclear t =
>     stuck
>   refine q@(IsEliminatorTip nom (TElim (Var (F nam)) _)) | nom == nam =
>     solved (BVal True) q
>   refine q@(IsEliminatorTip nom
>       (TBind All (unom,NormV) (Sem (Just dom) ran))) = do
>     bd <- compute "bd" $ IsMethodType nom dom
>     (xb,x) <- param ObjPar unom dom
>     (_,br) <- public "br" (Zip :<: xb) . await (Compute,QTerm) $
>                 IsEliminatorTip nom (ran x)
>     solved (bd <+> br) q
>   refine q =
>     solved (BVal False) q


******************************************************************************
IsMethodType
******************************************************************************

> data IsMethodType = IsMethodType LName Term deriving Show

> instance Displayable IsMethodType

> instance Updatable IsMethodType where
>   upd bull (IsMethodType nom t) = eta (IsMethodType nom) <$> upd bull t

> instance Problem IsMethodType (Boole LName) where
>   refine (IsMethodType nom t) | Might True <- unclear t =
>     stuck
>   refine q@(IsMethodType nom (TElim (Var (F nam)) _)) | nom == nam =
>     solved (BVal True) q
>   refine (IsMethodType nom (TBind All (unom,_) (Sem (Just dom) ran))) = do
>     x <- parPush unom dom
>     reduced (IsMethodType nom (ran x))
>   refine q =
>     solved (BVal False) q


