******************************************************************************
**********                                                          **********
**********     Equality.lhs --- Epigram equality                    **********
**********                                                          **********
******************************************************************************

> module Equality where

> import Category
> import Monadics
> import Logic
> import Zip
> import Name
> import Term
> import ObjKind
> import Igor

> -- import Debug.Trace
> import Utils

******************************************************************************
Equality Classes
******************************************************************************

> type QEnv = (Ctxt,Params,Int,Zip Term)

> qPush :: QEnv -> Term -> QEnv
> qPush (glob,del,n,loc) t = (glob,del,n + 1,loc :<: t)

> qGlob :: QEnv -> LName -> Term
> qGlob (glob,del,_,_) nom = replacement (TF Bot) $
>   varType nom glob <+> varType nom del

> qLoc :: QEnv -> Int -> Term
> qLoc (_,_,n,loc) i = zTop (zPop (n - i - 1) loc)

> qVar :: Var x => QEnv -> UName -> x
> qVar (_,_,n,_) u = var n u

> qType :: QEnv -> McKP LName -> Term
> qType e (F nom) = qGlob e nom
> qType e (B j _)   = qLoc e j

> class EtaEq ty t where
>   etaEq :: QEnv -> ty -> t -> t -> Must

> class BetaEq t where
>   betaEq :: QEnv -> t -> t -> Must

> instance (BetaEq ty,EtaEq ty t) => BetaEq (t ::: ty) where
>   betaEq i (t1 ::: ty1) (t2 ::: ty2)
>     = betaEq i ty1 ty2 <+> etaEq i ty1 t1 t2


******************************************************************************
Beta equality
******************************************************************************

> instance BetaEq Term where -- comparing types or ground blocked things
>   -- betaEq _ s t | unsafePtrEq s t = m0
>   betaEq _ (TF Star) (TF Star) = m0
>   betaEq _ (TF One)  (TF One)  = m0
>   betaEq _ (TF Zero) (TF Zero) = m0
>   betaEq n (TBind b1 (u1, v1) sc1) (TBind b2 (u2, v2) sc2)
>     | b1 == b2, v1 == v2 = betaEq n (u1, sc1) (u2, sc2)
>   betaEq n (TF (Con TypeCon _ nom1 az1)) (TF (Con TypeCon _ nom2 az2))
>     | nom1 == nom2
>     , Just _ <- zipEq n (qGlob n nom1) az1 az2
>     = m0
>   betaEq n (TF (Lbl LabTy l1 t1)) (TF (Lbl LabTy l2 t2))
>     = betaEq n l1 l2 <+> betaEq n t1 t2
>   betaEq n (TF (JMEq ssy1 tty1)) (TF (JMEq ssy2 tty2))
>     = betaEq n ssy1 ssy2 <+> betaEq n tty1 tty2
>   betaEq n (TElim h1 ez1) (TElim h2 ez2)
>     | Just _ <- spineEq n h1 ez1 h2 ez2
>     = m0
>   betaEq _ s t = track (show s ++ " UNEQ " ++ show t) $ Must False

> instance BetaEq (r LName) => BetaEq (UName, Sem (Tm Sem) r LName) where
>   betaEq n (u1, Sem (Just d1) f1) (u2, Sem (Just d2) f2)
>     = betaEq n d1 d2
>       <+> betaEq (qPush n d1) (f1 (qVar n u1)) (f2 (qVar n u2))

> instance BetaEq (Label Term) where
>   betaEq n (Label (u1 ::: t1) az1 wz1) (Label (u2 ::: _) az2 wz2)
>     = Must (u1 == u2) <+> etaEq n t1 (az1 <>> nil) (az2 <>> nil)
>    --   <+> id <!> (fun (betaEq n) wz1 wz2)


******************************************************************************
Eta equality
******************************************************************************

> instance EtaEq Term (List Term) where
>   etaEq n _ (Tip ()) (Tip ()) = m0
>   etaEq n (TBind All (_,NormV) (Sem (Just d) f)) (a1 :>: as1) (a2 :>: as2)
>     = etaEq n d a1 a2 <+> etaEq n (f a1) as1 as2
>   etaEq n (TBind All (u,UnifV) dr) (TF (U_ _) :>: as1) (TF (U_ _) :>: as2)
>     = etaEq n (TBind All (u,NormV) dr) as1 as2
>   etaEq _ y s t = track (show s ++ " UNEQ " ++ show t ++ " IN " ++ show y)
>     $ Must False

> instance EtaEq Term Term where
>   -- etaEq _ _ s t | unsafePtrEq s t = m0
>   etaEq n _ (TElim (Var n1) Zip) (TElim (Var n2) Zip) | n1 == n2 = m0
>   etaEq n (TF Star) ty1 ty2 = betaEq n ty1 ty2
>   etaEq n (TF One)  _   _   = m0
>   etaEq n (TF Zero)  _   _   = m0
>   etaEq n (TBind b (unom,UnifV) s) x1 x2
>     = etaEq n (TBind b (unom,NormV) s) (x1 @@ u_) (x2 @@ u_)
>   etaEq n (TBind All (u,NormV) (Sem (Just ty) f)) f1 f2
>     = etaEq (qPush n ty) (f x) (f1 @@ x) (f2 @@ x)
>       where x = qVar n u
>   etaEq n (TBind Ex (_,NormV) (Sem (Just ty) f)) xy1 xy2
>     = etaEq n ty x (xy2 @@ pi1)
>       <+> etaEq n (f x) (xy1 @@ pi2) (xy2 @@ pi2)
>     where x = xy1 @@ pi1
>   etaEq n (TF (JMEq _ _)) _ _ = m0
>   etaEq n (TF (Lbl LabTy _ _)) _ _ = m0
>   etaEq n _ (TF (Con (DataCon _) _ nom1 az1))
>             (TF (Con (DataCon _) _ nom2 az2))
>     | nom1 == nom2
>     , Just _ <- zipEq n (qGlob n nom1) az1 az2
>     = m0
>   etaEq n _ (TElim h1 ez1) (TElim h2 ez2)
>     | Just _ <- spineEq n h1 ez1 h2 ez2
>     = m0
>   etaEq _ _ (TF (U_ _)) (TF (U_ _)) = error "EQ _"
>   etaEq _ _ (TF (U_ _)) _ = error "EQ _ left only"
>   etaEq _ _ _ (TF (U_ _)) = error "EQ _ right only"
>   etaEq _ y s t = track (show s ++ " UNEQ " ++ show t ++ " IN " ++ show y)
>     $ Must False

> instance EtaEq Term (Elim Term) where
>   etaEq n (TBind All (_,NormV) (Sem (Just d) _)) (A t1) (A t2) =
>     etaEq n d t1 t2
>   etaEq n (TBind b (_,UnifV) (Sem d _)) (A (TF (U_ _))) (A (TF (U_ _))) = m0
>   etaEq n _ (NoughtE y1) (NoughtE y2) = etaEq n star y1 y2
>   etaEq n _   P1         P1        = m0
>   etaEq n _   P2         P2        = m0
>   etaEq n _  (Call _)   (Call _)   = m0
>   etaEq n _  (Ind g1 _) (Ind g2 _) = Must (gKind g1 == gKind g2)
>   etaEq n _ (JM JMCoe) (JM JMCoe)  = m0
>   etaEq n _ (JM (JMCon _)) (JM (JMCon _)) = m0
>   etaEq n _ (JM JMSym) (JM JMSym)  = m0
>   etaEq n _ (JM (JMResp f)) (JM (JMResp g)) = betaEq n f g
>   etaEq _ y s t = track (show s ++ " UNEQ " ++ show t ++ " IN " ++ show y)
>     $ Must False

> headEq :: QEnv -> (Hd Sem LName) -> (Hd Sem LName) -> Maybe Term
> headEq n (Var x1) (Var x2) | x1 == x2 = eta (qType n x1)
> headEq n (Hope x1) (Hope x2)
>   | x1 == x2 = eta (qType n (F x1))
> headEq n (Wait x1) (Wait x2)
>   | x1 == x2 = eta (qType n (F x1))
> headEq n (Blocked f1 ts1) (Blocked f2 ts2)
>   | show f1 == show f2
>   = listEq n (typeH f1) ts1 ts2
> headEq (_,_,n,_) s t =
>  track (show (quote n nil s) ++ " UNheadEQ " ++ show (quote n nil t) )
>     $ m0

> typeOf :: QEnv -> Hd Sem LName -> Zip (Elim Term) -> Term
> typeOf n (Var x) Zip = qType n x
> typeOf n (Hope x) Zip = qType n (F x)
> typeOf n (Wait x) Zip = qType n (F x)
> typeOf n (Blocked _ _) Zip = error "typeOf Blocked not done yet"
> typeOf n h (ez :<: e) | (_ ::: t) <- (TElim h ez ::: typeOf n h ez) @@ e = t

> spineEq :: QEnv -> Hd Sem LName -> Zip (Elim Term) ->
>                    Hd Sem LName -> Zip (Elim Term) -> Maybe Term
> spineEq n h1 ez1 h2 ez2 = sp ez1 ez2 where
>   sp Zip Zip = headEq n h1 h2
>   sp (ez1 :<: e1) (ez2 :<: e2) = el e1 e2 where
>     el e1 e2 | track ("EL " ++ show e1 ++ " " ++ show e2) False = Nothing
>     el (A (TF (U_ _))) (A (TF (U_ _))) = do
>       TBind b (u,UnifV) dr <- sp ez1 ez2
>       return $ TBind b (u,NormV) dr
>     el (A a1) (A a2) = do
>       ty <- sp ez1 ez2
>       track ("ELAA " ++ show ty) $ return ()
>       TBind All (_,NormV) (Sem (Just dom) ran) <- return ty
>       Must True <- return $ etaEq n dom a1 a2
>       return $ ran a1
>     el (NoughtE x) (NoughtE y) = do
>       Must True <- return $ betaEq n x y
>       return x
>     el P1 P1 = do
>       TBind Ex (_,NormV) (Sem (Just dom) _) <- sp ez1 ez2
>       return dom
>     el P2 P2 = do
>       TBind Ex (_,NormV) (Sem _ ran) <- sp ez1 ez2
>       return $ ran (TElim h1 ez1)
>     el (Call lab1) (Call lab2) = do
>       Must True <- return $ betaEq n lab1 lab2
>       TF (Lbl LabTy _ ty) <- return $ typeOf n h1 ez1
>       return ty
>     el (Ind g1 iz) (Ind g2 _) | gKind g1 == gKind g2 = do
>       sp ez1 ez2
>       return $ gType g1 iz (TElim h1 ez1)
>     el (JM j1) (JM j2) = do
>       Must True <- return $ jm j1 j2
>       q1 <- return $ typeOf n h1 ez1
>       Must True <- return $ betaEq n q1 (typeOf n h2 ez2)
>       _ ::: t <- return $ (TElim h1 ez1 ::: q1) @@ (JM j1)
>       return t
>     el e1 e2 = track ("UNEQ elims " ++ show e1 ++ show e2) $ Nothing
>     jm (JMResp f) (JMResp g) = betaEq n f g
>     jm JMCoe JMCoe = Must True
>     jm (JMCon _) (JMCon _) = Must True
>     jm JMSym JMSym = Must True
>     jm _ _ = Must False
>   sp _ _ = m0

> listEq :: QEnv -> Term -> List Term -> List Term -> Maybe Term
> listEq n ty (Tip ()) (Tip ()) = eta ty
> listEq n (TBind All (_,NormV) (Sem (Just d) f)) (t1 :>: ts1) (t2 :>: ts2)
>   | un (etaEq n d t1 t2)
>   = listEq n (f t1) ts1 ts2
> listEq n (TBind All (unom,UnifV) s) (TF (U_ _) :>: ts1) (TF (U_ _) :>: ts2)
>   = listEq n (TBind All (unom,NormV) s) ts1 ts2
> listEq _ y s t = 
>  track (show s ++ " UNlistEQ " ++ show t ++ " IN " ++ show y)
>     $ m0

> zipEq :: QEnv -> Term -> Zip Term -> Zip Term -> Maybe Term
> zipEq _ ty Zip Zip = eta ty
> zipEq n ty (tz1 :<: TF (U_ _)) (tz2 :<: TF (U_ _))
>   | Just (TBind All (unom,UnifV) s) <- zipEq n ty tz1 tz2
>   = eta (TBind All (unom,NormV) s)
> zipEq n ty (tz1 :<: t1) (tz2 :<: t2)
>   | Just (TBind All (_,NormV) (Sem (Just d) f)) <- zipEq n ty tz1 tz2
>   , un (etaEq n d t1 t2)
>   = eta (f t1)
> zipEq _ y s t =
>  track (show s ++ " UNzipEQ " ++ show t ++ " IN " ++ show y)
>     $ m0


******************************************************************************
Elim Types
******************************************************************************

 blockEq :: QEnv -> (Term ::: Term) ->
            List (Elim Term) -> List (Elim Term) -> Must
 blockEq _ _ (Tip ()) (Tip ()) = m0
 blockEq n tty@(_ ::: ty) (e1 :>: es1) (e2 :>: es2)
   = etaEq n ty e1 e2 <+> blockEq n (tty @@ e1) es1 es2
 blockEq _ y s t = 
  track (show s ++ " UNzipEQ " ++ show t ++ " IN " ++ show y)
     $ Must False


******************************************************************************
Interface
******************************************************************************

> equalIn :: Params -> Term -> Term -> Term -> Refine Must
> equalIn del ty s t = do
>   ctxt <- get id
>   return (etaEq (ctxt,del,0,Zip) ty s t)

> typeSpine :: Params -> Hd Sem LName -> Zip (Elim Term) -> Refine Term
> typeSpine del h ez = do
>   ctxt <- get id
>   return (typeOf (ctxt,del,0,Zip) h ez)
