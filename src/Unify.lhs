******************************************************************************
**********                                                          **********
**********     Unify.lhs --- Milleria dependensis                   **********
**********                                                          **********
******************************************************************************

> module Unify where

> import Debug.Trace

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
> import Equality


******************************************************************************
BOOLE
******************************************************************************

> data BOOLE = BOOLE deriving Show

> instance Updatable BOOLE
> instance Displayable BOOLE
> instance Problem BOOLE (Boole LName)

******************************************************************************
When
******************************************************************************

> data When q = When (Boole LName) q deriving Show

> instance Updatable q => Updatable (When q) where
>   upd bull (When b q)
>     = eta When <$> upd bull b <$> upd bull q

> instance Displayable q => Displayable (When q) where
>   display ew ctxt (When b q) = display ew ctxt q

> instance (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Problem q a)
>           => Problem (When q) a where
>   refine (When (BVal True) q) =
>     reduced q
>   refine (When (BVal False) q) =
>     failed
>   refine _ =
>     stuck


******************************************************************************
BWhen
******************************************************************************

> data BWhen q = BWhen (Boole LName) q deriving Show

> instance Updatable q => Updatable (BWhen q) where
>   upd bull (BWhen b q)
>     = eta BWhen <$> upd bull b <$> upd bull q

> instance Displayable q => Displayable (BWhen q) where
>   display ew ctxt (BWhen b q) = display ew ctxt q

> instance (Updatable q,Displayable q,Show q,
>           Problem q (Boole LName))
>           => Problem (BWhen q) (Boole LName) where
>   refine (BWhen (BVal True) q) =
>     reduced q
>   refine (BWhen (BVal False) q) =  -- False as failure
>     solved (BVal False) BOOLE
>   refine _ =
>     stuck


******************************************************************************
Solve
******************************************************************************

> data Solve a q = Solve a q deriving Show

> instance (Updatable a,Updatable q) => Updatable (Solve a q) where
>   upd bull (Solve a q) = eta Solve <$> upd bull a <$> upd bull q

> instance Displayable q => Displayable (Solve a q) where
>   display ew ctxt (Solve a q) = display ew ctxt q

> instance (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Problem q a)
>           => Problem (Solve a q) a where
>   refine (Solve a q) =
>     solved a q


******************************************************************************
Fail
******************************************************************************

> data Fail q = Fail q deriving Show

> instance (Updatable q) => Updatable (Fail q) where
>   upd bull (Fail q) = eta Fail <$> upd bull q

> instance Displayable q => Displayable (Fail q) where
>   display ew ctxt (Fail q) = display ew ctxt q

> instance (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Problem q a)
>           => Problem (Fail q) a where
>   refine (Fail q) =
>     failed


******************************************************************************
Declare
******************************************************************************

> data Declare = Declare UName ObjKind Term deriving Show

> instance Displayable Declare where
>   display ew ctxt (Declare unom ok _) = box (ok,unom)

> instance Updatable Declare where
>   upd bull (Declare unom ok dom) = eta (Declare unom ok) <$> upd bull dom

> instance Problem Declare Term where
>   refine q@(Declare unom@(UN s) ok dom) = do
>     Must b <- okName ok unom
>     if b
>       then do
>         (_,t) <- public s Zip $ declare ok dom
>         popOut . enter . News . story $ UStory unom
>         solved t q
>       else
>         failed


******************************************************************************
Define
******************************************************************************

> data Define = Define UName (Term ::: Term) deriving Show

> instance Displayable Define where
>   display ew ctxt (Define unom _) = box (ObjDefn,unom)

> instance Updatable Define where
>   upd bull (Define unom vt) = eta (Define unom) <$> upd bull vt

> instance Problem Define Term where
>   refine q@(Define unom@(UN s) vt) = do
>     Must b <- okName ObjDefn unom
>     if b
>       then do
>         (_,t) <- public s Zip $ define vt
>         popOut . enter . News . story $ UStory unom
>         solved t q
>       else
>         failed


******************************************************************************
Clear
******************************************************************************

> data Clear = Clear Term deriving Show

> instance Displayable Clear

> instance Updatable Clear where
>   upd bull (Clear t) = eta Clear <$> upd bull t

> instance Problem Clear (Boole LName) where
>   refine q@(Clear t) | Might False == unclear t =
>     solved (BVal True) q
>   refine _ =
>     stuck



******************************************************************************
UnifyIn
******************************************************************************

> data UnifyIn = UnifyIn Term Term Term deriving Show

> instance Displayable UnifyIn

> instance Updatable UnifyIn where
>   upd bull (UnifyIn y s t) =
>     eta UnifyIn <$> upd bull y <$> upd bull s <$> upd bull t

> instance Problem UnifyIn (Boole LName) where
>   refine q@(UnifyIn y s t) =
>     do track (show q) $ return ()
>        Must True <- equalIn Zip y s t
>        solved (BVal True) BOOLE
>     <+> rigid y s t
>     where
>       rigid _ (TF r1) (TF r2) = case (r1,r2) of
>         (Star,Star) -> solved (BVal True) BOOLE
>         (One ,One ) -> solved (BVal True) BOOLE
>         (Only,Only) -> solved (BVal True) BOOLE
>         (Con _ _ nom1 az1,Con _ _ nom2 az2) | nom1 == nom2 -> do
>           Rightmost ty <- get $ varType nom1
>           u <- argsUnify (BVal True) ty ty (az1 <>> nil) (az2 <>> nil)
>           solved u BOOLE
>         (JMEq sy1@(s1 ::: y1) tz1@(t1 ::: z1),
>          JMEq sy2@(s2 ::: y2) tz2@(t2 ::: z2)) -> do
>           u1 <- compute "u" $ UnifyIn star y1 y2
>           u2 <- compute "u" $ HetUnify u1 sy1 sy2
>           u3 <- compute "u" $ UnifyIn star z1 z2
>           u4 <- compute "u" $ HetUnify u3 tz1 tz2
>           solved (u1 `bAnd` u2 `bAnd` u3 `bAnd` u4) BOOLE
>         (JMRefl _,JMRefl _) -> solved (BVal True) BOOLE
>         _ -> track "Die!" $ solved (BVal False) BOOLE
>       rigid (TBind All (unom,NormV) (Sem (Just dom) ran)) f g = do
>         x <- parPush unom dom
>         reduced $ UnifyIn (ran x) (f @@ x) (g @@ x)
>       rigid (TBind b (unom,UnifV) s) f g = do
>         reduced $ UnifyIn (TBind b (unom,NormV) s) (f @@ u_) (g @@ u_)
>       rigid (TF One) _ _ =
>         solved (BVal True) BOOLE
>       rigid (TF Zero) _ _ =
>         solved (BVal True) BOOLE
>       rigid (TF (JMEq _ _)) _ _ =
>         solved (BVal True) BOOLE
>       rigid (TBind Ex (u,NormV) (Sem (Just dom) ran)) f g = do
>         let f1 = f @@ pi1
>         let g1 = g @@ pi1
>         u1 <- compute "u" $ UnifyIn dom f1 g1
>         u2 <- compute "u" $
>                 HetUnify u1 (f @@ pi2 ::: ran f1) (g @@ pi2 ::: ran g1)
>         solved (bAnd u1 u2) BOOLE
>       rigid _ (TBind b1 (unom,v1) (Sem (Just dom1) ran1))  -- not lambda
>         (TBind b2 (_,v2) (Sem (Just dom2) ran2)) | b1 == b2, v1 == v2 = do
>           u1 <- compute "u" $ UnifyIn star dom1 dom2
>           x <- parPush unom dom1
>           reduced $ BWhen u1 (UnifyIn star (ran1 x) (ran2 x))
>       rigid _ (TElim (Var (F x1)) ez1) (TElim (Var (F x2)) ez2)
>         | x1 == x2 = do
>           Rightmost ty <- get $ varType x1
>           u <- spineUnify (BVal True) (TElim (Var (F x1)) Zip ::: ty)
>                  (TElim (Var (F x1)) Zip ::: ty)
>                  (ez1 <>> nil) (ez2 <>> nil)
>           solved u BOOLE
>       rigid _ s t | Might True <- unclear s <+> unclear t =
>         stuck
>       rigid _ _ _ =
>         track "Die!" $ solved (BVal False) BOOLE

>   shock (UnifyIn ty (TElim (Hope x) xez) t)
>     (lz :<: Layer root' del' (ez' :*: es') prob' im'
>         :<: Layer (nom,_) del _ _ _)
>     | seeEnough ty t
>     , Just lz' <- solveFor m0 (moo "SOLVE" (del,((x,xez),t ::: ty)))
>                     (lz :<: Layer root' del' (ez' :*:
>                             News (story (LStory nom (NewBoole (BVal True))))
>                             :>: es')
>                             prob' im')
>     = Just lz'
>   shock (UnifyIn ty t (TElim (Hope x) xez))
>     (lz :<: Layer root' del' (ez' :*: es') prob' im'
>         :<: Layer (nom,_) del _ _ _)
>     | seeEnough ty t
>     , Just lz' <- solveFor m0 (moo "SOLVE" (del,((x,xez),t ::: ty)))
>                     (lz :<: Layer root' del' (ez' :*:
>                             News (story (LStory nom (NewBoole (BVal True))))
>                             :>: es')
>                             prob' im')
>     = Just lz'
>   shock _ _ = m0

> moo :: Show a => String -> a -> a
> moo s x = track (s ++ " " ++ show x) $ x

> seeEnough :: Term -> Term -> Bool
> seeEnough ty t | clearlyNotImplicit t = True
> seeEnough (TF Star) _ = False
> seeEnough ty _ | Might True <- unclear ty = False
> seeEnough _ _ = True

> argsUnify :: Boole LName -> Term -> Term ->
>              List Term -> List Term -> Refine (Boole LName)
> argsUnify (BVal False) _ _ _ _ = return (BVal False)
> argsUnify b _ _ (Tip _) (Tip _) = return (BVal True)
> argsUnify b _ _ (Tip _) _ = return (BVal False)
> argsUnify b _ _ _ (Tip _) = return (BVal False)
> argsUnify b (TBind All (u1,UnifV) dr1) (TBind All (u2,UnifV) dr2)
>   (TF (U_ _) :>: xs) (TF (U_ _) :>: ys) =
>     argsUnify b (TBind All (u1,NormV) dr1) (TBind All (u2,NormV) dr2)
>       xs ys
> argsUnify b (TBind All (_,NormV) (Sem (Just xdom) xran))
>             (TBind All (_,NormV) (Sem (Just ydom) yran))
>             (x :>: xs) (y :>: ys) =
>   case b of
>     BVal True -> do
>       u1 <- compute "u" (UnifyIn xdom x y)
>       eta (u1 <+>) <$> argsUnify u1 (xran x) (xran y) xs ys
>     _ -> do
>       u1 <- compute "u" (HetUnify b (x ::: xdom) (y ::: ydom))
>       u2 <- argsUnify u1 (xran x) (yran y) xs ys
>       return (u1 <+> u2)
> argsUnify _ _ _ _ _ = stuck


I strongly suspect the following of dodginess...

3 Mar 05 Indeed it is; made it lazier

> spineUnify :: (Boole LName) -> (Term ::: Term) -> (Term ::: Term) ->
>               List (Elim Term) -> List (Elim Term) -> Refine (Boole LName)
> spineUnify (BVal False) _ _ _ _ = return (BVal False)
> spineUnify b _ _ (Tip _) (Tip _) = return (BVal True)
> spineUnify b _ _ (Tip _) _ = return (BVal False)
> spineUnify b _ _ _ (Tip _) = return (BVal False)
> spineUnify wait{-(BVal True)-} (t1 ::: ty1) (t2 ::: ty2)
>            (xe :>: xes) (ye :>: yes)
>  = track ("SPU: " ++ show xe ++ " " ++ show ye) $
>   case (ty1,ty2,xe,ye) of
>   (TBind b (unom,UnifV) s1,
>    TBind _ _ s2,
>    A (TF (U_ _)),A (TF (U_ _))) ->
>     spineUnify wait{-(BVal True)-}
>        (t1 @@ u_ ::: TBind b (unom,NormV) s1)
>        (t2 @@ u_ ::: TBind b (unom,NormV) s2)
>        xes yes
>   (TBind All (_,NormV) (Sem (Just dom1) ran1),
>    TBind All (_,NormV) (Sem (Just dom2) ran2),
>    A x,A y) -> do
>     u <- compute "u" $ HetUnify wait (x ::: dom1) (y ::: dom2)
>     --u <- compute "u" {-!!!-} (When wait (UnifyIn dom x y))
>     u'<-
>       spineUnify u (t1 @@ xe ::: ran1 x) (t2 @@ ye ::: ran2 y) xes yes
>     return (u <+> u')
>   (TBind Ex (_,NormV) (Sem (Just dom1) _),
>    TBind Ex (_,NormV) (Sem (Just dom2) _),
>    P1,P1) ->
>     spineUnify wait{-(BVal True)-}
>       (t1 @@ pi1 ::: dom1) (t2 @@ pi1 ::: dom2) xes yes
>   (TBind Ex (_,NormV) (Sem _ ran1),
>    TBind Ex (_,NormV) (Sem _ ran2),
>    P2,P2) ->
>     spineUnify wait {-(BVal True)-} (t1 @@ pi2 ::: ran1 (t1 @@ pi1)) 
>                     (t2 @@ pi2 ::: ran2 (t2 @@ pi1)) xes yes
>   -- more to come
>   _ -> stuck

> solveFor :: (List Entry,Bulletin) ->
>             (Params,((LName,Zip (Elim Term)),Term ::: Term)) ->
>             Ctxt -> Maybe Ctxt
> solveFor _ _ (Zip :<: Layer _ _ (Zip :*: _) _ _) = m0
> solveFor rr uprob ctxt@(_ :<: Layer _ Zip (Zip :*: _) _ _) =
>   solveFor rr uprob (outRight ctxt)
> solveFor (res, rbull) uprob ctxt@(_ :<: Layer _ del (Zip :*: _) _ _) =
>   solveFor (res',rbull' <+> rbull) (del <+> psi',eqn') (outRight ctxt) where
>     (res',rbull') = parametrize del res
>     (psi',eqn') = rbull' <%> uprob
>     -- how did this take so long? is it right?
> solveFor (res,rbull) (psi,((x,xez),psit ::: ty))
>   (lz :<: Layer root del (ez :<: Name (nom,_) (Hoping _ phi _) _ :*: es)
>                 prob im)
>   | nom == x
>   , track (concat ["SOLVE\n",show res,"\n",show rbull,"\n",
>                    show psi,"\n",show (x,xez),"\n",show psit,"\n",
>                    show ty,"\n"]) $ True
>   , Just bull <- etaMatch 0 (phi,TElim (Hope x) Zip @@ phi)
>                             (psi,TElim (Hope x) xez)
>   , track "Bang!" $ True
>   , phit <- bull <%> psit
>   , track (show phi ++ " |- " ++ show phit) $ True
>   , Might False <- dep (nom : (return . key) <!> psi) phit
>   , track "Bong!" $ True
>   , hooray <- story (LStory x (report (phi |- phit))) <+> rbull
>   = return $
>       lz :<: Layer root del (ez :*: res <+> News hooray :>: es) prob im
> solveFor (res,rbull) (psi,((x,xez),psit ::: ty))
>   (lz :<: Layer root del (ez :<: Name (nom,_) (Hoping _ phi _) _ :*: es)
>                 prob im)
>   | nom == x
>   = track "Boo!" $ m0
> solveFor (res,rbull) uprob (lz :<:
>   Layer root del (ez :<: e@(Name (nom,_) _ _) :*: es) prob im)
>   | Might False <- dep [nom] (res,uprob)
>   = solveFor (res,rbull) uprob
>       (lz :<: Layer root del (ez :*: e :>: es) prob im)
> solveFor (res,rbull) uprob (lz :<: Layer root del
>    (ez :<: e@(Name (nom,_) (Object o) _) :*: es) prob im)
>   | parish o
>   , dex <- Zip :<: (nom :=: o)
>   , (res',rbull') <- parametrize dex res
>   , (psi',eqn') <- rbull' <%> uprob
>   = solveFor (res',rbull' <+> rbull) (dex <+> psi',eqn')
>       (lz :<: Layer root del (ez :*: e :>: es) prob im)
> solveFor (res,rbull) uprob (lz :<: Layer root del (ez :<: e :*: es) prob im)
>   | raisable e
>   = solveFor (e :>: res,rbull) uprob
>       (lz :<: Layer root del (ez :*: es) prob im)
>   | otherwise = track ("Hiss! " ++ show e) $ m0
> solveFor _ _ _ = m0


> etaMatch :: Int -> (Params,Term) -> (Params,Term) -> Maybe Bulletin
> etaMatch i (del,u) (del',TF Only) = return m0
> etaMatch i (del,u) (del',TF (Pair NormV x y)) =
>   do sbx <- etaMatch i (del,u @@ pi1) (del',x)
>      sby <- etaMatch i (del,u @@ pi2) (del',sbx <%> y)
>      return (sbx <+> sby)
> etaMatch i (del,u) (del',TF (Pair UnifV x y)) =
>   do sbx <- etaMatch i (del,u @@ u_ @@ pi1) (del',x)
>      sby <- etaMatch i (del,u @@ u_ @@ pi2) (del',sbx <%> y)
>      return (sbx <+> sby)
> etaMatch i (del,u) (del',TBind Lam (unom,NormV) (Sem _ r)) =
>   let a = var i unom
>   in  etaMatch (i + 1) (del,u @@ a) (del',r a)
> etaMatch i (del,u) (del',TBind Lam (unom,UnifV) (Sem _ r)) =
>   let a = var i unom
>   in  etaMatch (i + 1) (del,u @@ u_ @@ a) (del',r a)
> etaMatch i (del,TElim h (ez :<: e)) (del',TElim h' (ez' :<: e')) =
>   do sb <- etaMatch i (del,TElim h ez) (del',TElim h' ez')
>      case (e,e') of
>        (A (TF (U_ _)),A (TF (U_ _))) -> return sb
>        (P1,P1) -> return sb
>        (P2,P2) -> return sb
>        (A a,A a') ->
>          do sba <- etaMatch i (del,a) (del',sb <%> a')
>             return (sb <+> sba)
>        _ -> m0
> etaMatch i (del,TElim h Zip) (del',TElim h' Zip)
>   | case (h,h') of
>       (Var x,Var x') -> x == x'
>       (Hope x,Hope x') -> x == x'
>       (Wait x,Wait x') -> x == x'
>       _ -> False
>   = return m0
> etaMatch i (del,u) (del',TElim (Var (F x)) Zip)
>   | Might True <- (\ (nom :=: _) -> Might (nom == x)) <!> del'
>   = return (story (LStory x (report u)))
> etaMatch _ _ _ = m0






******************************************************************************
HetUnify
******************************************************************************

> data HetUnify = HetUnify (Boole LName) (Term ::: Term) (Term ::: Term)
>   deriving Show

> instance Displayable HetUnify

> instance Updatable HetUnify where
>   upd bull (HetUnify gd sS tT) =
>     eta HetUnify <$> upd bull gd <$> upd bull sS <$> upd bull tT

> instance Problem HetUnify (Boole LName) where
>   refine (HetUnify (BVal False) _ _) =
>     solved (BVal False) BOOLE
>   refine (HetUnify (BVal True) (s ::: sty) (t ::: tty)) = do
>     -- short cut to   Must True <- equalIn Zip star sty tty
>     reduced $ UnifyIn sty s t
>   refine (HetUnify _ (s ::: sty) (t ::: tty)) = do
>     Must True <- equalIn Zip star sty tty
>     reduced $ UnifyIn sty s t



******************************************************************************
KnotRec
******************************************************************************

> data KnotRec = KnotRec (Term ::: Term) deriving Show

> instance Displayable KnotRec

> instance Updatable KnotRec where
>   upd bull (KnotRec tty) = eta KnotRec <$> upd bull tty

> instance Problem KnotRec Term where
>   probType (KnotRec (_ ::: ty)) = ty
>   refine q@(KnotRec (tm ::: gy)) =
>     do False <- get recActive
>        solved tm q
>     <+>
>     case tm of
>       TElim (Var (F nom)) ez ->
>         do Rightmost (unom :=: (ObjRec,_ ::: _)) <- get $ varObj nom
>            Just (cez,lab,rez) <- return $ callSplit ez
>            ty <- typeSpine Zip (Var (F nom)) cez
>            rec <- compute "rec" $ SpotRec (lab ::: ty)
>            solved (rec @@ Call lab @@ rez) q
>         <+>
>         solved tm q
>       TBind Lam (unom,v) (Sem _{-dom-} ran) ->
>         do TBind All _ (Sem (Just dom) rant) <- return gy
>            a <- lamPush v unom dom
>            reduced $ KnotRec (ran a ::: rant a)
>       TElim _ _ -> stuck
>       _ -> solved tm q
>     where
>       recActive Zip = False
>       recActive (Zip :<: Layer _ _ (ez :*: _) _ _) = rA ez where
>         rA (ez :<: Name (Long (Zip :<: ("Gap",_)),_) _ _) = False
>         rA (ez :<: Name _ (Object (_ :=: (ObjRec,_))) _) = True
>         rA (ez :<: e) = rA ez
>         rA Zip = False
>       recActive (lz :<: l) = recActive lz
>       callSplit :: Zip (Elim Term) ->
>         Maybe (Zip (Elim Term),Label Term,Zip (Elim Term))
>       callSplit (ez :<: e)
>         | Just (cez,lab,rez) <- callSplit ez
>         = Just (cez,lab,rez :<: e)
>       callSplit (cez :<: Call lab) = Just (cez,lab,Zip)
>       callSplit _ = Nothing





******************************************************************************
SpotRec
******************************************************************************

> data SpotRec = SpotRec ((Label Term) ::: Term) deriving Show

> instance Displayable SpotRec

> instance Updatable SpotRec where
>   upd bull (SpotRec t) = eta SpotRec <$> upd bull t

> instance Problem SpotRec Term where
>   probType (SpotRec (lab ::: ty)) = TF (Lbl LabTy lab ty)
>   refine (SpotRec (lab ::: ty)) | Label (f ::: _) _ _ <- lab = do
>     lz <- get id
>     cz <- try f lz
>     r <- compute "r" $ Candidates cz prob
>     reduced $ NotBot r prob
>     where
>       prob = TF (Lbl LabTy lab ty)
>       try f Zip = return Zip
>       try f (lz :<: Layer _ del (ez :*: _) _ _) = lay lz del ez where
>         lay lz Zip Zip = try f lz
>         lay lz del (ez :<: e)
>           | Name _ (Object (nam :=: (ObjRec,_))) _ <- e
>           = if f == nam then return Zip else lay lz del ez
>           | Name _ (Object (_ :=: (_,tmty))) _ <- e = do
>             cz <- lay lz del ez
>             c <- compute "b" $ Blunderbuss tmty prob
>             return (cz :<: c)
>           | otherwise = lay lz del ez
>         lay lz (del :<: p) Zip
>           | _ :=: nam :=: (ObjRec,_) <- p
>           = if f == nam then return Zip else lay lz del Zip
>           | _ :=: _ :=: (_,tmty) <- p = do
>             cz <- lay lz del Zip
>             c <- compute "b" $ Blunderbuss tmty prob
>             return (cz :<: c)
>           | otherwise = lay lz del Zip


> data NotBot = NotBot Term Term deriving Show

> instance Displayable NotBot

> instance Updatable NotBot where
>   upd bull (NotBot t y) = eta NotBot <$> upd bull t <$> upd bull y

> instance Problem NotBot Term where
>   probType (NotBot t y) = y
>   refine (NotBot (TF Bot) y) = failed
>   refine q@(NotBot t y) | Might False <- unclear t = solved t q
>   refine _ = stuck

> data Candidates = Candidates (Zip Term) Term deriving Show

> instance Displayable Candidates

> instance Updatable Candidates where
>   upd bull (Candidates cz y) = eta Candidates <$> upd bull cz <$> upd bull y

> instance Problem Candidates Term where
>   probType (Candidates _ y) = y
>   refine q@(Candidates cz y) =
>     case chk cz of
>       Just t -> solved t q
>       Nothing -> stuck
>     where
>       chk Zip = Just (TF Bot)
>       chk (cz :<: c) =
>         case (chk cz,c,unclear c) of
>           (Just t,TF Bot,_) -> Just t
>           (Nothing,TF Bot,_) -> Nothing
>           (Just (TF Bot),c,Might True) -> Nothing
>           (m,c,Might True) -> m
>           (m,c,_) -> Just c


> data Blunderbuss = Blunderbuss (Term ::: Term) Term deriving Show

> instance Displayable Blunderbuss

> instance Updatable Blunderbuss where
>   upd bull (Blunderbuss tty y) =
>     eta Blunderbuss <$> upd bull tty <$> upd bull y

> instance Problem Blunderbuss Term where
>   probType (Blunderbuss _ y) = y

>   refine q@(Blunderbuss (tm ::: ty) y) = track (show q) $
>    case ty of
>     TBind b (u,UnifV) dr ->
>       reduced (Blunderbuss (tm @@ u_ ::: TBind b (u,NormV) dr) y)
>     TBind Ex (u,NormV) (Sem (Just dom) ran) -> do
>       c1 <- compute "b" $ Blunderbuss (tm @@ pi1 ::: dom) y
>       c2 <- compute "b" $ Blunderbuss (tm @@ pi2 ::: ran (tm @@ pi1)) y
>       reduced (Candidates (Zip :<: c1 :<: c2) y)
>     TBind All (_,NormV)
>      (Sem (Just dom@(TF (JMEq (s ::: sy) (t ::: ty)))) ran)
>       -> do
>       (_,u1) <- private "U" Zip . await (Compute,QTerm) $
>         UnifyIn star sy ty
>       (_,u2) <- private "u" Zip . await (Compute,QTerm) $
>         HetUnify u1 (s ::: sy) (t ::: ty)
>       (_,q) <- private "q" Zip . await (Compute,QTerm) $
>         When (u1 <+> u2) (Candidates (zOne (TF (JMRefl (s ::: sy)))) dom)
>       (_,c) <- private "b" Zip . await (Compute,QTerm) $
>         Blunderbuss (tm @@ q ::: ran q) y
>       reduced (Candidates (Zip :<: c) y)
>     TBind All (UN s,NormV) (Sem (Just dom) ran) -> do
>       (_,x) <- private s Zip $ hope dom
>       (_,c) <- private "b" Zip . await (Compute,QTerm) $
>         Blunderbuss (tm @@ x ::: ran x) y
>       reduced (Candidates (Zip :<: c) y)
>     TF (Lbl LabTy (Label (f ::: _) az Zip) ty) ->
>       case y of
>         TF (Lbl LabTy (Label (f' ::: fty) az' Zip) ty') | f == f' -> do
>           -- temporarily
>           b <- argsUnify (BVal True) fty fty (az <>> nil) (az' <>> nil)
>           reduced $ CondCand b tm y
>         _ -> solved (TF Bot) q
>     _ | Might True <- unclear ty -> stuck
>     _ -> solved (TF Bot) q

> data CondCand = CondCand (Boole LName) Term Term deriving Show

> instance Displayable CondCand

> instance Updatable CondCand where
>   upd bull (CondCand b t y) =
>     eta CondCand <$> upd bull b <$> upd bull t <$> upd bull y

> instance Problem CondCand Term where
>   probType (CondCand _ _ y) = y
>   refine q@(CondCand (BVal True) t _) = solved t q
>   refine q@(CondCand (BVal False) _ _) = solved (TF Bot) q
>   refine _ = stuck
