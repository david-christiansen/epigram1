******************************************************************************
**********                                                          **********
**********     Elimination with a motive                            **********
**********                                                          **********
******************************************************************************

> module Ewam where

> import Name
> import ObjKind
> import Zip
> import Category
> import Monadics
> import Logic

> import Term
> import Equality
> import Update
> import Igor

> -- import Debug.Trace
> import Utils

> type Goal = Root :=: (Params,Term)

A tactic returns a bunch of subgoals, and a term over the original params

> type Tactic = Goal -> Refine (Zip Goal,Term)

> ewam :: (Param -> Might) -> (Term ::: Term) -> [LName] -> Tactic
> ewam fixy (el ::: elty) clears (root@(roo,_) :=: (del,gy)) = do
>   track ("GOAL: " ++ show del ++ " |= " ++ show gy) $ return ()
>   TBind All (_,NormV) (Sem (Just moTy) moRan) <- return elty
>   nP <- return $ roo /// "P"
>   ((pP,vP),methoTy) <- return $ nP .| elty
>   (aperture,TF Star) <- return $ (roo,"i") -| moTy
>   let theta = pLam aperture
>   (rawMethTz,rt) <- return $ (roo,"m") -| methoTy
>   (TElim (Var (F monom)) Zip,targs) <- return $ unapplies rt
>   ensure $ monom == nP
>   Might False <- return $ hOpen 0 <!> targs
>   let mometh = ((: []) . parTy) <!> (theta <+> rawMethTz)
>   Might False <- return $ hOpen 0 <!> mometh
>   (delFix,delVary) <- return $
>     depSplit mometh fixy (pAll . pShow $ del)
>   track ("DEP: " ++ show mometh) $ return ()
>   track ("FIX: " ++ show delFix) $ return ()
>   track ("VARY: " ++ show delVary) $ return ()
>   let rawEqsRs = constrain 0 (theta <>> nil) (moTy,targs)
>   track ("RAW: " ++ show rawEqsRs) $ return ()
>   let delVaRaw = up (\ p -> (p,parVal p)) delVary
>   (delVaCooked,gyCooked) <- cook (delFix <+> theta) delVaRaw m0 rawEqsRs gy
>   track ("COOKED: " ++ show delVaCooked ++ " |- " ++ show gyCooked) $
>     return ()
>   delVaCleared <- return $ clear (nodep gyCooked <!> clears) delVaCooked
>   let moDel  = eta fst <$> delVaCleared
>   let elArgz = eta snd <$> delVaCleared
>   let motive = (theta <+> moDel) |- gyCooked
>   track ("EWAM: " ++ show motive) $ return ()
>   let methTz = story (LStory nP (report motive)) <%> rawMethTz
>   (subgz,methodz,_) <- subgoals delFix methTz
>   track ("SUBGZ: " ++ show subgz) $ return ()
>   let whammo = el @@ motive @@ methodz @@ elArgz
>   track ("WHAMMO: " ++ show whammo) $ return ()
>   return (subgz,whammo)
>   where

>     constrain :: Int -> List Param -> (Term,List Term) ->
>                  List (Param,Term)
>     constrain i ps (TBind All (u,UnifV) dr,TF (U_ _) :>: ts) =
>       constrain i ps (TBind All (u,NormV) dr,ts)
>     constrain i (p :>: ps)
>                 (TBind All (u,NormV) (Sem (Just dom) ran),t :>: ts) =
>       (fst $ decl (roo /// ("q",i)) (UN "q") All NormV
>         (TF (JMEq (parVal p ::: parTy p) (t ::: dom))) :: Param,
>         TF (JMRefl (t ::: dom)) :: Term)
>       :>: constrain (i + 1) ps (ran t,ts)
>     constrain _ _ _ = nil

>     cook :: Params -> (Zip (Param,Term)) -> Bulletin ->
>             List (Param,Term) -> Term ->
>             Refine (Zip (Param,Term),Term)
>     cook fixed delVaz bull (Tip _) ty = return (delVaz,bull <%> ty)
>     cook fixed delVaz bull ((q,r) :>: qrs) gy
>       | q'@(_ :=: _ :=: (_,_ ::: qt)) <- bull <%> q =
>       do TF (JMEq (s ::: sy) (TElim (Var (F nom)) Zip ::: ty)) <- return qt
>          Must True <- equalIn (fixed <+> (eta fst <$> delVaz)) star sy ty
>          (delVaz',bull') <- boil nom s delVaz
>          cook fixed delVaz' (bull' <+> bull) qrs gy
>       <+>
>       cook fixed (delVaz :<: (q',r)) bull qrs gy

>     boil :: LName -> Term -> Zip (Param,Term) ->
>             Refine (Zip (Param,Term),Bulletin)
>     boil nom tm (delaz :<: (nam :=: _,_)) | nom == nam
>       = return (delaz,story (LStory nom (report tm)))
>     boil nom tm (delaz :<: (p,a)) = do
>       (delaz',bull) <- boil nom tm delaz
>       return (delaz' :<: (bull <%> p,a),bull)
>     boil _ _ _ = doo m0

>     nodep :: Term -> LName -> [LName]
>     nodep ty nom | Might True <- dep [nom] ty = []
>     nodep _ nom = [nom]
>     clear :: [LName] -> Zip (Param,Term) -> Zip (Param,Term)
>     clear _ Zip = Zip
>     clear clears (pz :<: (nom :=: _,_)) | elem nom clears = clear clears pz
>     clear clears (pz :<: pt@(p,_)) =
>       clear (nodep (parTy p) <!> clears) pz :<: pt

>     subgoals :: Params -> Params ->
>                   Refine (Zip Goal,Zip Term,Bulletin)
>     subgoals rover Zip = return (Zip,Zip,m0)
>     subgoals rover (pz :<: p) = do
>       (subz,mz,bull) <- subgoals rover pz
>       (nom :=: unom :=: (ObjAbst All vis,mtm ::: mty)) <- return p
>       let (del',ty') = (nom,"x") -| bull <%> mty
>       let root' = (nom,const 1 <!> del')
>       return (
>         subz :<: (root' :=: (rover <+> del',ty')),
>         mz :<: mtm @@ rover,
>         bull <+> raiser nom star rover
>         )

> labial :: UName -> Int -> Term -> Might
> labial uno i (TBind Ex (u, _) (Sem (Just dom) ran)) =
>   labial uno (i + 1) (ran (var i u)) <+> labial uno i dom
> labial uno i (TBind _ (u, _) (Sem dom ran)) = labial uno i (ran (var i u))
> labial uno _ (TF (Lbl LabTy (Label (u ::: _) _ _) _)) = Might (uno == u)
> labial uno i (TF tm) = labial uno i <!> tm
> labial uno i (TElim _ ez) = (labial uno i <!>) <!> ez


 ewam :: (Param -> Might) -> (Term ::: Term) -> [LName] -> Tactic
 ewam fixy (el ::: elty) clears (root@(roo,_) :=: (del,ty)) = do
   TBind All (_,NormV) _ <- return elty
   nP <- return $ roo /// "P"
   ((pP,vP),mm) <- return $ nP .| elty
   tP <- return $ parTy pP
   (theta,TF Star) <- return $ (roo,"i") -| tP
   (psi,rt) <- return $ (roo,"m") -| mm
   (TElim (Var (F monom)) Zip,targs) <- return $ unapplies rt
   ensure $ monom == nP
   (delFix,delVary) <- return $
     depSplit ((return . parTy) <!> (theta <+> psi)) fixy
       (pAll del)
   let delQC = delFix <+> theta
   (delVary',(delEqns,reflz),ty') <-
     constrain delQC 0 delVary m0 m0 (theta <>> nil,tP,tP,targs) ty
   delVary'' <- return $ clear (nodep ty <!> clears) delVary'
   motive <- return $ (pLam theta <+> delVary'' <+> delEqns) |- ty'
   track ("EWAM: " ++ show motive) $ return ()
   (subz,vmz,_) <- subgoals delFix (story (LStory nP (report motive))) psi
   track ("SUBGOALS\n" ++ show subz) $ return ()
   return (subz,el @@ motive @@ vmz @@ delVary'' @@ reflz)
   where
     constrain :: Params -> Int -> Params -> (Params,Zip Term) -> Bulletin ->
                  (List Param,Term,Term,List Term) -> Term ->
                  Refine (Params,(Params,Zip Term),Term)
     constrain qc j delV delQrz bull (Tip _,_,_,Tip _) ty =
       return (delV,delQrz,bull <%> ty)
     constrain qc j delV (delQ,rz) bull
       (is,TBind All (u',UnifV) tdr',TBind All (u,UnifV) tdr,TF U_ :>: ts)
       ty =
       constrain qc j delV (delQ,rz) bull
         (is,TBind All (u',NormV) tdr',TBind All (u,NormV) tdr,ts) ty
     constrain qc j delV (delQ,rz) bull
       (i :>: is,TBind All (_,NormV) (Sem tdom' tran'),
                 TBind All (_,NormV) (Sem tdom tran),t :>: ts) ty = do
       (inom :=: iun :=: (ObjAbst All ivis,itm ::: ity)) <- return i
       t' <- return $ bull <%> t
       (<+>)
         (do TElim (Var (F nom)) Zip <- return t'
             Must True <- equalIn qc star ity tdom'
             let bull' = story (LStory nom (report itm))
             delV' <- dontNeed nom bull' delV
             constrain qc j delV' (delQ,rz) (bull <+> bull')
               (is,tran' itm,tran t,ts) ty)
         (do (pQ,_) <- return . decl (roo /// ("q",j)) (UN "q") All NormV
                         $ TF (JMEq (itm ::: ity) (t' ::: tdom'))
             constrain qc (j + 1) delV
               (delQ :<: pQ,rz :<: TF (JMRefl (t ::: tdom)))
                bull (is,tran' t',tran t,ts) ty)
     constrain _ _ _ _ _ _ _ = doo m0
     dontNeed :: LName -> Bulletin -> Params -> Refine Params
     dontNeed _ _ Zip = doo m0
     dontNeed nom b (del :<: (nam :=: _)) | nom == nam = return del
     dontNeed nom b (del :<: p) = eta (:<: b <%> p) <$> dontNeed nom b del
     nodep :: Term -> LName -> [LName]
     nodep ty nom | Might True <- dep [nom] ty = []
     nodep _ nom = [nom]
     clear :: [LName] -> Params -> Params
     clear _ Zip = Zip
     clear clears (pz :<: (nom :=: _)) | elem nom clears = clear clears pz
     clear clears (pz :<: p) = clear (nodep (parTy p) <!> clears) pz :<: p
     subgoals :: Params -> Bulletin -> Params ->
                   Refine (Zip Goal,Zip Term,Bulletin)
     subgoals rover bull Zip = return (Zip,Zip,bull)
     subgoals rover bull (pz :<: p) = do
       (subz,mz,bull') <- subgoals rover bull pz
       (nom :=: unom :=: (ObjAbst All vis,mtm ::: mty)) <- return p
       let (del',ty') = (nom,"x") -| bull <%> mty
       let root' = (nom,const 1 <!> del')
       return (
         subz :<: (root' :=: (rover <+> del',ty')),
         mz :<: mtm @@ rover,
         bull <+> raiser nom star rover
         )


> simpTrivial :: Tactic --- Ks all the reflexive hyps
> simpTrivial (root@(gnom,_) :=: (del,gy)) = boom Zip m0 (del <>> nil) where
>   boom :: Params -> Bulletin -> List Param -> Refine (Zip Goal,Term)
>   boom del' bull (Tip _) = case bull of
>     Bulletin Zip -> doo m0
>     _ -> return (zOne (root :=: (del',bull <%> gy)),nmTm gnom @@ del')
>   boom pz bull (p :>: ps) = case (bull <%> p) of
>     p'@(qnom :=: _ :=: (_,_ ::: TF (JMEq (s ::: sy) (t ::: ty)))) ->
>       do Must True <- equalIn del star sy ty
>          Must True <- equalIn del sy s t
>          boom pz (bull <+>
>                   story (LStory qnom (report (TF (JMRefl (s ::: sy)))))) ps
>       <+>
>       boom (pz :<: p') bull ps
>     p' -> boom (pz :<: p') bull ps

> simpPeano :: Tactic --- go for the constructor eqns
> simpPeano goal@(_ :=: (del,gy)) = boom (del <>> nil) where
>   boom ((qn :=: _ :=: (_,qv ::: qt)) :>: moo)
>     | TF (JMEq (TF (Con (DataCon _) u1 _ az1) ::: TF (Con TypeCon _ _ _))
>                (TF (Con (DataCon _) u2 _ az2) ::: TF (Con TypeCon _ _ _)))
>       <- qt
>     , Might False <- dep [qn] moo <+> dep [qn] gy
>     = do e <- if u1 == u2
>            then eta (JMCon . Just . parTy) <$> seekUName u1
>            else eta (JMCon Nothing)
>          let etty = (qv ::: qt) @@ e
>          ewam m0 etty [qn] goal
>     | otherwise = boom moo
>   boom _ = doo m0

> majorElim :: Params -> (Term ::: Term) -> Refine (Term ::: Term)
> majorElim del (prf ::: TF (JMEq ssy@(s ::: sy) (t ::: ty))) = do
>   Must True <- equalIn del star sy ty
>   return $
>     (TBind Lam (UN "P",NormV) . Sem Nothing{-motive-} $ \ p ->
>      TBind Lam (UN "m",NormV) . Sem Nothing{-(method p)-} $ \ m ->
>      prf @@ JMResp (predicate p) @@ (JMCoe :: JMElim Term)
>        @@ TBind Lam dull (Sem Nothing{-(TF (JMEq ssy ssy))-} (const m))
>        @@ prf)
>     :::
>     (TBind All (UN "P",NormV) . Sem (Just motive) $ \ p ->
>      TBind All (UN "m",NormV) . Sem (Just (method p)) $ \ m ->
>      p @@ t @@ prf)
>   where
>     motive :: Term
>     motive = TBind All (UN "x",NormV) . Sem (Just ty) $ \ x ->
>              TBind All (UN "q",NormV) .
>                Sem (Just (TF (JMEq (s ::: sy) (x ::: ty)))) $ \ q ->
>              star
>     method :: Term -> Term
>     method p = p @@ s @@ TF (JMRefl (s ::: sy))
>     predicate :: Term -> (Term ::: Term)
>     predicate p =
>       (TBind Lam (UN "x",NormV) . Sem Nothing{-sy-} $ \ x ->
>        TBind All (UN "q",NormV) .
>          Sem (Just (TF (JMEq (s ::: sy) (x ::: ty)))) $ \ q ->
>        p @@ x @@ q)
>       :::
>       (TBind All (UN "x",NormV) $ Sem (Just sy) (const star))

> majorJ :: Params -> (Term ::: Term) -> Refine (Term ::: Term)
> majorJ del (prf ::: TF (JMEq ssy@(s ::: sy) (t ::: ty))) = do
>   Must True <- equalIn del star sy ty
>   return $
>     (TBind Lam (UN "P",NormV) . Sem Nothing{-motive-} $ \ p ->
>      prf @@ JMResp (p ::: motive) @@ (JMCoe :: JMElim Term))
>     :::
>     (TBind All (UN "P",NormV) . Sem (Just motive) $ \ p ->
>      TBind All (UN "m",NormV) . Sem (Just (p @@ s)) $ \ m ->
>      p @@ t)
>   where
>     motive = TBind All (UN "x",NormV) . Sem (Just ty) $ \ x -> star

> simpSubst :: Tactic --- eliminate variables
> simpSubst goal@(_ :=: (del,gy)) = boom (del <>> nil) where
>   boom (Tip _) = doo m0
>   boom ((qn :=: _ :=: (_,qvt@(qv ::: qt))) :>: moo) =
>     do TF (JMEq tty (TElim (Var (F x)) Zip ::: ty1)) <- return qt
>        boing (x ::: ty1) tty qn qvt moo
>     <+>
>     do TF (JMEq (TElim (Var (F x)) Zip ::: ty1) tty) <- return qt
>        boing (x ::: ty1) tty qn (qvt @@ (JMSym :: JMElim Term)) moo
>     <+>
>     boom moo
>   boing (x ::: ty1) tty@(t ::: ty2) qn qvt moo = do
>     Rightmost _ <- return $ zAssoc del x       -- it's local
>     Might False <- return $ dep [x] t          -- occur check
>     Might False <- return $ dep [qn] gy        -- q not explicit in prob
>     etty <- if un (dep [qn] moo) then majorElim del qvt else majorJ del qvt
>     ewam m0 etty [qn] goal



> tacBull :: Tactic -> Goal -> Refine (Zip Goal,Bulletin)
> tacBull tac goal@((gnom,_) :=: (del,_)) =
>   do (subgz,sol) <- tac goal
>      return (subgz,story (LStory gnom (report (pLam del |- sol))))
>   <+>
>   return (zOne goal,m0)

> tacBullz :: Tactic -> Zip Goal -> Refine (Zip Goal,Bulletin)
> tacBullz tac Zip = return (Zip,m0)
> tacBullz tac (gz :<: g) = do
>   (gz',bull) <- tacBullz tac gz
>   (g',bull') <- tacBull tac (bull <%> g)
>   return (gz' <+> g',bull <+> bull')

> onSubgoals :: Tactic -> (Zip Goal,Term) -> Refine (Zip Goal,Term)
> onSubgoals tac (gz,tm) = do
>   (gz',bull) <- tacBullz tac gz
>   return (gz',bull <%> tm)

> simpEquation :: Tactic
> simpEquation = simpTrivial <+> simpPeano <+> simpSubst

> simpUnify :: Tactic
> simpUnify goal = simpEquation goal >>= onSubgoals simpUnify

> packRefinement :: (Zip Goal,Term) -> Refine Term
> packRefinement (gz,tm) = do
>   (snom,_) <- child "S"
>   let glom :: Zip Goal -> (Params,Term,Bulletin)
>       glom Zip = (Zip,nmTm snom,m0)
>       glom (gz :<: ((nom,_) :=: (del,ty)))
>         | (pz,tuple,bull) <- glom gz
>         , dt <- bull <%> del |- bull <%> ty
>         = (pz :<: (nom :=: UN "G" :=: (ObjAbst Ex NormV,(nmTm nom ::: dt))),
>            tuple @@ pi2,
>            bull <+> story (LStory nom (report (tuple @@ pi1))))
>   let (pz,_,bull) = glom gz
>   let sub = pz |- TF One
>   let sol = bull <%> tm
>   return . pair sub $
>     zOne (snom :=: UN "g" :=: (ObjAbst Lam NormV,nmTm snom ::: sub)) |- sol
