******************************************************************************
**********                                                          **********
**********     Gadgets.lhs --- computation for data                 **********
**********                                                          **********
******************************************************************************

> module Gadgets where

> import Utils
> import Category
> import Monadics
> import Zip
> import Name
> import Update
> import Logic
> import Igor
> import Term
> import ObjKind

> -- import Debug.Trace


******************************************************************************
Interface
******************************************************************************

> makeGadgets :: Term -> Refine (UName,[Gadget])
> makeGadgets (TF (Pair _ (TF (Con TypeCon ufam _ _)) cons)) = do
>   famP <- seekUName ufam
>   cPz <- seekCons cons
>   let uroot = UN (rootName ((recNames 0 . parTy) <!> cPz))
>   let fc = (uroot,famP,cPz)
>   let caseG = makeCase (track (";UROOT " ++ show uroot) fc)
>   let viewG = makeView fc
>   let memoG = makeMemo fc
>   let genG  = makeGen fc memoG
>   let recG  = makeRec fc memoG genG
>   return (ufam,[caseG,viewG,memoG,genG,recG])
>   where
>     seekCons (TF Only) = return Zip
>     seekCons (TF (Pair _ cons (TF (Con (DataCon _) ucon _ _)))) =
>       eta (:<:) <$> seekCons cons <$> seekUName ucon
>     seekCons _ = doo m0
>     recNames i (TBind All (u@(UN s), _) (Sem (Just dom) ran)) =
>       (if isRec i dom then [s] else []) ++ recNames (i + 1) (ran (var i u))
>     recNames _ _ = []
>     isRec i (TBind All (u, _) (Sem _ ran)) = isRec (i + 1) (ran (var i u))
>     isRec i (TF (Con TypeCon u _ _)) = u == ufam
>     isRec _ _ = False
> makeGadgets _ = doo m0

> gCase :: [(UName,Zip Term -> Zip Term -> Term)] ->
>          Zip Term -> Term -> Maybe Term
> gCase ucs iz (TF (Con _ unom _ az))
>   | Just f <- lookup unom ucs = Just (f iz az)
> gCase _ _ _ = Nothing


******************************************************************************
The namespace for gadget manufacture
******************************************************************************

> voon :: LName
> voon = Long (Zip :<: ("Voodoo",0))


******************************************************************************
Case Analysis
******************************************************************************

> makeCase :: (UName,Param,Params) -> Gadget
> makeCase (uroot,nF :=: uF :=: (_,vF ::: tF),cPz) = caseGadget
>   where
>     caseGadget = Gadget
>       {gKind = ICase, gType = caseType, gElim = gCase (caseBranch <!> cPz)}
>     caseType iz x = caseT @@ iz @@ x
>     caseT =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") uroot All NormV $ vF @@ indz
>           aperture  = pHide indz :<: px
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV
>                         $ aperture |- star
>           method :: Param -> Param
>           method (nC :=: UN s :=: (_,vC ::: tC)) =
>             let mnom = (voon /// "m" /// s)
>                 (az,TF (Con _ _ _ iz)) = (mnom,"a") -| tC
>             in  fst . decl mnom (UN ("m'" ++ s)) All NormV $
>                   az |- vP @@ (iz :<: (vC @@ az) ::: aperture)
>       in  (pLam (indz :<: px) <+>
>            zOne pP <+> up method cPz)
>           |- vP @@ aperture
>     caseBranch (nC :=: uC :=: (_,vC ::: tC)) =
>       [(uC,\ iz az -> branch @@ az)] where
>         (az,TF (Con _ _ _ iz)) = (voon,"a") -| tC
>         ((pP,vP),mm) = (voon /// "P") .| caseType iz (vC @@ az)
>         (methz,_) = (voon,"m") -| mm
>         pick (_ :<: (nam :=: _)) (_ :<: p) | nC == nam = parVal p
>         pick (cPz :<: _) (pz :<: _) = pick cPz pz
>         branch = pLam ((az :<: pP) <+> methz) |- pick cPz methz @@ az


******************************************************************************
View Analysis
******************************************************************************

> makeView :: (UName,Param,Params) -> Gadget
> makeView (uroot,nF :=: uF :=: (_,vF ::: tF),cPz) = viewGadget
>   where
>     viewGadget = Gadget
>       {gKind = IView, gType = viewType, gElim = gCase (viewBranch <!> cPz)}
>     viewType iz x = viewT @@ iz @@ x
>     viewT =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") uroot All NormV $ vF @@ indz
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV $ indz |- star
>           method :: Param -> Param
>           method (nC :=: UN s :=: (_,vC ::: tC)) =
>             let mnom = (voon /// "m" /// s)
>                 (az,TF (Con _ _ _ iz)) = (mnom,"a") -| tC
>                 hyp :: Param -> Zip Param
>                 hyp (nA :=: UN s :=: (_,vA ::: tA)) =
>                   case (nA,"b") -| tA of
>                     (hoaz,TF (Con TypeCon u _ hiz)) | u == uF -> zOne . fst .
>                       decl (nA /// "h") (UN ("h'" ++ s)) All NormV
>                         $ hoaz |- vP @@ hiz
>                     _ -> Zip
>             in  fst . decl mnom (UN ("m'" ++ s)) All NormV $
>                   (az <+> hyp <!> az) |- vP @@ iz
>       in  (pLam (indz :<: px) <+>
>            zOne pP <+> up method cPz)
>           |- vP @@ indz
>     viewBranch (nC :=: uC :=: (_,vC ::: tC)) =
>       [(uC,\ iz az -> branch @@ az)] where
>         (az,TF (Con _ _ _ iz)) = (voon,"a") -| tC
>         ((pP,vP),mm) = (voon /// "P") .| viewType iz (vC @@ az)
>         (methz,_) = (voon,"m") -| mm
>         pick (_ :<: (nam :=: _)) (_ :<: p) | nC == nam = parVal p
>         pick (cPz :<: _) (pz :<: _) = pick cPz pz
>         recce :: Param -> Zip Term
>         recce (nA :=: UN s :=: (_,vA ::: tA)) =
>           case (nA,"b") -| tA of
>             (hoaz,TF (Con TypeCon u _ hiz)) | u == uF -> zOne $
>               pLam hoaz |- vA @@ hoaz @@ Ind viewGadget hiz @@ vP @@ methz
>             _ -> Zip
>         branch = pLam ((az :<: pP) <+> methz)
>                  |- pick cPz methz @@ az @@ (recce <!> az)


******************************************************************************
Memoization
******************************************************************************

> makeMemo :: (UName,Param,Params) -> Gadget
> makeMemo (uroot,nF :=: uF :=: (_,vF ::: tF),cPz) = memoGadget
>   where
>     memoType iz x = memoT @@ iz @@ x
>     memoT =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") uroot All NormV $ vF @@ indz
>           aperture  = pHide indz :<: px
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV
>                         $ aperture |- star
>       in  pLam (indz :<: px) :<: pP |- star
>     memoBranch (nC :=: uC :=: (_,vC ::: tC)) =
>       [(uC,\ iz az -> branch @@ az)] where
>         (az,TF (Con _ _ _ iz)) = (voon,"a") -| tC
>         ((pP,vP),_) = (voon /// "P") .| memoType iz (vC @@ az)
>         (aperture,_) = (voon,"i") -| parTy pP
>         memoize :: Param -> Params
>         memoize (nA :=: UN s :=: (_,vA ::: tA)) =
>           case (nA,"b") -| tA of
>             (hoaz,TF (Con TypeCon u _ hiz)) | u == uF -> zOne . fst .
>               decl (nA /// "rm") (UN ("rm'" ++ s)) Ex NormV .
>                 (hoaz |-) .
>                 TBind Ex (UN ("r'" ++ s),NormV) $ Sem
>                   (Just (vA @@ hoaz @@ Ind memoGadget hiz @@ vP))
>                   (const (vP @@ (hiz :<: (vA @@ hoaz) ::: aperture)))
>             _ -> Zip
>         branch = (pLam (az :<: pP) <+> memoize <!> az) |- TF One
>     memoGadget = Gadget
>       {gKind = IMemo, gType = memoType, gElim = gCase (memoBranch <!> cPz)}

------------------------------------------------------------------------------

> makeGen :: (UName,Param,Params) -> Gadget -> Gadget
> makeGen (uroot,nF :=: uF :=: (_,vF ::: tF),cPz) memo = genGadget
>   where
>     genType iz x = genT @@ iz @@ x
>     genT =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") uroot All NormV $ vF @@ indz
>           aperture  = pHide indz :<: px
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV
>                         $ aperture |- star
>           (pm,vm)   = decl (voon /// "m") (UN "") All NormV
>                         $ aperture |- TBind All (UN "r",NormV) (Sem
>                             (Just (vx @@ Ind memo (parArg <!> indz) @@ vP))
>                             (const (vP @@ aperture)))
>       in  pLam (indz :<: px) :<: pP :<: pm |-
>             TBind Ex (UN "r",NormV) (Sem
>               (Just (vx @@ Ind memo (parArg <!> indz) @@ vP))
>               (const (vP @@ aperture)))
>     genBranch (nC :=: uC :=: (_,vC ::: tC)) =
>       [(uC,\ iz az -> branch @@ az)] where
>         (az,TF (Con _ _ _ iz)) = (voon,"a") -| tC
>         ((pP,vP),mm) = (voon /// "P") .| genType iz (vC @@ az)
>         ((pm,vm),_)  = (voon /// "m") .| mm
>         (aperture,_) = (voon,"i") -| parTy pP
>         collect :: Param -> Term -> Term
>         collect (nA :=: UN s :=: (_,vA ::: tA)) tuple =
>           case (nA,"b") -| tA of
>             (hoaz,TF (Con TypeCon u _ hiz)) | u == uF -> pair
>               (pLam hoaz |- vA @@ hoaz @@ Ind genGadget hiz @@ vP @@ vm)
>               tuple
>             _ -> tuple
>         tuple = action collect az (TF Only)
>         branch = pLam (az :<: pP :<: pm) |- pair tuple
>                    (vm @@ (iz :<: (vC @@ az) ::: aperture) @@ tuple)
>     genGadget = Gadget
>       {gKind = IGen, gType = genType, gElim = gCase (genBranch <!> cPz)}

------------------------------------------------------------------------------

> makeRec :: (UName,Param,Params) -> Gadget -> Gadget -> Gadget
> makeRec (uroot,nF :=: uF :=: (_,vF ::: tF),cPz) memo gen = recGadget
>   where
>     recType iz x = recT @@ iz @@ x
>     recT =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") (UN "") All NormV $ vF @@ indz
>           aperture  = pHide indz :<: px
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV
>                         $ aperture |- star
>           (pm,vm)   = decl (voon /// "m") (UN "") All NormV
>                         $ aperture |- TBind All (UN "xrec",NormV) (Sem
>                             (Just (vx @@ Ind memo (parArg <!> indz) @@ vP))
>                             (const (vP @@ aperture)))
>       in  pLam (indz :<: px) :<: pP :<: pm |- vP @@ aperture
>     recElim iz x = Just (recE @@ iz @@ x)
>     recE =
>       let (indz,_)  = (voon,"i") -| tF
>           (px,vx)   = decl (voon /// "x") (UN "") All NormV $ vF @@ indz
>           aperture  = pHide indz :<: px
>           (pP,vP)   = decl (voon /// "P") (UN "") All NormV
>                         $ aperture |- star
>           (pm,vm)   = decl (voon /// "m") (UN "") All NormV
>                         $ aperture |- TBind All (UN "xrec",NormV) (Sem
>                             (Just (vx @@ Ind memo (parArg <!> indz) @@ vP))
>                             (const (vP @@ aperture)))
>       in  pLam (indz :<: px :<: pP :<: pm)
>           |- vx @@ Ind gen (parArg <!> indz) @@ vP @@ vm @@ pi2
>     recGadget = Gadget
>       {gKind = IRec, gType = recType, gElim = recElim}

