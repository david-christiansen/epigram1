******************************************************************************
**********                                                          **********
**********     Elab.lhs --- the Epigram elaborator                  **********
**********                                                          **********
******************************************************************************

> module Elab where

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
> import Concrete
> import Term
> import ObjKind
> import Compute
> import Unify
> import Gadgets
> import Ewam


******************************************************************************
Gap
******************************************************************************

> data Gap = Gap deriving Show

> instance Displayable Gap where
>   display ew _ Gap = box (take ew (repeat '-'))

> instance Updatable Gap

> instance Problem Gap () where
>   refine _ =
>     solved () Gap
>   event _ _ DoubleClickEvent =
>     do epigramUndoMark
>        epigramRefine $
>          do tweak outRight
>             private "Gap" Zip $ await (Elab,QDecl) Gap
>             private "Source" Zip . await (Elab,QDecl) $
>               From emptyEDoc Source
>             tweak inLeft
>        epigramAskIgor
>   event q s e@(CharEvent _) = do
>     event q s DoubleClickEvent
>     epigramEvent e
>   event q s e@(StringEvent _) = do
>     event q s DoubleClickEvent
>     epigramEvent e
>   event _ _ _ = return ()


******************************************************************************
Button
******************************************************************************

> data Button = Button String String deriving Show

> instance Updatable Button

> instance Displayable Button where
>   display ew ctxt (Button bs _) = box bs

> instance Problem Button () where
>   event (Button _ as) _ (HoraceEvent _) =
>     epigramPostEvents [ActionEvent as]
>   event _ _ _ = return ()
>   refine q = solved () q


******************************************************************************
Blankety
******************************************************************************

> data Blankety = Blankety deriving Show

> instance Updatable Blankety
> instance Displayable Blankety

> instance Problem Blankety () where
>   refine Blankety = solved () Blankety


******************************************************************************
From
******************************************************************************

> data From syntax control = From syntax control deriving Show

> instance Updatable control => Updatable (From syntax control) where
>   upd bull (From syn cont) =
>     do cont' <- upd bull cont
>        return (From syn cont')

> instance Displayable syntax => Displayable (From syntax control) where
>   display ew lz (From syn _) = display ew lz syn
>   cursorXY (From syn _) = cursorXY syn


******************************************************************************
Editing
******************************************************************************

> instance Displayable Lexical where
>   display _ _ lexi = box lexi
>   cursorXY lexi = (1,0) <+> eDocXY lexi

> class Editor syntax control result | control -> syntax result where
>   editParser :: control -> Parser Maybe Item syntax
>   editType :: control -> Term
>   editInfo :: control -> Refine LName
>   editInfo _ = return $ button /// "Blankety"

> instance (Editor syntax control result,
>           Displayable syntax,Show syntax,
>           Updatable result,Reportable result,Show result,
>           Updatable control,Show control,
>           Problem (From syntax control) result)
>   => Problem (From Lexical control) result where
>   event (From lexi cont) _ (ActionEvent "Elab") =
>     case parseItemize (editParser cont) lexi :: Maybe syntax of
>       Nothing -> track "Barf!" $ return ()
>       Just syn -> do
>         epigramUndoMark
>         ctxt <- get epiCtxt
>         epigramRefine $
>           do tweak killLocalInfo
>              reduced (From syn cont)
>              return ()
>         epigramAskIgor
>   event (From lexi cont) _ e | Just e' <- inside e =
>     case eDocEvent e' lexi of
>       NoEdit -> return ()
>       MoveEdit lexi' -> epigramRefine $
>         tweak (\ (lz :<: Layer root del ezs (Prob _ k _) im) ->
>                  lz :<: Layer root del ezs
>                           (Prob (Pending MoreInfo) k (From lexi' cont))
>                           im)
>       ChangeEdit lexi' ->
>         do epigramUndoMark
>            epigramRefine $
>              do reduced (From lexi' cont)
>                 return ()
>     where
>       inside (SelectEvent _ (0,_)) = Nothing
>       inside (SelectEvent nom (x,y)) = Just (SelectEvent nom (x - 1,y))
>       inside (ReselectEvent (0,_)) = Nothing
>       inside (ReselectEvent (x,y)) = Just (ReselectEvent (x - 1,y))
>       inside DeselectEvent = Nothing
>       inside e = Just e
>   event _ _ _ = return ()
>   probType (From _ c) = editType c
>   localInfo (From _ c) = do
>     (ln,_) <- elabTerm "[Info]" $ do
>       del <- localContext
>       (deln,_) <- private "del" Zip . await (Elab,QTerm) $ From () del
>       ein <- editInfo c
>       (bn,_) <- private "elab" Zip . await (Elab,QTerm) $
>         Button "{Elaborate}" "Elab"
>       solved () $ EditInfo deln ein bn
>     return ln

> data EditInfo = EditInfo LName LName LName deriving Show

> instance Updatable EditInfo

> instance Displayable EditInfo where
>   display ew ctxt (EditInfo deln ein bn) =
>     (display ew ctxt deln `gTurnstile` display ew ctxt ein)
>     -#-
>     lineB
>     -#-
>     display ew ctxt bn

> instance Problem EditInfo () where
>   refine q = solved () q


> instance Show (Refine a) where
>   show _ = ""

> instance Updatable (Refine a)
> instance Displayable (Refine a)

> instance Problem (Refine a) a where
>   refine = id





******************************************************************************
Source
******************************************************************************

> type CSource = [CDecl Lexical]

> data Source = Source deriving Show

> instance Updatable Source

> instance Displayable CSource where
>   display _ _ _ = box0 -- only need a dummy here, as this guy vanishes!

> instance Editor CSource Source () where
>   editParser _ = iPP sourceParser
>   editType _ = TF Bot

Note, these must ALWAYS be between a pair of gaps

> instance Problem (From CSource Source) () where
>   refine (From ds _) =
>     do tweak (zPop 1)
>          -- kill the preceding gap
>        Zip :<: Layer _ _ (ez :<: _ :*: es) _ _ <- get id
>        tweak . layer . cursor $ \ _ -> (ez :*: es)
>        let swoon = case es of
>              _ :>: Tip _ -> track "swooning" True
>              _ -> False
>        blat swoon ds
>        tweak inRight
>     where
>       blat swoon [] = return ()
>       blat swoon (d : ds) =
>         do private "Gap" Zip . await (Elab,QDecl) $ Gap
>            if swoon then enter Swoon else return ()
>            private "Decl" Zip . suspend (Elab,QDecl) $ From d ()
>            blat swoon ds


******************************************************************************
CDecl
******************************************************************************

> instance Displayable x => Displayable (CDecl x) where
>   display ew ctxt dx = track "d Decl" $ box (up (display ew ctxt) dx)

> instance Problem (From (CDecl Lexical) ()) () where
>   refine (From (CSourcoid lexi) _) =
>     reduced $ From lexi Source
>   refine (From (CData _ fs cs) _) = do
>     (fn,ft) <- elabDecl "Form" $ From fs (SigsFormation,star)
>     (cn,ct) <- elabDecl "Cons" $ From cs (SigsConstructor,ft)
>     (gn,_) <- elabDecl "Gadgets" $ MakeGadgets ct
>     solved () $ From (CData (Just gn) (CSigsoid fn) (CSigsoid cn)) ()
>   refine (From (CLet ss mp) _) = track (show ss) $ do
>     (fn,tpp) <- elabDecl "PSig" $ From ss (SigsProgram,star)
>     let ty = tpp @@ pi1
>     let prob = tpp @@ pi2 @@ pi1
>     let pack = tpp @@ pi2 @@ pi2
>     (pn,sol) <- elabTerm "Prog" $ From mp prob
>     elabDecl "x" $ ProgDef prob (pack @@ sol ::: ty)
>     solved () $ From (CLet (CSigsoid fn) (Just (CProgoid pn))) ()
>   refine (From (CInspect _ ctm) _) = do
>     (cn,ct) <- private "e" Zip . suspend (Elab,QTerm) $
>       From ctm (Infer Recless TermPlease)
>     let tm ::: ty = llec ct
>     (vn,_) <- private "v" Zip . suspend (Elab,QTerm) $
>       From () (AppPlease,tm ::: Just ty)
>     (tn,_) <- private "t" Zip . suspend (Elab,QTerm) $
>       From () (TermPlease,ty ::: Just star)
>     solved () $ From (CInspect
>       (Just (CCast (Zip :<: CTermoid vn) (CApp (Zip :<: CTermoid tn))))
>       (CApp (Zip :<: CTermoid cn))) ()
>   refine (From (CInclude str) _) =
>     solved () $ From (CInclude str :: CDecl LName) ()
>   refine (From (CBegin str) _) =
>     solved () $ From (CBegin str :: CDecl LName) ()
>   refine (From (CEnd str) _) =
>     solved () $ From (CEnd str :: CDecl LName) ()


> data ProgDef = ProgDef Term (Term ::: Term) deriving Show

> instance Displayable ProgDef

> instance Updatable ProgDef where
>   upd bull (ProgDef p tty) = eta ProgDef <$> upd bull p <$> upd bull tty

> instance Problem ProgDef Term where
>   refine (ProgDef prob tty)
>     | (_,TF (Lbl LabTy (Label (f ::: _) _ _) _)) <- (voon,"x") -| prob
>     = reduced $ Define f tty
>   refine _ = stuck

> instance Problem (From (CDecl LName) ()) ()

> instance Displayable (UName,[Gadget]) where
>   display _ _ _ = box DATA

> instance Updatable (UName,[Gadget])

> instance Problem (UName,[Gadget]) () where
>   gadgets (unom,gs) unam | unom == unam = Rightmost gs
>   gadgets _ _ = m0

> data MakeGadgets = MakeGadgets Term deriving Show

> instance Displayable MakeGadgets where
>   display _ _ _ = box DATA

> instance Updatable MakeGadgets where
>   upd bull (MakeGadgets t) = eta MakeGadgets <$> upd bull t

> instance Problem MakeGadgets () where
>   refine (MakeGadgets t) = do
>     ugs <- makeGadgets t
>     track (show ugs) $ return ()
>     solved () ugs


******************************************************************************
CSigs
******************************************************************************

> instance Displayable x => Displayable (CSigs x) where
>   display ew ctxt sx = box (up (display ew ctxt) sx)

> data SigsControl
>   = SigsFormation
>   | SigsConstructor
>   | SigsType Bind
>   | SigsHyp
>   | SigsConc Term SigsControl
>   | SigsLamCheck
>   | SigsLamInfer
>   | SigsProgram
>   deriving Show

> sctType :: (SigsControl,Term) -> Term
> sctType (SigsType _,_) = star
> sctType _ = TF Bot

> instance Updatable SigsControl where
>   upd bull (SigsConc t sc) = eta SigsConc <$> upd bull t <$> upd bull sc
>   upd bull sc = eta sc

> instance Problem (From (CSigs Lexical) (SigsControl,Term)) Term where
>   refine (From CEmpty sct@(_,t)) =
>     solved t $ From (CEmpty :: CSigs LName) sct
>   refine (From (CSig s) sct) =
>     reduced $ From s sct
>   refine (From (CSigs ss1 ss2) sct@(SigsHyp,_)) = do
>     (n1,t1) <- elabDecl "SL" $ From ss1 sct
>     --(vn,_)  <- elabDecl "V" $ VarCatch Zip
>     (n2,t2) <- elabDecl "SR" $ From ss2 (SigsHyp,t1)
>     solved t2 $ From (CSigs (CSigsoid n1)
>                       --(CSigs (CSigsoid vn)
>                             (CSigsoid n2)--)
>                      ) sct
>   refine (From (CSigs ss1 ss2) sct@(sc,_)) = do
>     (n1,t1) <- elabDecl "SL" $ From ss1 sct
>     (n2,t2) <- elabDecl "SR" $ From ss2 (sc,t1)
>     solved t2 $ From (CSigs (CSigsoid n1) (CSigsoid n2)) sct
>   refine (From (CSigsoid lexi) sct) =
>     reduced $ From lexi sct
>   probType (From _ sct) = sctType sct

> instance Editor (CSigs Lexical) (SigsControl,Term) Term where
>   editParser _ = iPP (eta CSig <$> (eta CRule <$> blah </> iPP (pF RULE) <$>
>                        blah </> iPP (pF COLON) <$> blah)
>                      <+> blah)
>   editType = sctType

> instance Problem (From (CSigs LName) (SigsControl,Term)) Term


******************************************************************************
CSig
******************************************************************************

> instance Displayable x => Displayable (CSig x) where
>   display ew ctxt sx = box (up (display ew ctxt) sx)

> instance Problem (From (CSig LName) (SigsControl,Term)) Term where
>   probType (From _ sct) = sctType sct

> noArgs :: [(Visibility,UName)]
> noArgs = []

> instance Problem (From (CSig Lexical) (SigsControl,Term)) Term where
>   refine (From (CSimple ps mty) sct@(sc,t0)) = do
>     (mdomn,dom) <- case mty of
>       Just ty -> do
>         (domn,dom) <- elabTerm "Dom" $ From ty (Check Recce TermPlease star)
>         return (Just domn,dom)
>       Nothing -> do
>         (_,dom) <- public "X" Zip $ hope star
>         return (Nothing,dom)
>     (ns,t') <- blat ps dom t0
>     solved t' $ From (ns ::: mdomn) sct
>     where
>       blat :: [CParam] -> Term -> Term ->  Refine ([LName],Term)
>       blat [] d t0 = return ([],t0)
>       blat (p : ps) d t0 = do
>         (n,t1) <- elabDecl "B" $ From (p,noArgs)  (d,(sc,t0))
>         (ns,t') <- blat ps d t1
>         return (n : ns,t')
>   refine (From (CRule hyps concs ty) sct@(sc,t)) = do
>     (hvn,_)  <- private "V" Zip . await (Elab,QDecl) $ VarCatch Zip
>     (hyn,_) <- private "H" Zip . await (Elab,QDecl) $
>                  From hyps (SigsHyp,star)
>     --(rvn,_)  <- private "V" Zip . await (Elab,QDecl) $ VarCatch Zip
>     (rn,rt) <- private "ConcT" Zip . await (Elab,QTerm) $
>                  From ty (Check Recce TermPlease star)
>     (cn,ct) <- private "C" Zip . await (Elab,QDecl) $
>                  From concs ((),(SigsConc rt sc,t))
>     reduced $ From (CRule --(CSigs 
>                      (CSigs (CSigsoid hvn) (CSigsoid hyn))
>                            --(CSigsoid rvn)) 
>                      (CCncloid cn)
>                     (CApp (Zip :<: CTermoid rn))) sct
>   probType (From _ sct) = sctType sct

> instance Displayable ([LName] ::: (Maybe LName)) where
>   display ew gam (ns ::: mnom) =
>     bSimple (up (display ew gam) ns) (up (display ew gam) mnom)

> instance Problem (From ([LName] ::: (Maybe LName)) (SigsControl,Term))
>   Term where
>     probType (From _ sct) = sctType sct

> instance Displayable (Visibility,LName) where
>   display ew gam (NormV,nom) = display ew gam nom
>   display ew gam (UnifV,nom) = UNDER |?| display ew gam nom

> instance Displayable ((Visibility,LName),[(Visibility,UName)]) where
>   display ew ctxt (vl,[]) = display ew ctxt vl
>   display ew ctxt (vl,vus) =
>     display ew ctxt vl `gApp`
>     seqB gApp (up vub vus) where
>       vub (NormV,u) = box (ObjPar,u)
>       vub (UnifV,u) = UNDER |?| box (ObjPar,u)

> instance Problem (From ((Visibility,LName),[(Visibility,UName)])
>                   (SigsControl,Term)) Term where
>   probType (From _ sct) = sctType sct

> instance Displayable (CParam,[(Visibility,UName)]) where
>   display _ _ (p,[]) = box p
>   display ew ctxt (p,vus) =
>     box p `gApp`
>     seqB gApp (up vub vus) where
>       vub (NormV,u) = box (ObjPar,u)
>       vub (UnifV,u) = UNDER |?| box (ObjPar,u)


******************************************************************************
Which declarations are ok?
******************************************************************************

> instance Problem (From (CParam,[(Visibility,UName)])
>                        (Term,(SigsControl,Term))) Term where
>   refine (From (CParam _ NormV unom,vus)
>     (dom,sct@(SigsFormation,TF Star))) = do
>       b <- compute "b" $ IsFamilyType dom
>       (dn,d) <- elabDecl "D" $ When b (Declare unom (ObjDecl TypeCon) dom)
>       bc <- compute "bc" $ Clear d
>       reduced . When bc $ Solve (pair d (TF Only))
>                                 (From ((NormV,dn),vus) sct)
>   refine (From (CParam _ NormV unom,_) (dom,(SigsFormation,TF _))) =
>     failed
>   refine (From (CParam _ NormV unom,vus) (dom,sct@(SigsConstructor,
>     TF (Pair _ d@(TF (Con TypeCon ufam nfam _)) cs)))) = do
>       b <- compute "b" $ IsConstructorType ufam dom
>       (cn,c) <- elabDecl "C" $
>         When b (Declare unom (ObjDecl (DataCon nfam)) dom)
>       bc <- compute "bc" $ Clear c
>       reduced . When bc $ Solve (pair d (pair cs c))
>                                 (From ((NormV,cn),vus) sct)
>   refine (From (CParam _ NormV unom,_) (dom,(SigsConstructor,t))) =
>     if Might True == unclear t then stuck else failed
>   refine (From (CParam _ NormV unom@(UN f),vus)
>     (dom,sct@(SigsProgram,TF Star)))
>     | Just (prob,pack) <- progProb unom vus dom
>     = track "progProb done\n" $
>       do Must b <- okName ObjDefn unom
>          track ("PROB " ++ show prob) $ return ()
>          track ("PACK " ++ show pack) $ return ()
>          if b
>            then do
>              fprob@(fpnom,_) <- child f
>              fake@(fnom,_) <- child f
>              subEntries $ Zip :<:
>                Name fprob
>                  (Object (unom :=: (ObjRec,nmTm fpnom ::: prob)))
>                  ImNew :<:
>                Name fake
>                  (Object (unom :=: (ObjRec,pack @@ nmTm fpnom ::: dom)))
>                  ImNew
>              (fn,_) <- elabTerm "f" $ From (Variable (Just ObjDefn) unom) ()
>              solved (pair dom (pair prob pack)) $
>                From ((NormV,fn),vus) sct
>            else failed
>   refine (From _ (_,(SigsProgram,TF (Pair _ _ _)))) =
>     failed
>   refine (From (CParam _ vis unom,vus) (dom,sct@(SigsHyp,_))) = do
>     (xn,x) <- elabDecl "x" $ Declare unom (ObjAbst All vis) dom
>     xok <- compute "ok" $ Clear x
>     reduced . When xok . Solve star $ From ((vis,xn),vus) sct
>   refine (From (CParam _ vis unom,vus) (dom,sct@(SigsLamInfer,_))) = do
>     (xn,x) <- elabDecl "x" $ Declare unom (ObjAbst Lam vis) dom
>     xok <- compute "ok" $ Clear x
>     reduced . When xok . Solve star $ From ((vis,xn),vus) sct
>   refine (From (CParam _ vis unom,vus) (dom,sct@(SigsType ae,_))) = do
>     (xn,x) <- elabDecl "x" $ Declare unom (ObjAbst ae vis) dom
>     xok <- compute "ok" $ Clear x
>     reduced . When xok . Solve star $ From ((vis,xn),vus) sct
>   refine (From (CParam _ vis unom,vus) (dom,sct@(SigsLamCheck,ft))) = do
>     -- DODGY??
>     fdr <- compute "ff" $ FunDomRan ft
>     d <- return $ fdr @@ pi1
>     r@(TBind Lam (_,vis') _) <-return $ fdr @@ pi2
>     if vis /= vis' then failed else do
>       u <- compute "u" $ UnifyIn star dom d
>       (xn,x) <- elabDecl "x" $ When u (Declare unom (ObjAbst Lam vis) dom)
>       xok <- compute "ok" $ Clear x
>       reduced . When xok . Solve (r @@ x) $ From ((vis,xn),vus) sct
>   refine (From (CParam _ UnifV _,_) _) =
>     failed
>   refine _ =
>     stuck
>   probType (From _ (_,sct)) = sctType sct


******************************************************************************
CCncl
******************************************************************************

> data VarCatch = VarCatch (Zip (UName :=: LName)) deriving Show

> instance Updatable VarCatch where
>   upd bull (VarCatch unz) = eta VarCatch <$> spot unz where
>     spot Zip = eta Zip
>     spot (unz :<: un@(u :=: _)) = eta (:<:) <$> spot unz <$>
>       (do tweak (heardOf u bull <+>) ; return un)

> instance Displayable VarCatch where
>   display ew (gam :<: _ :<: _) (VarCatch unz) = blat unz where
>     blat Zip = box0
>     blat (unz :<: (u :=: nom)) =
>       skipSep gSig (blat unz) $ case result gam (seekUName u) of
>         Nothing -> box0
>         Just (nam :=: _) ->
>           if nom == nam then box0 else box (ObjPar,u)
>   display _ _ _ = box0

> instance Problem VarCatch () where
>   refine q = solved () q
>   varCatch (VarCatch unomz) = Just unomz

> instance Editor (CCncl Lexical) ((),(SigsControl,Term)) Term where
>   editParser _ = iPP blah
>   editType (_,sct) = sctType sct

> instance Displayable (CCncl Lexical) where
>   display ew ctxt (sx) = box (up (display ew ctxt) sx)

> instance Problem (From (CCncl Lexical) ((),(SigsControl,Term))) Term where
>   refine (From (CCncloid lexi) usct) =
>     reduced $ From lexi usct
>   refine (From c (_,sct)) =
>     reduced $ From (c,noArgs) (Trigger sct)
>   probType (From _ (_,sct)) = sctType sct

> instance Problem (From (CCncl Lexical,[(Visibility,UName)])
>                   (Trigger (SigsControl,Term))) Term where
>   shock (From (CCncl pz,vus) (Trigger (SigsConc rt sc,t)))
>     (lz :<: l''@(Layer root'' del'' (ez'' :*: es'') prob'' im'')
>         :<: Layer root' del' (ez' :*: es') prob'@(Prob _ rk rq)
>               im'
>         :<: Layer croot@(cnom,_) _ _ _ _) =
>     move False (pz,vus) rt (ez' :*: es') where
>       move :: Bool -> (Zip CParam,[(Visibility,UName)]) -> Term ->
>                 Cursor Entry -> Maybe Ctxt
>       move b (Zip :<: p,vus) rt (Zip :*: work) =
>        track ("OUT " ++ show p) .
>        Just $
>         lz :<: Layer root'' del'' (ez'' :*:
>           Name croot (Waiting Zip nil (Prob (Pending Refine) (Elab,QDecl)
>                        (From (p,vus) (rt,(sc,t))))) ImNew :>:
>           Name root' (Waiting del' work
>             (Prob (Solved (wait cnom)) rk rq)) im' :>:
>           es'') prob'' im''
>       move b pv rt (ez :<: e@(Name _ (Waiting _ _ (Prob Satisfied _ _)) _)
>                     :*: es) =
>         move True pv rt (ez :*: e :>: es)
>       move b pv rt (ez :<: e@(Name (nom,_) (Hoping u del s) _) :*: es) =
>         move True pv
>           (if un (dep [nom] rt)
>              then Zip :<: (nom :=: u :=: (ObjAbst All UnifV,
>                             TElim (Var (F nom)) Zip
>                             ::: up (up pify) del |- s))
>                   |- rt
>              else rt)
>           (ez :*: e :>: es)
>       move b (pz@(_ :<: _) :<: CParam _ vis unom,vus) rt
>         (ez :<: e@(Name (nom,_) (Object (unam :=: (ObjAbst All _,tty))) im)
>          :*: es) | unom == unam
>         = move True (pz,(vis,unom) : vus)
>             (Zip :<: (nom :=: unom :=: (ObjAbst All vis,tty)) |- rt)
>             (ez :*: e :>: es)
>       move b pv rt
>         (ez :<: e@(Name (nom,_) (Object (unam :=: (ObjAbst All _,tty))) im)
>          :*: es)
>         = move True pv
>             (if un (dep [nom] rt)
>                then Zip :<: (nom :=: unam :=: (ObjAbst All UnifV,tty)) |- rt
>                else rt)
>             (ez :*: e :>: es)
>       move False _ _ _ = Nothing
>       move True (pz,vus) rt (ez :*: es) = Just $
>         lz :<: l'' :<:
>         Layer root' del' (ez :<:
>           Name croot (Waiting Zip nil (Prob (Pending MoreInfo) (Elab,QDecl)
>             (From (CCncl pz :: CCncl Lexical,vus)
>                   (Trigger (SigsConc rt sc,t))))) ImNew
>           :*: es)
>           prob' im'
>   shock _ _ = Nothing
>   probType (From _ (Trigger sct)) = sctType sct

> instance Displayable (CCncl Lexical,[(Visibility,UName)]) where
>   display ew ctxt (sx,[]) = display ew ctxt sx
>   display ew ctxt (sx,vus) =
>     display ew ctxt sx `gApp`
>     seqB gApp (up vub vus) where
>       vub (NormV,u) = box (ObjPar,u)
>       vub (UnifV,u) = UNDER |?| box (ObjPar,u)


******************************************************************************
CTerm
******************************************************************************

> instance Displayable x => Displayable (CTerm x) where
>   display ew ctxt sx = box (up (display ew ctxt) sx)

> instance Displayable x => Displayable (CHead x) where
>   display ew ctxt sx = box (up (display ew ctxt) sx)

> instance Displayable x => Displayable (Zip (CHead x)) where
>   display ew ctxt sx = display ew ctxt (CApp sx)

> data Recce = Recce | Recless deriving Show

> data TermShape = TermPlease | HeadPlease | AppPlease deriving Show

> data Infer = Infer Recce TermShape deriving Show

> instance Updatable Infer

> instance Editor (CTerm Lexical) Infer Term where
>   editParser (Infer r TermPlease) = iPP blah
>   editParser (Infer r HeadPlease) =
>     eta (CApp . (Zip :<:)) <$>
>       (iPP blah </> pEmpty <+>
>        eta (CTuple . (: [])) <$> iPP blah)
>   editParser (Infer r AppPlease) =
>     eta CApp <$>
>       (iPP blah </> pEmpty <+>
>        eta (zOne . CTuple . return) <$> iPP blah)
>   editType _ = cellType

> data Check = Check Recce TermShape Term deriving Show

> instance Editor (CTerm Lexical) Check Term where
>   editType (Check r _ t) = t
>   editParser (Check r th _) = editParser (Infer r th)
>   editInfo (Check _ _ t) = do
>     (tn,_) <- private "ty" Zip . await (Elab,QTerm) $
>       From () (TermPlease,t ::: Just star)
>     return tn

> instance Updatable Check where
>   upd bull (Check r th want) = eta (Check r th) <$> upd bull want

> cName :: LName -> CTerm LName
> cName nom = CApp (zOne (CTermoid nom))

> data Exact = Exact deriving Show

> instance Updatable Exact

> instance Problem (From (Zip (CHead LName)) Exact) Term where
>   probType _ = cellType

> instance Problem (From (Zip (CHead Lexical)) Exact) Term where
>   refine (From (Zip :<: h) c) = case h of
>     CTuple [t] -> do
>       (tn,t) <- elabTerm "t" $ From t (Infer Recless TermPlease)
>       solved t $ From (zOne (CTuple [cName tn])) c
>     CStar ->
>       solved (cell (star ::: star))
>         $ From (zOne (CStar :: CHead LName)) c
>     CZero ->
>       solved (cell (TF Zero ::: star))
>         $ From (zOne (CZero :: CHead LName)) c
>     COne ->
>       solved (cell (TF One ::: star))
>         $ From (zOne (COne :: CHead LName)) c
>     CTuple [] ->
>       solved (cell (TF Only ::: TF One))
>         $ From (zOne (CTuple [] :: CHead LName)) c
>     CRefl ->
>       solved (cell ((TBind Lam (UN "X",UnifV) . Sem Nothing{-star-}$ \ ty ->
>                      TBind Lam (UN "x",UnifV) . Sem Nothing{-ty-}$ \ t ->
>                      TF (JMRefl (t ::: ty)))
>                     :::
>                     (TBind All (UN "X",UnifV) . Sem (Just star) $ \ ty ->
>                      TBind All (UN "x",UnifV) . Sem (Just ty) $ \ t ->
>                      TF (JMEq (t ::: ty) (t ::: ty)))))
>         $ From (zOne (CRefl :: CHead LName)) c
>     CVar _ unom ->
>       reduced $ Trigger (Variable Nothing unom)
>     CQM -> do
>       (_,ty) <- public "X" Zip $ hope star
>       (_,tm) <- public "x" Zip $ hope ty
>       solved (cell (tm ::: ty)) (From (zOne (CQM :: CHead LName)) c)
>     CUnder ->
>       failed
>     CTermoid _ -> track "Bugger!" $ stuck
>     _ ->
>       stuck
>   refine (From (hz :<: h) c) = do
>     (fn,f) <- elabTerm "f" $ From hz (Infer Recless AppPlease)
>     let fv ::: ft = llec f
>     dr <- compute "dr" $ FunDomRan ft
>     anv <- elabTerm "a" $
>                  From (Zip :<: h) (Check Recce HeadPlease (dr @@ pi1))
>     reduced $ Application (fn,fv) dr anv
>   refine _ =
>     stuck
>   probType _ = cellType

> data Application = Application (LName,Term) Term (LName,Term) deriving Show

> instance Updatable Application where
>   upd bull (Application f dr a) =
>     eta Application <$> upd bull f <$> upd bull dr <$> upd bull a

> instance Displayable Application where
>   display ew ctxt (Application (fn,_) _ (an,_)) =
>     display ew ctxt (CApp (Zip :<: CTermoid fn :<: CTermoid an))

> instance Problem Application Term where
>   probType _ = cellType
>   refine q@(Application (_,fv) (TF (Pair _ dom ran)) (_,av)) =
>     solved (cell (fv @@ av ::: ran @@ av)) q
>   refine (Application _ (TF Bot) _) =
>     failed
>   refine _ =
>     stuck


> instance Problem (From (Zip (CHead LName)) Infer) Term where
>   probType _ = cellType

> instance Problem (From (Zip (CHead Lexical)) Infer) Term where
>   refine (From (Zip :<: CTuple [t]) iq) = do
>     (tn,t) <- elabTerm "t" $ From t iq
>     solved t $ From (Zip :<: (CTuple [cName tn])) iq
>   refine (From (Zip :<: CTermoid lexi) iq) = do
>     (nom,_) <- getRoot
>     track ("Editor " ++ show nom) $ return ()
>     reduced $ From lexi iq
>   refine (From (Zip :<: CUnder) _) =
>     failed
>   refine q@(From hz iq@(Infer Recce th)) = do
>     (nt,vTt) <- elabTerm "t" $ From hz (Infer Recless th)
>     let vtT@(vt ::: vT) = llec vTt
>     vr <- compute "r" $ KnotRec vtT
>     solved (cell (vr ::: vT)) $ From (zOne (CTermoid nt)) iq
>   refine (From (hz :<: CUnder) iq) = do
>     (sSn,sS) <- elabTerm "sS" $ From hz Exact
>     tT <- compute "tT" $ Explicit (llec sS)
>     solved tT $ From (Zip :<: CTermoid sSn :<: CUnder) iq
>   refine (From hz iq) = do
>     (sSn,sS) <- elabTerm "sS" $ From hz Exact
>     tT <- compute "tT" $ IComplete (llec sS)
>     solved tT $ From (zOne (CTermoid sSn)) iq
>   probType _ = cellType

> instance Problem (From (CTerm LName) Infer) Term where
>   probType _ = cellType

> instance Problem (From (CTerm Lexical) Infer) Term where
>   refine (From (CApp hz) iq) =
>     reduced $ From hz iq
>   refine (From (CBind Lam doms ran) _) = do
>     (dn,_) <- private "D" Zip . await (Elab,QDecl) $
>       From doms (SigsLamInfer,star)
>     (bn,bvt) <- private "b" Zip . await (Elab,QTerm) $
>       From ran (Infer Recce TermPlease)
>     reduced $ From (CBind Lam (CSigsoid dn) (CApp (Zip :<: CTermoid bn)))
>                    (DischargeInfer bvt)
>   refine (From t@(CBind ae doms ran) iq@(Infer _ th)) = do
>     (tyn,ty) <- elabTerm "BindT" $ From t (Check Recce th star)
>     solved (cell (ty ::: star)) $ From (Zip :<: CTermoid tyn) iq
>   refine (From (CElim g t) _) = do
>     (sn,s) <- elabTerm "s" $ From t (Infer Recce TermPlease)
>     reduced $ From (g,sn) s
>   refine (From (CCast hz ty) iq) = do
>     (tn,t) <- elabTerm "CastT" $ From ty (Check Recce TermPlease star)
>     (sn,s) <- elabTerm "s" $ From hz (Check Recce AppPlease t)
>     solved (cell (s ::: t)) $
>       From (CCast (Zip :<: CTermoid sn) (CApp (Zip :<: CTermoid tn))) iq
>   refine (From (CArrow sz ty) iq) = do
>     (sn,s) <- elabTerm "ArrS" $ From sz (Check Recce AppPlease star)
>     (tn,t) <- elabTerm "ArrT" $ From ty (Check Recce TermPlease star)
>     solved (cell (TBind All dull (Sem (Just s) (const t)) ::: star)) $
>       From (CArrow (zOne (CTermoid sn)) (cName tn)) iq
>   refine (From (CWedge sz ty) iq) = do
>     (sn,s) <- elabTerm "WedgS" $ From sz (Check Recce AppPlease star)
>     (tn,t) <- elabTerm "WedgT" $ From ty (Check Recce TermPlease star)
>     solved (cell (TBind Ex dull (Sem (Just s) (const t)) ::: star)) $
>       From (CWedge (zOne (CTermoid sn)) (cName tn)) iq
>   refine (From (CEquals sz tz) iq) = do
>     (sn,sS) <- elabTerm "qsS" $ From sz (Infer Recce AppPlease)
>     (tn,tT) <- elabTerm "qsT" $ From tz (Infer Recce AppPlease)
>     solved (cell (TF (JMEq (llec sS) (llec tT)) ::: star)) $
>       From (CEquals (zOne (CTermoid sn)) (zOne (CTermoid tn))) iq
>   probType _ = cellType

> instance Problem (From (Zip (CHead LName)) Check) Term where
>   probType (From _ (Check _ _ t)) = t

> instance Problem (From (Zip (CHead Lexical)) Check) Term where
>   refine (From (Zip :<: CTuple [t]) cq) = do
>     (tn,t) <- elabTerm "t" $ From t cq
>     solved t $ From (Zip :<: (CTuple [CApp (Zip :<: CTermoid tn)])) cq
>   refine (From (Zip :<: CTermoid lexi) cq) = do
>     (nom,_) <- getRoot
>     track ("Editor " ++ show nom) $ return ()
>     reduced $ From lexi cq
>   refine (From (Zip :<: CUnder) _) =
>     failed
>   refine (From (Zip :<: CQM) cq@(Check _ _ want)) = do
>     (_,tm) <- public "x" Zip $ hope want
>     solved tm $ From (Zip :<: (CQM :: CHead LName)) cq
>   refine (From hz cq@(Check Recce th ty)) = do
>     (nt,vt) <- elabTerm "t" $ From hz (Check Recless th ty)
>     del <- getDel
>     track ("Recce: " ++ show del ++ " |- " ++ show vt) $ return ()
>     vr <- compute "r" $ KnotRec (vt ::: ty)
>     solved vr $ From (Zip :<: CTermoid nt) cq
>   refine (From (hz :<: CUnder) cq@(Check _ _ want)) = do
>     (sSn,sS) <- elabTerm "sS" $ From hz Exact
>     let s ::: got = llec sS
>     u <- compute "u" $ UnifyIn star got want
>     reduced $ When u . Solve s $ From (Zip :<: CTermoid sSn :<: CUnder) cq
>   refine (From hz cq@(Check _ _ want)) = do
>     (_,wrapped) <- private "wrap" Zip . await (Compute,QDecl) $ IWrap want
>     (sSn,sS) <- private "sS" Zip . await (Elab,QTerm) $ From hz Exact
>     (_,tT) <- private "tT" Zip . await (Compute,QTerm) $ IComplete (llec sS)
>     let (t ::: got) = llec tT
>     (_,u) <- private "u" Zip . await (Compute,QTerm) $
>       UnifyIn star got wrapped
>     reduced $ From (CApp (Zip :<: CTermoid sSn)) (DischargeCheck u t want)
>   probType (From _ (Check _ _ t)) = t

> instance Problem (From (CTerm LName) Check) Term where
>   probType (From _ (Check _ _ t)) = t

> instance Problem (From (CTerm Lexical) Check) Term where
>   refine (From (CApp hz) cq) =
>     reduced $ From hz cq
>   refine (From (CBind Lam doms ran) (Check _ _ want)) = do
>     (dn,bt) <- private "D" Zip . await (Elab,QDecl) $
>       From doms (SigsLamCheck,want)
>     (bn,bv) <- private "b" Zip . await (Elab,QTerm) $
>       From ran (Check Recce TermPlease bt)
>     reduced $ From (CBind Lam (CSigsoid dn) (CApp (Zip :<: CTermoid bn)))
>                    (DischargeCheck (BVal True) bv want)
>   refine (From (CBind ae doms ran) (Check _ _ want)) = do
>     u <- compute "u" $ UnifyIn star star want
>     (dn,_) <- private "Ds" Zip . await (Elab,QDecl) $
>                 From doms (SigsType ae,star)
>     (rn,r) <- private "R" Zip . await (Elab,QTerm) $
>                 From ran (Check Recce TermPlease star)
>     reduced $ From (CBind ae (CSigsoid dn) (CApp (Zip :<: CTermoid rn)))
>                 (DischargeCheck u r want)
>   refine (From tm (Check r th want)) = do
>     (_,wrapped) <- private "wrap" Zip . await (Compute,QDecl) $ IWrap want
>     (sSn,sS) <- private "sS" Zip . await (Elab,QTerm) $ From tm (Infer r th)
>     (_,tT) <- private "tT" Zip . await (Compute,QTerm) $ IComplete (llec sS)
>     let (t ::: got) = llec tT
>     (_,u) <- private "u" Zip . await (Compute,QTerm) $
>       UnifyIn star got wrapped
>     reduced $ From (CApp (Zip :<: CTermoid sSn)) (DischargeCheck u t want)
>   probType (From _ (Check _ _ t)) = t

 data FunDomRan = FunDomRan Term deriving Show

 instance Updatable FunDomRan where
   upd bull (FunDomRan ft) = eta FunDomRan <$> upd bull ft

 instance Displayable x => Displayable (Maybe x) where
   display ew ctxt (Just x) = display ew ctxt x
   display ew ctxt Nothing  = box0

 instance Problem (From (Maybe LName) FunDomRan) Term where
   refine q@(From x (FunDomRan (TBind All uv@(_,NormV) sc@(Sem dom _)))) =
     solved (pair dom (TBind Lam uv sc)) q
   refine q@(From x (FunDomRan t@(TElim (Hope _) _))) = do
     (_,dom) <- public "S" Zip $ hope star
     (_,ran) <- public "T" Zip . hope $ TBind All dull (Sem dom (const star))
     u <- compute "u" . UnifyIn star t $ TBind All dull (Sem dom (ran @@))
     reduced . When u $
       Solve (pair dom (TBind Lam dull (Sem dom (ran @@)))) q
   refine (From x (FunDomRan t)) | Might True <- unclear t =
     stuck
   refine _ =
     failed
   probType _ = TBind Ex dull . Sem star $ \ d ->
                TBind All dull . Sem d $ \ _ -> star

> instance Displayable (IndElim,LName) where
>   display ew ctxt (ie,t) =
>     display ew ctxt (CElim ie (CApp (Zip :<: CTermoid t)))

> instance Problem (From (IndElim,LName) Term) Term where
>   refine q@(From (ie,_) tmty)
>     | TF (Con TypeCon unom _ iz) <- ty = do
>         lz <- get id
>         g <- doo $ fug unom lz
>         solved (cell (tm @@ Ind g iz ::: gType g iz tm)) q
>     | TF Zero <- ty = do
>         solved (cell ((TBind Lam dull . Sem Nothing{-star-} $ \ kill ->
>                        tm @@ NoughtE kill) :::
>                       TBind All dull (Sem (Just star) id))) q
>     | TF (JMEq _ _) <- ty = do
>         etty <- majorElim Zip (tm ::: ty)
>         solved (cell etty) q
>     | Might True <- unclear ty = stuck
>     | otherwise = failed
>     where
>       tm ::: ty = llec tmty
>       fug unom lz | Rightmost gs <- lay <!> lz = gie <!> gs where
>         gie g = when (ie == gKind g) (Just g)
>         lay (Layer _ _ (ez :*: _) _ _) = ent <!> ez
>         ent (Name _ (Waiting _ _ (Prob _ _ q)) _) = gadgets q unom
>         ent _ = m0
>       fug _ _ = m0
>   probType _ = cellType


******************************************************************************
Discharges
******************************************************************************

> data DischargeCheck = DischargeCheck (Boole LName) Term Term deriving Show

> instance Updatable DischargeCheck where
>   upd bull (DischargeCheck b t ty) =
>     eta DischargeCheck <$> upd bull b <$> upd bull t <$> upd bull ty

> instance Problem (From (CTerm LName) DischargeCheck) Term where
>   export del work q@(From d (DischargeCheck (BVal True) t _)) = do
>     case tidyWorkSpace del (Zip,Zip) m0 (work <>> nil) of
>       ((ez,del'),(Tip _,bull)) -> do
>         subEntries ez
>         let sol = del' |- bull <%> t
>         let q' = bull <%> q
>         track ("DISCHARGECHECK[ " ++ show q) $ return ()
>         track (show ez) $ return ()
>         track (show del') $ return ()
>         track (show bull) $ return ()
>         track (show sol) $ return ()
>         track (show q') $ return ()
>         track "]DISCHARGECHECK" $ return ()
>         return (nil,Solved sol,ProbFor q')
>       _ -> stuck
>   export del work q@(From d (DischargeCheck (BVal False) _ ty)) =
>     return (work <>> nil,Failed,ProbFor q)
>   export _ _ _ = track "DC No Export" $ stuck
>   probType (From _ (DischargeCheck _ _ ty)) = ty


> data DischargeInfer = DischargeInfer Term deriving Show

> instance Updatable DischargeInfer where
>   upd bull (DischargeInfer tty) = eta DischargeInfer <$> upd bull tty

> instance Problem (From (CTerm LName) DischargeInfer) Term where
>   export del work q@(From d (DischargeInfer tty)) | tm ::: ty <- llec tty =
>     case tidyWorkSpace del (Zip,Zip) m0 (work <>> nil) of
>       ((ez,del'),(Tip _,bull)) -> do
>         subEntries ez
>         let sol = cell $ (del' |- bull <%> tm) :::
>                          (up (up pify) del' |- bull <%> ty)
>         let q' = bull <%> q
>         track ("DISCHARGEINFER[ " ++ show q) $ return ()
>         track (show ez) $ return ()
>         track (show del') $ return ()
>         track (show bull) $ return ()
>         track (show sol) $ return ()
>         track (show q') $ return ()
>         track "]DISCHARGEINFER" $ return ()
>         return (nil,Solved sol,ProbFor q')
>       _ -> m0
>   probType _ = cellType


> data DischargeBoole = DischargeBoole (Boole LName) deriving Show

> instance Updatable DischargeBoole where
>   upd bull (DischargeBoole b) = eta DischargeBoole <$> upd bull b

> instance (Displayable (cf LName), Show (cf LName)) =>
>   Problem (From (cf LName) DischargeBoole) (Boole LName) where
>     export del ez q@(From syn (DischargeBoole (BVal True))) =
>       return (ez <>> nil, Solved (BVal True), ProbFor q)
>     export _ _ _ = m0

******************************************************************************
Variable
******************************************************************************

> data Variable = Variable (Maybe ObjKind) UName deriving Show

> instance Displayable Variable where
>   display _ _ (Variable Nothing (UN s)) = box s
>   display _ _ (Variable (Just ok) unom) = box (ok,unom)

> instance Updatable Variable where
>   upd bull (Variable mok unom) = eta (Variable mok) <$> upd bull unom

> instance Problem (Trigger Variable) Term where
>   refine (Trigger (Variable Nothing unom)) = do
>     _ :=: _ :=: (ok,tmty) <- elabUName unom
>     track ("Found " ++ show unom) $ return ()
>     solved (cell tmty) (Trigger (Variable (Just ok) unom))
>   refine _ =
>     stuck
>   seeksVar (Trigger (Variable Nothing unom)) = Just unom
>   seeksVar _ = Nothing
>   shock (Trigger (Variable Nothing unom@(UN s))) ctxt = catchIt ctxt where
>     catchIt ctxt@(Zip :<: Layer _ _ (Zip :*: _) _ _) = m0
>     catchIt ctxt@(_ :<: Layer _ _ (Zip :*: _) _ _) = catchIt (outRight ctxt)
>     catchIt (lz :<: Layer root del (ez :<:
>       Name croot (Waiting _ _ (Prob _ _ q)) cim :*: es) prob im)
>       | Just unz <- varCatch q
>       , Must True <- okToCatchL <!> lz <+> okToCatchE ez
>       = effect (lz :<: Layer root del (ez :*: es) prob im) (insv unz)
>       where
>         insv unz = do
>           (_,ty) <- private "VarT" Zip $ hope star
>           (n,_) <- private s Zip $ forAll UnifV ty
>           tweak . layer . cursor $ \ (ez :*: es) ->
>             (ez :<: Name croot (Waiting Zip nil
>               (Prob Satisfied (Elab,QDecl) (VarCatch (unz :<: (unom :=: n))))
>              ) ImNew :*: News (story (UStory unom)) :>: es)
>     catchIt (_ :<: Layer _ _ (_ :<:
>       Name _ (Waiting _ _ (Prob (Pending _) (Elab,_) _)) _ :*: _) _ _) = m0
>     catchIt (_ :<: Layer _ _ (_ :<:
>       Name _ (Waiting _ _ (Prob Failed (Elab,_) _)) _ :*: _) _ _) = m0
>     catchIt ctxt = catchIt (layer (cursor (unjust . curUp)) ctxt)
>     okToCatchL (Layer _ _ (ez :*: _) _ _) = okToCatchE ez
>     okToCatchE Zip = m0
>     okToCatchE (ez :<: Name (Long (Zip :<: ("Gap",_)),_) _ _) = m0
>     okToCatchE (ez :<: e) = okToCatchE ez <+>
>       case e of
>         Name _ (Waiting _ _ (Prob (Pending _) (Elab,QDecl) _)) _ ->
>           Must False
>         _ -> m0
>   probType _ = cellType


******************************************************************************
Rendering
******************************************************************************

> mystery :: Boxings
> mystery = faceB (Face Background OK Orange) (box "?")

> instance Displayable () where
>   display ew ctxt _ = mystery

> forceIt :: (Term -> Term) -> Bool
> forceIt _ = False

> brApp :: TermShape -> Zip (CHead LName) -> CTerm LName
> brApp HeadPlease hz@(_ :<: _ :<: _) = CApp (Zip :<: CTuple [CApp hz])
> brApp _ hz = CApp hz

> brTm :: TermShape -> CTerm LName -> CTerm LName
> brTm ts (CApp hz) = brApp ts hz
> brTm TermPlease t = t
> brTm _ t = CApp (Zip :<: CTuple [t])

> hdTm :: CHead LName -> CTerm LName
> hdTm h = CApp (Zip :<: h)

> instance Updatable TermShape

> noType :: Maybe Term
> noType = Nothing

> instance Problem (From (CHead LName) ()) Term
> instance Problem (From (CTerm LName) ()) Term
> instance Problem (From (CSigs LName) ()) ()

> instance Displayable (TermShape,Zip (CHead LName)) where
>   display ew gam (sh,hz) = display ew gam (brApp sh hz)

> instance Problem (From (TermShape,Zip (CHead LName)) (Term,List Term))
>                  Term where
>   probType _ = star
>   refine (From (sh,hz) (ty,Tip _)) =
>     solved ty $ From (brApp sh hz) ()
>   refine (From (sh,hz) (TBind All (u,UnifV) dr@(Sem (Just dom) ran),
>     TF (U_ i) :>: as))
>     | i == Shown || forceIt ran
>     = reduced $ From (sh,hz :<: CUnder) (TBind All (u,NormV) dr,as)
>     | otherwise
>     = case as of
>         a :>: as ->
>           reduced $ From (sh,hz) (ran a,as)
>         _ -> solved (TBind All (u,NormV) dr) $
>                From (brApp sh (hz :<: CUnder)) ()
>   refine (From (sh,hz)
>       (TBind All (_,NormV) (Sem (Just dom) ran),a :>: as)) = do
>     (an,_) <- elabTerm "a" $ From () (HeadPlease,a ::: Just dom)
>     reduced $ From (sh,hz :<: CTermoid an) (ran a,as)
>   refine _ = stuck

> data Labby = Labby LName deriving Show

> instance Updatable Labby

> instance Displayable Labby where
>   display ew ctxt (Labby nom) = "<" |?| display ew ctxt nom |?| ">"

> instance Problem Labby () where
>   refine q = solved () q

> instance Problem (From () (TermShape,Term ::: (Maybe Term))) Term where
>   refine (From () (_,tmty)) | track (show tmty) $ False = stuck
>   refine (From () c@(ts,tm ::: mty)) = blat tm where
>     blat tm | Might True <- unclear tm = stuck
>     blat (TBind b _ _) = do
>       (del',mty',ss,r) <- bindPrefix b tm mty Zip CEmpty
>       (rn,rty) <- public "r" del' . await (Elab,QTerm) $
>         From () (TermPlease,r ::: mty')
>       sol <- return $ case b of
>         Lam -> (up (up pify) del' |- rty @@ del')
>         _ -> star
>       solved sol $ From (brTm ts (CBind b ss (hdTm (CTermoid rn)))) c
>     blat (TF Star) =
>       solved star $ From (hdTm CStar) c
>     blat (TF Zero) =
>       solved star $ From (hdTm CZero) c
>     blat (TF One) =
>       solved star $ From (hdTm COne) c
>     blat (TF Only) =
>       solved (TF One) $ From (hdTm (CTuple [])) c
>     blat (TF (JMRefl tty)) =
>       solved (TF (JMEq tty tty)) $ From (hdTm CRefl) c
>     blat (TF (Lbl LabTy lab _)) = do
>       (xn,_) <- elabTerm "x" $ From () lab
>       (yn,_) <- elabTerm "y" $ Labby xn
>       solved star $ From (hdTm (CTermoid yn)) ()
>     blat (TF (JMEq (s ::: sy) (t ::: ty))) = do
>       (ns,_) <- elabTerm "s" $ From () (AppPlease,s ::: Just sy)
>       (nt,_) <- elabTerm "t" $ From () (AppPlease,t ::: Just ty)
>       solved star $
>         From (brTm ts (CEquals (zOne (CTermoid ns)) (zOne (CTermoid nt)))) c
>     blat (TElim h (ez :<: Ind g iz)) = do
>       let targ = TElim h ez
>       (tn,_) <- elabTerm "t" $ From () (TermPlease,targ ::: noType)
>       solved (gType g iz targ) $
>         From (brTm ts (CElim (gKind g) (hdTm (CTermoid tn)))) c
>     blat x = do
>       (h,as) <- unapps x
>       (hh,hty) <- case h of
>         TF (Con _ unom _ Zip) -> do
>           _ :=: _ :=: (ok,_ ::: ty) <- seekUName unom
>           (hn,_) <- elabTerm "h" $ From (Variable (Just ok) unom) ()
>           return (CTermoid hn,ty)
>         TElim (Var (F x)) Zip -> do
>           Rightmost (unom :=: (ok,_ ::: ty)) <- get $ varObj x
>           (hn,_) <- elabTerm "h" $ From (Variable (Just ok) unom) ()
>           return (CTermoid hn,ty)
>         _ -> case as of
>           Tip _ -> return (CQM,star)
>           _ -> do
>             (hn,ty) <- elabTerm "h" $ From () (HeadPlease,h ::: noType)
>             return (CTermoid hn,ty)
>       reduced $ From (ts,zOne hh) (hty,as)
>     bindPrefix b (TBind b' (uno,v) (Sem d r)) mty del' ss
>       | b == b' = do
>         lz <- get id
>         del <- getDel
>         let unom@(UN s) = if uno == UN "" then UN "x" else uno
>         if already unom lz del'
>           then
>             bindPrefix b (TBind b (UN (s ++ "'"),v) (Sem d r)) mty del' ss
>           else case (mty,b,d) of
>             (Just (TBind All _ (Sem (Just dom) rat)),Lam,_) -> do
>               (p,x) <- param ObjPar unom dom
>               bindPrefix Lam (r x) (Just (rat x)) (del' :<: p)
>                 (CSigs ss (CSig (CSimple [CParam True v unom] Nothing)))
>             (Nothing,Lam,Just dom) -> do
>               (dn,_) <- public "d" del' . await (Elab,QTerm) $
>                 From () (TermPlease,dom ::: Just star)
>               (p,x) <- param ObjPar unom dom
>               bindPrefix Lam (r x) Nothing (del' :<: p)
>                 (CSigs ss (CSig (CSimple [CParam True v unom]
>                                    (Just (hdTm (CTermoid dn))))))
>             (Nothing,b,Nothing) -> do
>               (p,x) <- param ObjPar unom star --dom dummy oops
>               bindPrefix b (r x) Nothing (del' :<: p)
>                 (CSigs ss (CSig (CSimple [CParam True v unom] Nothing)))
>             (_,b,Just dom) -> do
>               (dn,_) <- public "d" del' . await (Elab,QTerm) $
>                  From () (TermPlease,dom ::: Just star)
>               (p,x) <- param ObjPar unom dom
>               bindPrefix b (r x) (Just star) (del' :<: p)
>                 (CSigs ss (CSig (CSimple [CParam True v unom]
>                                  (Just (hdTm (CTermoid dn))) )))
>     bindPrefix b r mty del' ss = return (del',mty,ss,r)
>     already unom lz Zip | Just _ <- result lz (seekUName unom) = True
>     already unom lz (_ :<: (_ :=: unam :=: _)) | unom == unam  = True
>     already unom lz (del :<: _) = already unom lz del
>     already _ _ _ = False
>   probType _ = star

> instance Problem (From (CTerm LName) (TermShape,Term ::: (Maybe Term))) Term
>   where
>     probType _ = star

> instance Problem (From Variable (TermShape,Term ::: (Maybe Term))) Term
>   where
>     probType _ = star
>     refine q@(From _ (_,_ ::: Just ty)) = solved ty q

> instance Problem (From () Params) () where
>   refine (From () Zip) =
>     solved () $ From (CEmpty :: CSigs LName) ()
>   refine (From () (pz :<: (_ :=: o))) = do
>     (pzn,_) <- elabTerm "pz" $ From () pz
>     (on,_) <- elabTerm "o" $ From () o
>     solved () $ From (CSigs (CSigsoid pzn) (CSigsoid on)) ()

> instance (Displayable x,Displayable y) => Displayable (x ::: y) where
>   display ew ctxt (x ::: y) = gColon (display ew ctxt x) (display ew ctxt y)

> instance Problem (From () Object) () where
>   refine (From () (unom :=: (ok,_ ::: ty))) = do
>     (tyn,_) <- elabTerm "ty" $ From () (TermPlease,ty ::: Just star)
>     solved () $ Variable (Just ok) unom ::: CTermoid tyn

> instance Updatable (CHead LName)
> instance Problem (Variable ::: (CHead LName)) ()




******************************************************************************
Programs
******************************************************************************

> instance Displayable x => Displayable (CProg x) where
>   display ew ctxt = box . up (display ew ctxt)

> instance Displayable x => Displayable (CLhs x) where
>   display ew ctxt = box . up (display ew ctxt)

> instance Displayable x => Displayable (CRhs x) where
>   display ew ctxt = box . up (display ew ctxt)

> instance Displayable x => Displayable [CRhs x] where
>   display ew ctxt = seqB gRhs . up (display ew ctxt)

> instance Displayable x => Displayable (CProgs x) where
>   display ew ctxt = box . up (display ew ctxt)


------------------------------------------------------------------------------
Compute a programming problem from a declaration
------------------------------------------------------------------------------

> progProb :: UName -> [(Visibility,UName)] -> Term -> Maybe (Term,Term)
> progProb f vus ty = bof 0 Zip Zip vus ty where
>   bof :: Int -> Params -> Zip Term -> [(Visibility,UName)] -> Term ->
>          Maybe (Term,Term)
>   bof i del az ((UnifV,UN s) : vus) (TBind All (_,UnifV) dr) =
>     let ((pa,va),r) = (voon /// ("X",i) /// s) .| TBind All (UN s,UnifV) dr
>     in  bof (i + 1) (del :<: pa)
>         (az :<: TF (U_ Shown) :<: (track ("Shown " ++ s ++ "\n") va)) vus r
>   bof i del az vus t@(TBind All (UN s,UnifV) _) =
>     let ((pa,va),r) = (voon /// ("X",i) /// s) .| t
>     in  bof (i + 1) (del :<: pa)
>         (az :<: TF (U_ Hidden) :<: (track ("Hidden " ++ s ++ "\n") va))
>         vus r
>   bof i del az ((NormV,UN s) : vus) t@(TBind All (_,NormV) dr) =
>     let ((pa,va),r) = (voon /// ("X",i) /// s) .| TBind All (UN s,NormV) dr
>     in  bof (i + 1) (del :<: pa)
>         (az :<: (track ("Normal " ++ s ++ "\n") va)) vus r
>   bof i del az [] ty | clearlyNotImplicit ty =
>     let sdel = pShow del
>         lab = Label (f ::: (del |- ty)) az {-(parArg <!> del)-} Zip
>         prob = sdel |- TF (Lbl LabTy lab ty)
>         (pS,vS) = decl (voon /// "S") (UN "") Lam NormV $ prob
>         pack = (zOne pS <+> pLam del) |- vS @@ sdel @@ Call lab
>     in  Just (prob,pack)
>   bof i _ _ _ _ = m0


------------------------------------------------------------------------------
Elaborating a program wrt a problem
------------------------------------------------------------------------------

Note, if the program is missing, this is easy. Just construct the lhs
from the label, then make a hole for the rhss!

It's harder if the f***er has already written the program!

> instance Problem (From (Maybe (CProg LName)) Term) Term where
>   probType (From _ prob) = prob

> noProg :: Maybe (CProg Lexical)
> noProg = Nothing

> noProgs :: Maybe (CProgs Lexical)
> noProgs = Nothing

> instance Problem (From (Maybe (CProg Lexical)) Term) Term where
>   probType (From _ prob) = prob
>   refine q | track (show q) False = stuck
>   refine (From _ prob) | Might True <- unclear prob = stuck
>   refine (From Nothing (TBind All (UN "", vis) sem)) =
>     refine (From noProg (TBind All (UN "x", vis) sem))
>   refine (From Nothing (TBind All (unom@(UN s),vis) (Sem (Just dom) ran))) =
>     do _ <- seekUName unom
>        reduced $ From noProg
>                    (TBind All (UN (s ++ "'"),vis) (Sem (Just dom) ran))
>     <+>
>     do va <- lamPush vis unom dom
>        reduced $ From noProg (ran va)
>   refine (From Nothing prob@(TF (Lbl LabTy lab ty))) = do
>     (ln,lhb) <- private "Lhs" Zip . await (Elab,QTerm) $ From () lab
>     (rn,tac) <- private "Rhs" Zip . await (Elab,QTerm) . When lhb $
>                   From [CRhssoid emptyEDoc] (lab ::: ty)
>     reduced $ ProgTac (ln,rn) Nothing tac prob
>   refine (From mp@(Just _) (TBind All (UN s,vis) (Sem (Just dom) ran))) = do
>     va <- lamPush vis (UN (brace s)) dom
>     reduced $ From mp (ran va)
>     where
>       brace s@('{' : _) = s
>       brace s = "{" ++ s ++ "}"
>   refine (From (Just (CProg lhs rhss mps)) prob@(TF (Lbl LabTy lab ty))) = do
>     (ln,lhb) <- private "Lhs" Zip . await (Elab,QTerm) $ From lhs lab
>     (rn,tac) <- private "Rhs" Zip . await (Elab,QTerm) . When lhb $
>                   From rhss (lab ::: ty)
>     reduced $ ProgTac (ln,rn) mps tac prob
>   refine _ = stuck

> data ProgTac = ProgTac (LName,LName) (Maybe (CProgs Lexical)) Term Term
>   deriving Show

> instance Displayable ProgTac where
>   display ew ctxt (ProgTac (ln,rn) mps _ _) =
>     box (CProg (CLhsoid (display ew ctxt ln))
>                [CRhssoid (display ew ctxt rn)]
>                (up (up (display ew ctxt)) mps))

> instance Updatable ProgTac where
>   upd bull (ProgTac lr mps t p) =
>     eta (ProgTac lr mps) <$> upd bull t <$> upd bull p

> instance Problem ProgTac Term where
>   probType (ProgTac _ _ _ p) = p
>   export _ _ q | track (show q) False = stuck
>   export del work (ProgTac (ln,rn) mps tac prob)
>     | Must True <- happy <!> work
>     = do (nsub,vsub) <- publicNoLift "Sub" Zip . await (Elab,QTerm) $
>            From mps (tac @@ pi1)
>          let sol = tac @@ pi2 @@ vsub
>          del <- getDel
>          track ("PROG: " ++ show (del |- sol)) $ return ()
>          return (work <>> nil,
>                  Solved sol,ProbFor $
>                  From (CProg (CLhsoid ln) [CRhssoid rn]
>                        (Just (CProgsoid nsub))) ())
>     | otherwise = stuck
>     where
>       happy (Name _ (Waiting _ _ (Prob Satisfied _ _)) _) = m0
>       happy _ = Must False
>   suppressesYellow _ = True -- filthy hack

> instance Problem (From (CProg LName) ()) Term

------------------------------------------------------------------------------
Make an lhs from the problem
------------------------------------------------------------------------------

> instance Problem (From Variable ()) () where
>   refine = solved () 

> instance Problem (From () (Label Term)) (Boole LName) where
>   refine q | track (show q) False = stuck
>   refine (From _ (Label (f ::: fty) az wWz)) = do
>     pf <- seekUName f
>     (fn,_) <- elabTerm "f" $ From (Variable (Just ObjDefn) f) ()
>     (fan,_) <- elabTerm "fa" $
>       From (AppPlease,zOne (CTermoid fn)) (fty,az <>> nil)
>     lhs <- eta (CLhs (zOne (CTermoid fan))) <$> (wblat <^> wWz)
>     solved (BVal True) (From lhs ())
>     where wblat (w ::: wt) = do
>             (wn,_) <- elabTerm "w" $ From () (TermPlease,w ::: Just wt)
>             return $ CTermoid wn

> instance Problem (From (CLhs LName) ()) (Boole LName)


------------------------------------------------------------------------------
Check an lhs
------------------------------------------------------------------------------

> unapps :: Term -> Refine (Term,List Term)
> unapps (TF (Con c unom nom az)) =
>   return (TF (Con c unom nom Zip),az <>> nil)
> unapps (TElim h ez) = rev ez nil where
>   rev (ez :<: A t) ts = rev ez (t :>: ts)
>   rev (ez :<: Call (Label (f ::: _) az _)) ts = do
>     (nom :=: _ :=: (_,_ ::: _)) <- seekUName f
>     return (nmTm nom,az <>> ts)
>   rev ez ts = return (TElim h ez,ts)
> unapps t = return (t,nil)

> instance Problem (From (CLhs LName) BOOLE) (Boole LName)

> instance Problem (From (CLhs Lexical) (Label Term)) (Boole LName) where
>   refine q | track (show q) False = stuck
>   refine (From (CLhs faz wz) (Label (f ::: fty) az wWz)) = do
>     (nom :=: _ :=: (_,_ ::: _)) <- seekUName f
>     (fan,fab) <- elabTerm "fa" $ From (faz <>> nil) (nmTm nom,az <>> nil)
>     (wnz,wwb) <- blat fab wz wWz
>     reduced . When wwb . Solve (BVal True) $
>       From (CLhs (zOne (CTermoid fan)) wnz) BOOLE
>     where
>       blat b Zip _ = return (Zip,b)
>       blat b (wz :<: lw) (wWz :<: (w ::: _)) = do
>         (wnz,wwb) <- blat b wz wWz
>         (wn,wwb') <- elabTerm "w" . When wwb $ From lw w
>         return (wnz :<: CTermoid wn,wwb')
>       blat b (wz :<: w) Zip = do
>         (wnz,wwb) <- blat b wz Zip
>         (wn,wwb') <- elabTerm "w" . When (BVal False) $ From w star
>         return (wnz :<: CTermoid wn,BVal False)
>   refine _ = stuck

> instance Displayable (List (CHead Lexical)) where
>   display ew gam as = display ew gam (Zip <>< as)

> instance Displayable UName where
>   display ew gam unom = box unom

> instance Problem
>     (From (List (CHead Lexical)) (Term,List Term)) (Boole LName) where
>   refine (From (CRefl :>: Tip _) (r@(TF (JMRefl _)),Tip _)) = do
>     (rn,_ :: Term) <- elabTerm "r" $ (From () (TermPlease,r ::: noType))
>     solved (BVal True) (From (CRefl :: CHead LName) BOOLE)
>   refine (From (CVar _ unom :>: las) (f,as)) = do
>     (fn,fb) <- elabTerm "f" $ From unom f
>     (hz,b) <- blat (zOne (CTermoid fn),fb) las as
>     solved b (From (CApp hz) BOOLE)
>     where
>       blat :: (Zip (CHead LName),Boole LName) -> List (CHead Lexical) ->
>               List Term -> Refine (Zip (CHead LName),Boole LName)
>       blat hzb (Tip _) (Tip _) = return hzb
>       blat (hz,b) (CUnder :>: las) (TF (U_ _) :>: as) =
>         blat (hz :<: CUnder,b) las as
>       blat hzb las (TF (U_ _) :>: _ :>: as) = blat hzb las as
>       blat (hz,b) (la :>: las) (a :>: as) = do
>         (an,b') <- elabTerm "a" . When b $ From la a
>         blat (hz :<: CTermoid an,b') las as
>       blat (hz,b) (Tip _) _ = return (hz,BVal False)
>       blat (hz,b) (la :>: las) (Tip _) = do
>         (an,b') <- elabTerm "a" . When (BVal False) $ From la star
>         blat (hz :<: CTermoid an,BVal False) las nil
>   refine _ = stuck

> instance Problem (From (CHead LName) BOOLE) (Boole LName)
> instance Problem (From (CTerm LName) BOOLE) (Boole LName)
> instance Problem (From Variable BOOLE) (Boole LName)

> instance Problem (From UName Term) (Boole LName) where
>   refine (From unom (TF (Con c unam _ Zip))) =
>     uMatch unom (ObjDecl c) unam
>   refine (From unom (TElim (Var (F x)) Zip)) = do
>     Rightmost (unam :=: (ok,_)) <- get $ varObj x
>     case unam of
>       UN ('{': _ ) -> reduced $ PickName x unom
>       _ -> uMatch unom ok unam
>   refine _ = stuck

> uMatch :: UName -> ObjKind -> UName -> Refine (Boole LName)
> uMatch unom ok unam | unom == unam = do
>   solved (BVal True) (From (Variable (Just ok) unom) BOOLE)
> uMatch unom _ _ = do
>   solved (BVal False) (From (Variable Nothing unom) BOOLE)

> instance Problem (From (CHead Lexical) Term) (Boole LName) where
>   refine (From (CTuple [lt]) t) = do
>     (tn,tb) <- elabTerm "t" $ From lt t
>     solved tb $ From (CTuple [CApp (zOne (CTermoid tn))]) BOOLE
>   refine (From h t) =
>     reduced $ From (CApp (zOne h)) t

> instance Problem (From (CTerm Lexical) Term) (Boole LName) where
>   refine (From (CApp hz) tm) = do
>     fas <- unapps tm
>     reduced $ From (hz <>> nil) fas
>   refine (From (CBind b sigs range) tm) = track "Into Bind" $ do
>     (sen,ser) <- private "S" Zip . await (Elab,QDecl) $
>       From sigs (b, tm)
>     (ran,rab) <- private "T" Zip . await (Elab,QTerm) $
>       From range ser
>     reduced $
>       From (CBind b (CSigsoid sen) (CApp (zOne (CTermoid ran))))
>         (DischargeBoole rab)
>   refine (From (CEquals hz1 hz2) (TF (JMEq (t1 ::: y1) (t2 ::: y2)))) = do
>     (qn1,qb1) <- elabTerm "L" $ From (CApp hz1) t1
>     (qn2,qb2) <- elabTerm "R" $ From (CApp hz2) t2
>     solved (bAnd qb1 qb2) $
>       From (CEquals (zOne (CTermoid qn1)) (zOne (CTermoid qn2))) BOOLE
>   refine _ = stuck

> instance Updatable Bind where
>   upd bull b = eta b

> instance Problem (From (CSigs LName) Bind) Term

> instance Problem (From (CSigs Lexical) (Bind, Term)) Term where
>   refine (From CEmpty (b, ran)) =
>     solved ran $ From (CEmpty :: CSigs LName) b
>   refine (From (CSigs ss1 ss2) (b, ran)) = do
>     (sen1, ser1) <- elabDecl "S" $ From ss1 (b, ran)
>     (sen2, ser2) <- elabDecl "R" $ From ss2 (b, ser1)
>     solved ser2 $ From (CSigs (CSigsoid sen1) (CSigsoid sen2)) b
>   refine (From (CSig sig) bran) =
>     reduced $ From sig bran
>   refine _ = stuck

> instance Problem (From (CSig Lexical) (Bind, Term)) Term where
>   refine (From _ (_, t)) | Might True <- unclear t = stuck
>   refine (From (CSimple [CParam _ vis unom] mty) (b, tm)) = case tm of
>     TBind b' (_, vis') (Sem mdom ran) | b == b', vis == vis' ->
>       let dom = prefer mdom star -- that's such a dodgy dummy
>       in case mty of
>            Nothing -> track "Unlabelled Lambda" $ do
>              (xn,x) <- elabDecl "x" $ Declare unom (ObjAbst All vis) dom
>              solved (ran x) $
>                From (CSig (CSimple [CParam True vis unom] Nothing)
>                      :: CSigs LName) b
>            Just cdom -> track "Labelled Lambda" $ do
>              (dn,db) <- elabTerm "D" $ From cdom dom
>              (xn,x) <- elabDecl "x" $ Declare unom (ObjAbst All vis) dom
>              reduced . When db . Solve (ran x) $
>                From (CSig (CSimple [CParam True vis unom]
>                            (Just (CApp (zOne (CTermoid dn)))))) b
>     _ -> failed 
>   refine _ = stuck

> data PickName = PickName LName UName deriving Show

> instance Updatable PickName where
>   upd bull (PickName nom unom) = eta (PickName nom) <$> upd bull unom

> instance Displayable PickName where
>   display _ _ (PickName _ unom) = box unom

> instance Problem PickName (Boole LName) where
>   refine (PickName nom u) = do
>     nam :=: _ :=: (ok,_) <- seekUName u
>     if nom == nam
>       then solved (BVal True) (From (Variable (Just ok) u) BOOLE)
>       else solved (BVal False) (From (Variable Nothing u) BOOLE)
>   shock (PickName nom u) lz = bif lz where
>     bif (Zip :<: _) = m0
>     bif (lz :<: Layer root del (ez :*: es) prob im)
>       | Just del' <- bof del
>       = Just (lz :<: Layer root del' (ez :*: News (story (UStory u)) :>: es)
>                        prob im)
>     bif lz = bif (outRight lz)
>     bof Zip = m0
>     bof (del :<: (nam :=: UN ('{':_) :=: ott)) | nam == nom =
>       Just (del :<: (nom :=: u :=: ott))
>     bof (del :<: p) = up (:<: p) (bof del)



------------------------------------------------------------------------------
Compute an LCF-style problem decomposition from an rhs
------------------------------------------------------------------------------

> instance Problem (From [CRhs LName] ()) Term

> instance Problem (From [CRhs Lexical] ((Label Term) ::: Term)) Term where
>   probType (From _ (l ::: t)) =
>     TBind Ex  dull . Sem (Just star) $ \ sus ->
>     TBind All dull . Sem (Just sus)  $ \ _ ->
>     TF (Lbl LabTy l t)
>   refine q | track (show q) False = stuck
>   refine (From [CRhssoid lexi] lt) = reduced $ From lexi lt
>   refine (From [CRet t] (lab ::: ty)) = do
>     (nt,vt) <- elabTerm "t" $ From t (Check Recce TermPlease ty)
>     solved (pair (TF One) (TBind Lam dull (Sem Nothing{-(TF One)-}
>                             (const (TF (Lbl Return lab vt))))))
>            (From [CRet . CApp . zOne $ CTermoid nt] ())
>   refine (From [CBy e] lt) = do
>     (ne,ve) <- elabTerm "e" $ From e (Infer Recce TermPlease)
>     eb <- compute "eb" $ IsEliminatorType (ve @@ pi1)
>     reduced . When eb $
>       From [CBy (CApp (Zip :<: CTermoid ne))] (Split (llec ve) lt)
>   refine _ = stuck

> data Split = Split (Term ::: Term) ((Label Term) ::: Term) deriving Show

> instance Updatable Split where
>   upd bull (Split e t) = eta Split <$> upd bull e <$> upd bull t

> instance Problem (From [CRhs LName] Split) Term where
>   probType (From _ (Split _ (l ::: t))) =
>     TBind Ex  dull . Sem (Just star) $ \ sus ->
>     TBind All dull . Sem (Just sus)  $ \ _ ->
>     TF (Lbl LabTy l t)
>   refine q@(From _ (Split etty@(_ ::: ety)
>                    (lab@(Label (uno ::: _) _ _) ::: ty))) = do
>     del <- popOut getDel
>     root <- getRoot
>     let paranoia =
>           if un (inductive ety)
>             then track "IND" $ \ (_ :=: _ :=: (_,_ ::: pty)) ->
>                    labial uno 0 pty
>             else track "INV" m0
>     wham <- ewam paranoia etty [] (root :=: (del,TF (Lbl LabTy lab ty)))
>             >>= onSubgoals simpUnify
>     track (show wham) $ return ()
>     tac <- packRefinement wham
>     track (show tac) $ return ()
>     solved tac q

> inductive :: Term -> Might
> inductive (TBind All _ (Sem dom ran)) = indMethods 0 (ran (nmTm voon)) where
>   indMethods :: Int -> Term -> Might
>   indMethods i (TBind All (u, _) (Sem (Just dom) ran)) =
>     indMethod i dom <+> indMethods (i + 1) (ran (var i u))
>   indMethods _ _ = m0
>   indMethod :: Int -> Term -> Might
>   indMethod i (TBind All (u, _) (Sem (Just dom) ran)) =
>     dep [voon] dom <+> indMethod (i + 1) (ran (var i u))
>   indMethod _ _ = m0
> inductive _ = m0

> instance Editor [CRhs Lexical] ((Label Term) ::: Term) Term where
>   editType (l ::: t) = 
>     TBind Ex  dull . Sem (Just star) $ \ sus ->
>     TBind All dull . Sem (Just sus)  $ \ _ ->
>     TF (Lbl LabTy l t)
>   editParser _ = iPP (pSeq1 blah iSkip)
>   editInfo (l ::: t) = do
>     (ln,_) <- elabTerm "pp" $ do
>       (labn,_) <- private "lab" Zip . await (Elab,QTerm) $ From () l
>       (tyn,_) <- private "ty" Zip . await (Elab,QTerm) $
>         From () (TermPlease,t ::: Just star)
>       solved () $ From (labn ::: tyn) ()
>     return ln

> instance Problem (From (LName ::: LName) ()) () where
>   refine q = solved () q

------------------------------------------------------------------------------
Solve subproblems from subprograms
------------------------------------------------------------------------------

> instance Problem (From (CProgs LName) ()) Term where {}

> instance Problem (From (Maybe (CProgs Lexical)) Term) Term where
>   probType (From _ probs) = probs
>   refine q | track (show q) False = stuck
>   refine (From _ probs) | Might True <- unclear probs = stuck
>   refine (From Nothing probs) = do
>     (ans,a) <- blat probs
>     solved a (From (CProgs ans) ())
>     where
>       blat (TF One) = return ([],TF Only)
>       blat (TBind Ex _ (Sem (Just dom) ran)) = do
>         (dns,d) <- blat dom
>         (rns,r) <- blat (ran d)
>         return (dns ++ rns,pair d r)
>       blat p | Might False <- unclear p = do
>         (sn,sprog) <- elabTerm "sprog" $ From noProg p
>         return ([CProgoid sn],sprog)
>       blat _ = stuck
>   refine (From (Just (CProgs progs)) probs) = do
>     (ans,a,[]) <- blat progs probs
>     solved a (From (CProgs ans) ())
>     where
>       blat :: [CProg Lexical] -> Term ->
>               Refine ([CProg LName],Term,[CProg Lexical])
>       blat progs (TF One) = return ([],TF Only,progs)
>       blat progs0 (TBind Ex _ (Sem (Just dom) ran)) = do
>         (dns,d,progs1) <- blat progs0 dom
>         (rns,r,progs2) <- blat progs1 (ran d)
>         return (dns ++ rns,pair d r,progs2)
>       blat (prog : progs) prob | Might False <- unclear prob = do
>         (sn,sprog) <- elabTerm "sprog" $ From (Just prog) prob
>         return ([CProgoid sn],sprog,progs)
>       blat [] prob | Might False <- unclear prob = do
>         (sn,sprog) <- elabTerm "sprog" $ From noProg prob
>         return ([CProgoid sn],sprog,[])
>       blat _ _ = stuck
>   refine _ = stuck


******************************************************************************
Some helpers
******************************************************************************

> instance Displayable x => Displayable (Maybe x) where
>   display ew ctxt (Just x) = display ew ctxt x
>   display _ _ _ = box0
