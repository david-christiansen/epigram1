*****************************************************************************
**********                                                          **********
**********     Igor.lhs --- the faithful lab assistant              **********
**********                                                          **********
******************************************************************************

> module Igor where

> import Utils
> import Category
> import Monadics
> import Logic
> import Zip
> import Name
> import ObjKind
> import Term
> import Doc
> import Box
> import Emacs
> import Update
> import Boole
> import Emacs

> import Debug.Trace

******************************************************************************
Problem
******************************************************************************

> class -- (Displayable q,Updatable q,Show q,
>       -- Reportable a,Show a) =>
>       Problem q a | q -> a where
>   refine :: q -> Refine a
>   refine _ = stuck
>   export :: Params -> Zip Entry -> q ->
>             Refine (List Entry,QStatus a,ProbFor a)
>   export _ _ _ = stuck
>   shock :: q -> Ctxt -> Maybe Ctxt   -- for nonlocal actions
>   shock = m0
>   event :: q -> QStatus a -> Event -> Interactive ()
>   event _ _ _ = return ()
>   probType :: q -> Term
>   probType _ = TF Bot -- really should be overridden!
>   gadgets :: q -> UName -> Rightmost [Gadget]
>   gadgets = m0
>   varCatch :: q -> Maybe (Zip (UName :=: LName))
>   varCatch = m0
>   seeksVar :: q -> Maybe UName
>   seeksVar = m0
>   seeksName :: q -> Bool
>   seeksName _ = False
>   suppressesYellow :: q -> Bool
>   suppressesYellow _ = False
>   localInfo :: q -> Refine LName
>   localInfo _ = doo m0

> data Dummy = Dummy deriving Show

> instance Updatable Dummy
> instance Displayable Dummy
> instance Problem Dummy ()


******************************************************************************
Entry and Entity
******************************************************************************

> data Entry
>   = Name Root Entity Image
>   | News Bulletin
>   | Swoon
>   | RefMark

> type Root = (LName,Int)

> data Entity
>   = Object Object
>   | Waiting Params (List Entry) Prob
>   | Hoping UName Params Term

> data Prob = forall q a . (Displayable q,Updatable q,Show q,
>                           Updatable a,Reportable a,Show a,
>                           Problem q a )
>   => Prob (QStatus a) QKind q

> data ProbFor a = forall q. (Displayable q,Updatable q,Show q,
> --                          Updatable a,Reportable a,Show a,
>                           Problem q a )
>   => ProbFor q

> instance Show Prob where
>   show (Prob s (x,y) q) = concat [show s," ",show x,show y," ",show q]

> data QPersist = Elab | Compute deriving Eq

> instance Show QPersist where
>   show Elab = "E"
>   show Compute = "C"

> data QProduce = QDecl | QTerm deriving Eq

> instance Show QProduce where
>   show QDecl = "D"
>   show QTerm = "T"

> type QKind = (QPersist,QProduce)

> data QStatus a
>   = Failed
>   | Pending PendWhat
>   | Solved a
>   | Satisfied
>   deriving Show

> shade :: QStatus a -> Params -> Bool -> Bool -> Boxings -> Boxings
> shade s del curb syelb = shs s del . shc curb where
>   shs Failed _ = faceB fError
>   shs (Pending _) _ {-Zip-} | not syelb = faceB fWarning
>   shs _ _ = id
>   shc True = faceB fForeground
>   shc _ = id

> data Image = ImOld Bool Boxings | ImNew

> instance Show Image where
>   show _ = ""

> data PendWhat = Refine | Shock | MoreInfo deriving Show

> data Layer = Layer Root Params (Cursor Entry) Prob Image deriving Show

> type Ctxt = Zip Layer

> type Refine = State Maybe Ctxt

> instance Show Ctxt where
>   show lz | (s1,s2) <- blat lz = s1 ++ "YOU ARE HERE\n" ++ s2 where
>     blat Zip = ("","")
>     blat (lz :<: Layer (nom,_) del (ez :*: es) prob _) | (s1,s2) <- blat lz =
>      (concat [
>         s1,
>         "LAYER[ " ++ show nom ++ "\n",
>         zosh "DEL" del,
>         show ez
>         ],
>       concat [
>         show es,
>         " |- ",show prob,"\n",
>         "]LAYER\n",
>         s2
>         ])

> instance Show Entry where
>   show (Name (nom,_) ent _) = show nom ++ " " ++ show ent
>   show (News (Bulletin ss)) = show "NEWS[\n" ++ show ss ++ "]NEWS"
>   show Swoon = "SWOON"
>   show RefMark = "REFMARK"

> instance Show Entity where
>   show (Object o) = show o
>   show (Waiting del work prob) = concat
>     ["PROB ",show prob,"\n",zosh "DEL" del,losh "WORK" work,"--------\n"]
>   show (Hoping unom del ty) = concat
>     ["HOPE ",show unom," : ",show ty,"\n",zosh "DEL" del,"--------\n"]


******************************************************************************
Lifters
******************************************************************************

> layer :: (Layer -> Layer) -> Ctxt -> Ctxt
> layer f (ctxt :<: l) = ctxt :<: f l
> layer _ _ = error "layer in empty context"

> cursor :: (Cursor Entry -> Cursor Entry) -> Layer -> Layer
> cursor f (Layer root del cur prob im) = Layer root del (f cur) prob im


******************************************************************************
Navigation
******************************************************************************

> outLay :: Layer -> Entry
> outLay (Layer root del ezs prob im)
>   = Name root (Waiting del (curList ezs) prob) im

> outLeft :: Ctxt -> Ctxt
> outLeft (lz :<: Layer root del (ez :*: es) prob im :<: l)
>   = lz :<: Layer root del (ez :<: outLay l :*: es) prob im

> outRight :: Ctxt -> Ctxt
> outRight (lz :<: Layer root del (ez :*: es) prob im :<: l)
>   = lz :<: Layer root del (ez :*: outLay l :>: es) prob im

> inLay :: Entry -> Layer
> inLay (Name root (Waiting del es prob) im)
>   = Layer root del (Zip :*: es) prob im

> inLeft :: Ctxt -> Ctxt
> inLeft (lz :<: Layer root del (ez :<: e :*: es) prob im)
>   = lz :<: Layer root del (ez :*: es) prob im :<: inLay e

> inRight :: Ctxt -> Ctxt
> inRight (lz :<: Layer root del (ez :*: e :>: es) prob im)
>   = lz :<: Layer root del (ez :*: es) prob im :<: inLay e

> origin :: Ctxt -> Ctxt
> origin Zip = error "origin Zip"
> origin (Zip :<: Layer root del (ez :*: es) prob im)
>   = Zip :<: Layer root del (Zip :*: (ez <>> es)) prob im
> origin ctxt = origin (outRight ctxt)

> focus :: LName -> Ctxt -> Ctxt  -- could be implemented better
> focus nom ctxt | track ("Focus " ++ show nom) False = ctxt
> focus nom done@(lz :<: Layer root@(nam,_) del (ez :*: es) prob im)
>   | nom == nam = done
> focus nom ctxt = let ctxt' = foc (origin ctxt)
>                  in  track ("Focused " ++ show (whereAmI ctxt')) ctxt' where
>   foc done@(lz :<: Layer root@(nam,_) del (ez :*: es) prob im)
>     | nom == nam = done
>   foc ctxt@(lz :<:
>     Layer _ _ (ez :*: Name root@(nam,_) (Waiting _ _ _) _ :>: es) _ _)
>     | nam <= nom = foc (inRight ctxt)
>   foc ctxt@(lz :<:
>     Layer _ _ (ez :*: Name root@(nam,_) _ _ :>: es) _ _)
>     | nam == nom = ctxt
>   foc (lz :<: Layer root del (ez :*: e :>: es) prob im)
>     = foc (lz :<: Layer root del (ez :<: e :*: es) prob im)
>   foc ctxt = ctxt


******************************************************************************
Refinement
******************************************************************************

> getRoot :: Refine Root
> getRoot =
>   do (_ :<: Layer root _ _ _ _) <- get id
>      return root

> getDel :: Refine Params
> getDel =
>   do (_ :<: Layer _ del _ _ _) <- get id
>      return del

> setDel :: Params -> Refine ()
> setDel del =
>   do (lz :<: Layer root _ work prob _) <- get id
>      set (lz :<: Layer root del work prob ImNew)

> whereAmI :: Ctxt -> LName
> whereAmI (_ :<: Layer (nom,_) _ _ _ _) = nom
> whereAmI _ = Long Zip

> child :: String -> Refine Root
> child x =
>   do (lz :<: Layer (nom,non) del ezs prob im) <- get id
>      set (lz :<: Layer (nom,non + 1) del ezs prob im)
>      return (nom /// (x,non),0)

> param :: ObjKind -> UName -> Term -> Refine (Param,Term)
> param ok unom@(UN s) dom = do
>   root@(nom,_) <- child s
>   let v = TElim (Var (F nom)) Zip
>   return (nom :=: unom :=: (ok,v ::: dom),v)

> locdef :: UName -> (Term ::: Term) -> Refine (Param,Term)
> locdef unom@(UN s) tty@(v ::: _) = do
>   root@(nom,_) <- child s
>   return (nom :=: unom :=: (ObjDefn,tty),v)

> parPush :: UName -> Term -> Refine Term
> parPush unom dom = do
>   (b,t) <- param ObjPar unom dom
>   del <- getDel
>   setDel (del :<: b)
>   return t

> lamPush :: Visibility -> UName -> Term -> Refine Term
> lamPush vis unom dom = do
>   (b,t) <- param (ObjAbst Lam vis) unom dom
>   del <- getDel
>   setDel (del :<: b)
>   return t

> allPush :: Visibility -> UName -> Term -> Refine Term
> allPush vis unom dom = do
>   (b,t) <- param (ObjAbst All vis) unom dom
>   del <- getDel
>   setDel (del :<: b)
>   return t

> popOut :: Refine a -> Refine a
> popOut rfn = do
>   tweak outRight
>   a <- rfn
>   tweak inRight
>   return a

> public :: Apply a Param =>
>           String -> Params -> 
>           (Params -> Root -> Refine a) -> Refine (LName,a)
> public x del' refiner =
>   do root <- child x
>      del <- getDel
>      pdel <- return $ parify <!> del
>      a <- popOut $ refiner (pdel <+> del') root
>      return (fst root,a @@ pdel)

> publicNoLift :: Apply a Param =>
>           String -> Params -> 
>           (Params -> Root -> Refine a) -> Refine (LName,a)
> publicNoLift x del' refiner =
>   do root <- child x
>      a <- popOut $ refiner del' root
>      return (fst root,a)

> ppublic :: Apply a Param =>
>           String -> Params -> 
>           (Params -> Root -> Refine (a,y)) -> Refine (LName,(a,y))
> ppublic x del' refiner =
>   do root <- child x
>      del <- getDel
>      pdel <- return $ parify <!> del
>      (a,y) <- popOut $ refiner (pdel <+> del') root
>      return (fst root,(a @@ pdel,y))

> private :: String -> Params -> (Params -> Root -> Refine a) ->
>              Refine (LName,a)
> private x del refiner =
>   do root <- child x
>      a <- refiner del root
>      return (fst root,a)

> enter :: Entry -> Refine ()
> enter e = tweak (layer . cursor $ curIns e)

> forwardEnter :: Entry -> Refine ()
> forwardEnter e = tweak (layer . cursor $ (unjust . curUp . curIns e))

> subEntries :: Zip Entry -> Refine ()
> subEntries ez = popOut $ sequentially enter ez

> refMark :: Refine ()
> refMark = popOut $ enter RefMark

> kramFer :: Refine ()
> kramFer = tweak kf where
>   kf (lz :<: Layer root del (ez :<: RefMark :*: es) prob im)
>      = lz :<: Layer root del (ez :*: es) prob im
>   kf (lz :<: Layer root del (ez :<: e :*: es) prob im)
>      = kf (lz :<: Layer root del (ez :*: e :>: es) prob im)
>   kf lz = kf (outRight lz)

> failed :: Reportable a => Refine a
> failed
>   = do (lz :<: Layer root@(nom,_) del ezs (Prob _ k q) _) <- get id
>        set (lz :<: Layer root del ezs (Prob Failed k q) ImNew)
>        track ("failed " ++ show nom ++ " " ++ show q) $ return ()
>        return (wait nom)

> solved :: (Updatable q,Displayable q,Show q,
>            Updatable a,Reportable a,Show a,Problem q a) => a -> q -> Refine a
> solved a q
>   = do (lz :<: Layer root@(nom,_) del ezs (Prob _ k _) _) <- get id
>        set (lz :<: Layer root del ezs (Prob (Solved a) k q) ImNew)
>        let x = del |- a
>        track ("solved " ++ show nom ++ " = " ++ show x) $ return x

> tryRefine :: (Updatable q,Displayable q,Show q,
>               Updatable a,Reportable a,Show a,Problem q a) => q -> Refine a
> tryRefine q =
>   do track "tryRefine" $ return ()
>      refine q
>   <+>
>   do (lz :<: Layer root@(nom,_) del (work :*: Tip _)
>          (Prob (Pending _) k _) im) <- get id
>      (es,stat,ProbFor q') <- export del work q
>      del' <- getDel
>      track ("EXPORT: " ++ show del') $ return ()
>      tweak (zPop 1)
>      tweak (:<: Layer root del' ((Zip <>< es) :*: nil)
>                  (Prob stat k q') ImNew)
>      statusAction stat del' q'
>   <+>
>   do (lz :<: Layer root@(nom,_) del ezs (Prob _ k _) im) <- get id
>      track "didn't refine" $ return ()
>      set (lz :<: Layer root del ezs (Prob (Pending Shock) k q) im)
>      return (wait nom)

> statusAction :: (Updatable q,Displayable q,Show q,
>                 Updatable a,Reportable a,Show a,Problem q a) =>
>                 QStatus a -> Params -> q -> Refine a
> statusAction (Pending Refine) _ q = do
>   tryRefine q
> statusAction (Solved a) del q = return (del |- a)
> statusAction _ _ _ =
>   do (nom,_) <- getRoot
>      return (wait nom)

> reduced :: (Updatable q,Displayable q,Show q,
>             Updatable a,Reportable a,Show a,Problem q a) => q -> Refine a
> reduced q
>   = do (lz :<: Layer root@(nom,_) del ezs (Prob _ k _) _) <- get id
>        set (lz :<: Layer root del ezs (Prob (Pending Refine) k q) ImNew)
>        track ("reduced " ++ show nom) $ tryRefine q

> await :: (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>           QKind -> q -> Params -> Root -> Refine a
> await k q del root@(nom,_) =
>   do tweak (:<: Layer root del cur0 (Prob (Pending Refine) k q) ImNew)
>      a <- track ("aw refines " ++ show nom) $ tryRefine q
>      tweak tidy
>      return a

> suspend :: (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>           QKind -> q -> Params -> Root -> Refine a
> suspend k q del root@(nom,_) =
>   do tweak (:<: Layer root del cur0 (Prob (Pending Refine) k q) ImNew)
>      tweak tidy
>      return (wait nom)

> qwait :: (Updatable q,Displayable q,Show q,
>           Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>           QKind -> Refine (q,x) -> Params -> Root -> Refine (a,x)
> qwait k rq del root@(nom,_) =
>   do tweak (:<: Layer root del cur0 (Prob (Pending Refine) k Dummy) ImNew)
>      (q,x) <- rq
>      tweak (zPop 1)
>      tweak (:<: Layer root del cur0 (Prob (Pending Refine) k q) ImNew)
>      a <- track ("aw refines " ++ show nom) $ tryRefine q
>      tweak tidy
>      return (a,x)

> elabDecl :: (Updatable q,Displayable q,Show q,
>              Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>              String -> q -> Refine (LName,a)
> elabDecl s q = do
>   public s Zip $ await (Elab,QDecl) q

> elabTerm :: (Updatable q,Displayable q,Show q,
>              Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>              String -> q -> Refine (LName,a)
> elabTerm s q = do
>   public s Zip $ await (Elab,QTerm) q

> compute :: (Updatable q,Displayable q,Show q,
>              Updatable a,Reportable a,Show a,Apply a Param,Problem q a) =>
>              String -> q -> Refine a
> compute s q = do
>   eta snd <$> (public s Zip $ await (Compute,QTerm) q)

> tidy :: Ctxt -> Ctxt
> tidy (lz :<: Layer _ _ _ (Prob (Solved _) (Compute,_) _) _) = lz
> tidy (lz :<: Layer root' del' (ez' :*: es') prob' im'
>               :<: Layer root del ezs (Prob (Solved _) k q) im)
>   = lz :<: Layer root' del' (ez' :<:
>               Name root (Waiting del (curList ezs) (Prob Satisfied k q)) im
>               :*: es') prob' im'
> tidy lz = outLeft lz

> declare :: ObjKind -> Term -> Params -> Root -> Refine Term
> declare ok dom _ root@(nom@(Long (_ :<: (s,_))),_) = do
>   let val = case ok of
>               ObjDecl con -> TF (Con con (UN s) nom Zip)
>               _ -> TElim (Var (F nom)) Zip
>   enter $ Name root (Object $ UN s :=: (ok,val ::: dom)) ImNew
>   return val

> define :: (Term ::: Term) -> Params -> Root -> Refine Term
> define vt@(v ::: _) _ root@(nom@(Long (_ :<: (s,_))),_) = do
>   enter $ Name root (Object $ UN s :=: (ObjDefn,vt)) ImNew
>   return v

> lambda :: Visibility -> Term -> Params -> Root -> Refine Term
> lambda = declare . ObjAbst Lam

> forAll :: Visibility -> Term -> Params -> Root -> Refine Term
> forAll = declare . ObjAbst All

> exists :: Visibility -> Term -> Params -> Root -> Refine Term
> exists = declare . ObjAbst Ex

> witness :: Visibility -> (Term ::: Term) -> Params -> Root -> Refine Term
> witness vis vt@(val ::: _) _ root@(Long (_ :<: (s,_)),_) = do
>   enter $ Name root (Object $ UN s :=: (ObjWit vis,vt)) ImNew
>   return val

> hope :: Term -> Params -> Root -> Refine Term
> hope ty del root@(nom@(Long (_ :<: (s,_))),_) = do
>   sh <- hopeRefined (UN s) (del,ty)
>   case sh of
>     Left (del',ty') -> do
>       track ("HOPE: " ++ show nom ++ " : " ++ show del' ++ " |- "
>              ++ show ty') $ return ()
>       enter $ Name root (Hoping (UN s) del' ty') ImNew
>       return (TElim (Hope nom) Zip @@ del)
>     Right tm -> return tm

> stuck :: Refine x
> stuck = doo m0


******************************************************************************
Hoping
******************************************************************************

> lHope :: Params -> UName -> Params -> Term -> Refine Term
> lHope del (UN s) del' ty = do
>   roo <- child s
>   x <- hope ty (del <+> del') roo
>   return (x @@ del)

> hopeRefined :: UName -> (Params,Term) -> Refine (Either (Params,Term) Term)
> hopeRefined unom dt = hopeRefine unom dt <+> return (Left dt)

> hopeRefine :: UName -> (Params,Term) -> Refine (Either (Params,Term) Term)
> hopeRefine unom (del,TBind All (u,v) (Sem (Just (TF Zero)) ran)) =
>   return . Right $
>     TBind Lam (u,v) (Sem Nothing{-TF Zero-} (\x -> x @@ NoughtE (ran x)))
> hopeRefine unom (del,TBind All (u,v) (Sem (Just dom) ran)) = do
>   (pa,va) <- param (ObjAbst Lam v) u dom
>   hopeRefined unom (del :<: pa,ran va)
> hopeRefine unom (del,TBind Ex (u,v) (Sem (Just dom) ran)) = do
>   x <- lHope del u Zip dom
>   y <- lHope del unom Zip (ran x)
>   return . Right $ TF (Pair v x y)
> hopeRefine unom (del,TF One) = return $ Right (TF Only)
> -- hopeRefine unom (del,TF (JMEq (s ::: sy) (t ::: ty))) = do
> --   Must True <- equalIn star sy ty
> --   Must True <- equalIn sy s t
> --   return . Right $ TF (JMEq (s ::: sy))
> hopeRefine _ _ = stuck


******************************************************************************
Ambulando
******************************************************************************

> instance Updatable Prob where
>   upd bull (Prob s k q)
>     | (q',m) <- update bull q
>     = do tweak (m <+>) ; return (Prob (nudge m s q) k q')
>     where
>       nudge (Might True) _ q' | Just _ <- varCatch q' = Pending Refine
>       nudge (Might True) (Pending _) q' = Pending Refine
>       nudge _            (Solved a)  q' = Solved (bull <%> a)
>       nudge _             s          q' = s

> instance Updatable Entry where
>   upd bull (Name root ent im) = eta (Name root) <$> upd bull ent <$> eta im
>   upd bull (News bull') = eta (News (bull <+> bull'))
>   upd bull Swoon = eta Swoon
>   upd bull RefMark = eta RefMark

> propagator :: Bulletin -> List Entry -> Mod (List Entry,Bulletin)
> propagator bull (Tip _) = return (nil,bull)
> propagator bull (News bull' :>: es) = propagator (bull <+> bull') es
> propagator bull (e :>: es) = do
>   e' <- upd bull e
>   (es',bull') <- propagator bull es
>   return (e' :>: es',bull')

> propagate :: Bulletin -> List Entry -> (List Entry,Bulletin)
> propagate bull es = un . result m0 $ propagator bull es

> instance Updatable Entity where
>   upd bull (Object o) = {-# SCC "updEntityObject" #-}
>     eta Object <$> upd bull o
>   upd bull (Hoping u del t) = eta (Hoping u) <$> upd bull del <$> upd bull t
>   upd bull (Waiting del es p) = do
>     del' <- upd bull del
>     (es',bull') <- propa bull es
>     p' <- upd bull' p
>     return $ Waiting del' es' p'
>     where
>       propa bull (Tip _) = return (nil,bull)
>       propa bull (News bull' :>: es) = propa (bull <+> bull') es
>       propa bull (e :>: es) = do
>         e' <- upd bull e
>         (es',bull') <- propa bull es
>         return (e' :>: es',bull')

> ambulando :: Bulletin -> Ctxt -> Ctxt
> ambulando bull Zip = error "how the hell did that happen?"
> ambulando bull (lz :<: Layer root del (ez :*: e :>: es) prob im)
>   = case e of
>       News bull' -- | trace "COMPOSE SUBSTITUTION" True
>         -> (ambulando $! (bull <+> bull')) $!
>                       (lz :<: Layer root del (ez :*: es) prob im)
>       Swoon -> ambulando m0 $! track (show ("SWOON " ++ show bull))
>                                 (lz :<: Layer root del (ez :*: es) prob im)
>       RefMark -> error "ambulando hit a RefMark"
>       Name root' (Waiting del' es' prob') im'
>      --  | trace (show (fst root') ++ " " ++ show prob') True
>         ->
>         ambulando bull $!
>           (lz :<: Layer root del (ez :*: News bull :>: es) prob im
>               :<: Layer root' (bull <%> del') (Zip :*: es') prob' im')
>       Name root0@(nom,_) (Hoping _ del0 ty0) im'
>         | ((del1,ty1),Might True) <- update bull (del0,ty0)
>         -> ambulando bull $!( tryThis  -- UWOT?
>              (lz :<: Layer root del (ez :*: es) prob im) $ do
>                tm <- hope ty1 del1 root0
>                case tm of
>                  TElim (Hope nam) Zip | nom == nam -> return ()
>                  _ -> forwardEnter $
>                        News (story (LStory nom (report (del1 |- tm)))))
>       _ -> ambulando bull $! (lz :<:
>         Layer root del (ez :<: bull <%> e :*: es) prob im)
> ambulando bull (lz :<: Layer root del ezs@(ez :*: Tip _) prob im)
>   = odnalubma $! (lz :<: Layer root del ezs (bull <%> 
>                             track (show prob) prob) im)

> odnalubma :: Ctxt -> Ctxt
> odnalubma ctxt@(_ :<: Layer (nom,_) _ _ p@(Prob _ _ _) _)
>   | track ("odnalubma " ++ show nom ++ " " ++ show p) $ False = ctxt
> odnalubma done@(Zip :<: _) = track "odnalumba done" $ done
> odnalubma ctxt@(_ :<:
>   Layer (nom,_) _ (Zip :*: Tip _) (Prob (Pending Refine) _ q) _)
>   = ambulando m0 $!( tryThis ctxt $
>       do refMark
>          track ("od refines " ++ show nom) $ tryRefine q
>          kramFer)
> odnalubma ctxt@(lz :<: 
>                 Layer root del ezs@(wk :*: _) (Prob (Pending Refine) k q) im)
>   = ambulando m0 $! (tryThis ctxt $
>       do refMark
>          (es,stat,ProbFor q') <- export del wk q
>          del' <- getDel
>          tweak (zPop 1)
>          tweak (:<: Layer root del' ((Zip <>< es) :*: nil)
>                     (Prob stat k q') ImNew)
>          kramFer
>       <+>
>       do set (lz :<: Layer root del ezs (Prob (Pending Shock) k q) im))
> odnalubma ctxt@(lz :<: Layer root del work (Prob (Pending Shock) k q) im)
>   | Just ctxt' <- shock q ctxt
>   = ambulando m0 $! ctxt'
>   | otherwise
>   = odnalubma $!
>       (lz :<: Layer root del work (Prob (Pending MoreInfo) k q) im)
> odnalubma ctxt@(_ :<: Layer (nom,_) del _ (Prob (Solved a) _ _) _)
>   = ambulando (story (LStory nom (report $! (del |- a)))) $! (tidy ctxt)
> odnalubma lz = ambulando m0 $! (outLeft lz)


******************************************************************************
Redisplay
******************************************************************************

> class Displayable x where
>   display :: Int -> Ctxt -> x -> Boxings
>   display _ _ _ = box0 -- dummy to be overridden
>   cursorXY :: x -> (Int,Int)
>   cursorXY _ = (0,0)

> instance Displayable x => Displayable (Trigger x) where
>   display ew ctxt (Trigger x) = display ew ctxt x

> instance Displayable Boxings where
>   display _ _ = id

can I do this?

 instance (Functorial f,Displayable x,Displayable (f Boxings)) =>
   Displayable (f x) where
     display ew gam fx = display ew gam (up (display ew gam) fx)

> data ReDispTree = RDT [((String,Int),ReDispTree)]

> findOut :: Eq a => a -> [(a,b)] -> Maybe (b,[(a,b)])
> findOut a ((a',b) : abs) | a == a' = Just (b,abs)
> findOut a (ab : abs) | Just (b,abs') <- findOut a abs = Just (b,ab : abs)
> findOut a _ = Nothing

> checkReDisp :: LName -> State Id ReDispTree Bool
> checkReDisp (Long siz) = boof (siz <>> nil) where
>   boof (Tip _) = return True
>   boof (si :>: sis) =
>     do RDT sirdts <- get id
>        case findOut si sirdts of
>          Nothing -> return False
>          Just (rdt,sirdts') ->
>            do let Id (b,rdt') = un (boof sis) rdt
>               set (RDT ((si,rdt') : sirdts'))
>               return b

> makeReDisp :: LName -> State Id ReDispTree ()
> makeReDisp (Long siz) = boof (siz <>> nil) where
>   boof (Tip _) = return ()
>   boof (si :>: sis) =
>     do RDT sirdts <- get id
>        case findOut si sirdts of
>          Just (rdt,sirdts') ->
>            do let Id rdt' = effect rdt (boof sis)
>               set (RDT ((si,rdt') : sirdts'))
>          Nothing -> set (RDT ((si,bof sis) : sirdts))
>     where
>       bof (Tip _) = RDT []
>       bof (si :>: sis) = RDT [(si,bof sis)]

> updateImage :: LName -> Image -> Bool -> State Id ReDispTree Image
> updateImage nom ImNew _ = -- whole new thing
>   do makeReDisp nom
>      return ImNew
> updateImage nom (ImOld curb _) curb' | curb /= curb' = -- new cursor state
>   do makeReDisp nom
>      return ImNew
> updateImage nom oi _ = -- not directly updated
>   do b <- checkReDisp nom
>      if b then return ImNew else return oi

> type Globz = Zip ((String,Int),Rightmost Boxings)

> redisplay :: Int -> LName -> Ctxt -> State (State Id ReDispTree) Globz Ctxt
> redisplay ew cur (lz :<: Layer root del (ez :*: e :>: es) prob im)
>   = case e of
>       Name root' (Waiting del' es' prob') im' ->
>         redisplay ew cur (lz :<: Layer root del (ez :*: es) prob im
>                          :<: Layer root' del' (Zip :*: es') prob' im')
>       _ -> redisplay ew cur (lz :<: Layer root del (ez :<: e :*: es) prob im)
> redisplay ew cur ctxt@(lz@(_ :<: _) :<:
>        Layer root@(nom,_) del ezs@(_ :*: Tip _) prob@(Prob s _ q) im0)
>   = do let curb = nom == cur  -- are we at the cursor?
>        track (show nom ++ show s ++ show q) $ return ()
>        im1 <- doo $ updateImage nom im0 curb
>        (bx,rbx) <- case im1 of
>               ImNew -> let bx' =
>                              tagB nom (shade s del curb
>                                     (suppressesYellow q) (display ew ctxt q))
>                        in  return (bx',Rightmost bx')
>               ImOld _ bx -> return (bx,Missing)
>        case nom of -- global name?
>          Long (Zip :<: si) -> tweak (:<: (si,rbx))
>          _ -> return ()
>        redisplay ew cur . outLeft $
>          lz :<: Layer root del ezs prob (ImOld curb bx)
> redisplay _ _ ctxt = return ctxt

> redisplayAll :: Int -> Ctxt -> (Ctxt,Globz)
> redisplayAll ew ctxt
>   | cur <- whereAmI ctxt
>   , track ("Cursor " ++ show cur) True
>   , Id ((ctxt',g),_) <- un (un (redisplay ew cur (origin ctxt)) Zip) (RDT [])
>   = (focus cur ctxt',g)

> renewDisplayMarks :: Ctxt -> Ctxt
> renewDisplayMarks = up relay where
>   relay (Layer root del work prob _)
>     = Layer root del (up ree work) prob ImNew
>   ree (Name root ent _) = Name root (reent ent) ImNew
>   ree e = e
>   reent (Waiting del work prob) = Waiting del (up ree work) prob
>   reent ent = ent


******************************************************************************
Names are displayable
******************************************************************************

crappy search algorithm for now

> instance Displayable LName where
>   display ew gam nom = replacement box0 (hunt gam) where
>     hunt (lz :<: Layer root@(nam,_) del (ez :*: es) prob@(Prob s _ q) im)
>       | nam == nom
>       = case im of
>           ImOld _ bx -> Rightmost bx
>           ImNew -> Rightmost . tagB nom . shade s del False False
>                     $ display ew
>                      (lz :<: Layer root del ((ez <>< es) :*: nil) prob im)
>                      q
>     hunt ctxt@(lz :<: Layer _ _ (ez :<: Name _ (Waiting _ _ _) _ :*: _) _ _)
>       = hunt (inLeft ctxt)
>     hunt (lz :<: Layer root del (ez :<: e :*: es) prob im) =
>       hunt (lz :<: Layer root del (ez :*: e :>: es) prob im)
>     hunt (Zip :<: Layer _ _ (Zip :*: _) _ _) = Missing
>     hunt ctxt@(lz :<: Layer _ _ (Zip :*: es) _ _) = hunt (outRight ctxt)


******************************************************************************
UName stuff
******************************************************************************

> okName :: ObjKind -> UName -> Refine Must
> okName ok unom =
>   case ok of
>     ObjDecl _ -> get (lay <!>)
>     ObjDefn   -> get (lay <!>)
>     _         -> get (lay . zTop)
>   where
>     lay (Layer _ del (ez :*: es) _ _) =
>       par <!> del <+> ent <!> ez <+> ent <!> es
>     par (_ :=: o) = obj o
>     ent (Name _ (Object o) _) = obj o
>     ent _ = m0
>     obj (_ :=: (ObjRec,_)) = m0
>     obj (unam :=: _) = Must (unam /= unom)

> seekUName :: UName -> Refine Param
> seekUName unom = do
>   lz <- get id
>   searchUName unom False lz Zip Zip where {}

 seekUName unom = do
   Rightmost o <- get (lay <!>)
   return o
   where
     lay (Layer _ del (ez :*: _) _ _) = par <!> del <+> ent <!> ez
     par p@(_ :=: unam :=: _) = when (unom == unam) $ return p
     ent (Name (nom,_) (Object o@(unam :=: _)) _) =
       when (unom == unam) $ return (nom :=: o)
     ent _ = m0

> elabUName :: UName -> Refine Param
> elabUName unom = do
>   lz <- get id
>   searchUName unom True lz Zip Zip where {}

> searchUName :: UName -> Bool -> Ctxt -> Params -> Zip Entry -> Refine Param
> searchUName unom _ Zip Zip Zip = doo m0
> searchUName unom b (lz :<: Layer _ del (ez :*: _) _ _) Zip Zip =
>   searchUName unom b lz del ez
> searchUName unom _ lz (del :<: p@(_ :=: unam :=: _)) Zip | unom == unam =
>   return p
> searchUName unom b lz (del :<: _) Zip = searchUName unom b lz del Zip
> searchUName unom b lz del (ez :<: e) = case e of
>   Name (nom,_) (Object o@(unam :=: _)) _ | unom == unam ->
>     return (nom :=: o)
>   Name (Long (Zip :<: ("Gap",_)),_) _ _ ->
>     searchUName unom False lz del ez
>   Name _ (Waiting _ _ (Prob (Pending _) (Elab,QDecl) _)) _ | b -> doo m0
>   _ -> searchUName unom b lz del ez


******************************************************************************
Get the type of that var
******************************************************************************

> class Context x where
>   varType :: LName -> x -> Rightmost Term

> instance Context x => Context (Zip x) where
>   varType nom xz = varType nom <!> xz

> instance Context Layer where
>   varType nom (Layer (nam,_) del (ez :*: _) _ _) =
>     varType nom del <+> varType nom ez

> instance Context Param where
>   varType nom (nam :=: o) = when (nam == nom) (eta (obTy o))

> instance Context Entry where
>   varType nom (Name (nam,_) ent _) | nom == nam = case ent of
>       Object o -> eta (obTy o)
>       Waiting del _ (Prob _ _ q) -> eta $ up (up pify) del |- probType q
>       Hoping u del t -> eta $ up (up pify) del |- t
>   varType _ _ = m0


******************************************************************************
Get the UName of that var
******************************************************************************

> varUName :: LName -> Ctxt -> Rightmost UName
> varUName nom lz = lay <!> lz where
>   lay (Layer (nam,_) del (ez :*: _) _ _) = parm <!> del <+> entr <!> ez
>   parm (nam :=: unom :=: _) | nom == nam = eta unom
>   parm _ = m0
>   entr (Name (nam,_) ent _) | nom == nam = case ent of
>     Object (unom :=: _) -> eta unom
>     _ -> m0
>   entr _ = m0


******************************************************************************
Get the Obj of that var
******************************************************************************

> varObj :: LName -> Ctxt -> Rightmost Object
> varObj nom lz = lay <!> lz where
>   lay (Layer (nam,_) del (ez :*: _) _ _) = parm <!> del <+> entr <!> ez
>   parm (nam :=: o@(unom :=: _)) | nom == nam = eta o
>   parm _ = m0
>   entr (Name (nam,_) ent _) | nom == nam = case ent of
>     Object o -> eta o
>     _ -> m0
>   entr _ = m0


******************************************************************************
Discharge-related stuff
******************************************************************************

> raisable :: Entry -> Bool
> raisable (Name _ (Waiting _ _ (Prob s (_,QDecl) _)) _) = case s of
>   Pending _ -> False
>   Solved _ -> False
>   _ -> True
> raisable (Name _ (Waiting _ _ _) _) = True
> raisable (Name _ (Hoping _ _ _) _) = True
> raisable _ = False

> raising :: LName -> Params -> Prob -> Bulletin
> raising nom del (Prob (s :: QStatus a) _ _) = raiser nom (wait nom :: a) del

> raise :: Params -> Entry -> List Entry  -- presumes raisable
> raise Zip e = e :>: nil
> raise del (Name root@(nom,_) (Waiting theta work prob) im) =
>   Name root (Waiting (del' <+> theta) work prob) im :>:
>   News (raising nom del' prob) :>:
>   nil
>   where del' = parify <!> del
> raise del (Name root@(nom,_) (Hoping u theta want) im) =
>   track ("RAISE HOPE: " ++ show nom ++ " " ++ show del)
>   Name root (Hoping u (del' <+> theta) want) im :>:
>   News (raiser nom star del') :>:
>   nil
>   where del' = parify <!> del
> raise _ _ = nil

> parish :: Object -> Bool
> parish (_ :=: (ObjDecl _,_)) = False
> parish _ = True

> parify :: Param -> Params
> parify (_ :=: _ :=: (ObjDecl _,_)) = Zip
> parify p@(_ :=: _ :=: (ObjDefn,_)) = Zip :<: p
> parify (_ :=: _ :=: (ObjWit _,_)) = Zip
> parify (nom :=: unom :=: (_,_ ::: ty)) =
>   Zip :<: (nom :=: unom :=: (ObjPar,TElim (Var (F nom)) Zip ::: ty))

> parametrize :: Params -> List Entry -> (List Entry,Bulletin)
> parametrize Zip es = (es,m0)
> parametrize del es = propagate m0 (raise del <!> es) where {}

> tidyWorkSpace :: Params -> (Zip Entry,Params) -> Bulletin -> List Entry ->
>                  ((Zip Entry,Params),(List Entry,Bulletin))
> tidyWorkSpace del (ez,del') bull (Name (nom,_) (Object o) _ :>: es)
>   = tidyWorkSpace del (ez,del' :<: (nom :=: bull <%> o)) bull es
> tidyWorkSpace del ezd bull (News bull' :>: es)
>   = tidyWorkSpace del ezd (bull <+> bull') es
> tidyWorkSpace del (ez,del') bull (e :>: es)
>   | raisable e
>   , (e',bull') <- propagate bull (raise (del <+> del') e)
>   = tidyWorkSpace del (ez <>< e',del') bull' es
> tidyWorkSpace _ ezd bull es = (ezd,propagate bull es)


******************************************************************************
Local info
******************************************************************************

> killLocalInfo :: Ctxt -> Ctxt
> killLocalInfo (lz :<: Layer root' del' (ez' :*: es') prob' im'
>                   :<: l@(Layer (Long siz,_) _ _ _ _)) =
>   lz :<: Layer root' del' (clean siz <!> ez' :*: es') prob' im' :<: l
>   where
>     clean siz (Name (Long siz',_) _ _) | info siz' = Zip where
>       info Zip = False
>       info (siz' :<: ("[Info]",_)) = siz == siz'
>       info (siz' :<: _) = info siz'
>     clean siz e = zOne e
> killLocalInfo ctxt = ctxt


> localContext :: Refine Params
> localContext = do
>   lz :<: Layer _ del (ez :*: _) _ _ <- get id
>   return $ glom lz del ez
>   where
>     glom Zip del _ = del  --- 'swhat makes it local
>     glom (lz' :<: Layer _ del' (ez' :*: _) _ _ ) del Zip =
>       glom lz' del' ez' <+> del
>     glom lz del (ez :<: Name (nom,_) (Object o) _) =
>       glom lz del ez :<: (nom :=: o)
>     glom lz del (ez :<: e) = glom lz del ez


******************************************************************************
Epigram State
******************************************************************************

> data Epigram = Epigram {
>   epiCtxt :: Ctxt,
>   epiDisplay :: Zip ((String,Int),BoxS),
>   epiUndo :: Zip Ctxt,
>   epiEditorWidth :: Int,
>   epiNeedsIgor :: Bool,
>   epiEventQueue :: [Event],
>   epiLocalInfo :: (Maybe LName,Bool),
>   epiLocalDisplay :: BoxS
>   }

> type Interactive = State IO Epigram

> epigramPostEvents :: [Event] -> Interactive ()
> epigramPostEvents es' = do
>   es <- get epiEventQueue
>   tweak $ \ x -> x {epiEventQueue = es ++ es'}

> epigramUndoMark :: Interactive ()
> epigramUndoMark =
>   do epi <- get id
>      set $ epi {epiUndo = epiUndo epi :<: epiCtxt epi}

> epigramAskIgor :: Interactive ()
> epigramAskIgor = do
>   tweak $ \ x -> x {epiNeedsIgor = True}

> epigramGetLocalInfo :: Interactive ()
> epigramGetLocalInfo = do
>   ctxt@(_ :<: Layer _ _ _ (Prob _ _ q) _) <- get (killLocalInfo . epiCtxt)
>   case un (localInfo q) ctxt of
>     Just (nom,ctxt') -> do
>       tweak $ \ x -> x {epiCtxt = ctxt', epiLocalInfo = (Just nom,True)}
>     _ -> tweak $ \ x -> x {epiLocalInfo = (Nothing,True)}

> epigramUndo :: Interactive ()
> epigramUndo =
>   do (undo :<: ctxt) <- get epiUndo
>      ew <- get epiEditorWidth
>      eq <- get epiEventQueue
>      doo . emacsDOIT . epigram $ ("delete-buffer-contents" ~$ [])
>      set $ Epigram {
>        epiCtxt = renewDisplayMarks ctxt,
>        epiDisplay = Zip,
>        epiUndo = undo,
>        epiEditorWidth = ew,
>        epiNeedsIgor = False,
>        epiEventQueue = eq,
>        epiLocalInfo = (Nothing,False),
>        epiLocalDisplay = box0
>        }
>      epigramGetLocalInfo

> epigramRefine :: Refine () -> Interactive ()
> epigramRefine rfn =
>   do epi <- get id
>      let ctxt = epiCtxt epi
>      set $ epi {epiCtxt = tryThis ctxt rfn}

> epigramEvent :: Event -> Interactive ()
> epigramEvent e =
>   do ctxt <- get epiCtxt
>      case ctxt of
>        (_ :<: Layer (nom,_) _ _ (Prob s _ q) _) ->
>          track ("Event at " ++ show nom ++ " " ++ show q) event q s e
>        _ -> return ()

> epigramPoint :: (Int,Int) -> Interactive ()
> epigramPoint (x,y) =
>   doo . emacsDOIT . epigram $ ("goto-xy" ~$ [EI x,EI y])

> rebuildDisplay :: Globz -> Interactive ()
> rebuildDisplay globz =
>   do disp <- get epiDisplay
>      pab <- get $ pickABox . epiEditorWidth
>      (disp',_) <- blat pab disp globz
>      tweak $ \ x -> x {epiDisplay = disp'}
>   where
>     blat pab Zip Zip = return (Zip,(False,0))
>     blat pab (sibz :<: (_,b)) Zip =
>       do (_,bline) <- blat pab sibz Zip
>          l <- cursory bline
>          doo $ emacsDelete b
>          return (Zip,(True,l))
>     blat pab Zip (gz :<: (si,Missing)) = error "missing new display entry"
>     blat pab Zip (gz :<: (si,Rightmost g)) =
>       do (sibz,bline) <- blat pab Zip gz
>          let b = pab g
>          l <- cursory bline 
>          doo $ emacsInsert b
>          return (sibz :<: (si,b),(False,l + tallness b))
>     blat pab (sibz :<: (osi,b)) (gz :<: (nsi,Missing)) | osi == nsi =
>       do (sibz',(_,l)) <- blat pab sibz gz
>          return (sibz' :<: (osi,b),(False,l + tallness b))
>     blat pab (sibz :<: (osi,b)) (gz :<: (nsi,Rightmost g)) | osi == nsi =
>       do (sibz',bline) <- blat pab sibz gz
>          l <- cursory bline
>          let b' = pab g
>          doo $ emacsReplace b b'
>          return (sibz' :<: (osi,b'),(True,l + tallness b'))
>     blat pab sibz (gz :<: (si,Rightmost g)) =
>       do (sibz',bline) <- blat pab sibz gz
>          let b' = pab g
>          l <- cursory bline
>          doo $ emacsInsert b'
>          return (sibz' :<: (si,b'),(True,l + tallness b'))
>     blat pab (sibz :<: (_,b)) gz@(_ :<: (nsi,Missing)) =
>       do (sibz',bline) <- blat pab sibz gz
>          l <- cursory bline
>          doo $ emacsDelete b
>          return (sibz',(True,l))
>     cursory (True,l) = return l
>     cursory (False,l) = do
>       epigramPoint (0,l)
>       return l

> epigramCursor :: Interactive ()
> epigramCursor =
>   do _ :<: Layer (nom,_) _ _ (Prob _ _ q) _ <- get epiCtxt
>      let xy = cursorXY q
>      disp <- get epiDisplay
>      case tl nom disp of
>        Just oxy -> epigramPoint (oxy <+> xy)
>        Nothing -> return ()
>   where
>     tl nom Zip = Nothing
>     tl nom (sibz :<: (_,b))
>       | Just xy <- tagPos nom b
>       , (_,(h,_)) <- bSize b
>       = Just ((0 :: Int,h + hgt sibz) <+> xy)
>     tl nom (sibz :<: _) = tl nom sibz
>     hgt Zip = 0
>     hgt (sibz :<: (_,b)) | (_,(h,d)) <- bSize b = hgt sibz + h + d

> epigramDisplay :: Interactive ()
> epigramDisplay =
>   do ew <- get epiEditorWidth
>      (ctxt',globz) <- get (redisplayAll ew . epiCtxt)
>      rebuildDisplay globz
>      tweak $ \ x -> x {epiCtxt = ctxt'}

> button :: LName
> button = Long Zip /// "Button"

> epigramLocalDisplay :: Interactive ()
> epigramLocalDisplay = do
>   (mnom,b) <- get epiLocalInfo
>   if b
>     then do
>       ew <- get epiEditorWidth
>       ctxt <- get epiCtxt
>       let li = case mnom of
>                  Just nom -> display ew ctxt nom
>                  _ -> box0
>       let ld = pickABox ew $
>                  display ew ctxt (button /// "Undo") |?| _B |?|
>                  display ew ctxt (button /// "Reset") |?| _B |?|
>                  display ew ctxt (button /// "Quit")
>                  -#- lineB
>                  -#- li
>       tweak $ \x -> x {epiLocalInfo = (mnom,False), epiLocalDisplay = ld}
>       let lb = un $ boxText m0 ld
>       doo $ do
>         emacsDOIT . horace $ ("delete-buffer-contents" ~$ [])
>         emacsDOIT . horace $ emacs (0 :: Int,lb)
>     else return ()


> igor :: Interactive ()
> igor =
>   do ctxt <- get epiCtxt
>      need <- get epiNeedsIgor
>      if need
>        then do
>          let ctxt' =  focus (whereAmI ctxt) $ ambulando m0 (origin ctxt)
>          case ctxt' of
>            (_ :<: _) -> track "Igor!" $ return ()
>            _ -> return ()
>          tweak $ \ x -> x {epiCtxt = ctxt', epiNeedsIgor = False}
>          epigramGetLocalInfo
>        else return ()

> instance Show Epigram where
>   show _ = "ok"


