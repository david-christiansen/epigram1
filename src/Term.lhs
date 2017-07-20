******************************************************************************
**********                                                          **********
**********     Epigram terms                                        **********
**********                                                          **********
******************************************************************************

> module Term where

> import Utils
> import Category
> import Monadics
> import Logic
> import Zip
> import Name
> import ObjKind


******************************************************************************
Scope
******************************************************************************

> data Sem d r x = Sem (Maybe (d x)) (d x -> r x)
> data Sym d r x = Sym Int (Maybe (d x)) (r x)

These are candidates for the scope-forming parameter sc, below.

Crucially...

> instance (Functorial d,Functorial r) => Functorial (Sym d r) where
>   g <^> (Sym i d r) = fun (Sym i) (g <^^> d) (g <^> r)

> instance (Functor d,Functor r) => Functor (Sym d r) where
>   fmap g (Sym i d r) = Sym i (fmap (fmap g) d) (fmap g r)



******************************************************************************
Term
******************************************************************************

> data Tm sc x
>   = TF (TmF (Tm sc x))  -- the purely functorial part of the signature
>   | TBind Bind Desc (sc (Tm sc) (Tm sc) x)
>   | TElim (Hd sc x) (Zip (Elim (Tm sc x)))

> data TmF t -- t is the type of subterms
>   = Star | One | Only | Zero | Bot  -- Bot is used to propagate failure
>   | U_ Implicit
>   | JMEq (t ::: t) (t ::: t)
>   | JMRefl (t ::: t)
>   | Pair Visibility t t
>   | Con Con UName LName (Zip t)
>   | Lbl LabKind (Label t) t
>   deriving Show

> data Hd sc x
>   = Var (McKP x)
>   | Hope x        -- metavariables to be inferred from constraints
>   | Wait x        -- unsolved checking problems
>   | forall f . Haskell f => Blocked f (List (Tm sc x))

> data Elim t
>   = A t | NoughtE t | P1 | P2 | Call (Label t) | Ind Gadget (Zip t)
>   | JM (JMElim t)
>   deriving Show

> data JMElim t
>   = JMCoe | JMCon (Maybe t) | JMSym | JMResp (t ::: t)
>   deriving Show

> data McKP x
>   = F x | B Int UName
>   deriving Show

> instance Eq x => Eq (McKP x) where
>   F x == F y = x == y
>   B i _ == B j _ = i == j
>   _ == _ = False

> infix 3 :::
> data t ::: y = t ::: y deriving Show

> data Implicit = Shown | Hidden deriving (Show, Eq)

> data LabKind = LabTy | Return deriving Show

> data Label t = Label (UName ::: t) (Zip t) (Zip (t ::: t)) deriving Show

> data Gadget
>   = Gadget
>     { gKind :: IndElim,
>       gType :: Zip Term -> Term -> Term,
>       gElim :: Zip Term -> Term -> Maybe Term
>     }

> instance Show Gadget where
>   show = show . gKind

> class Show f => Haskell f where
>   runH :: f -> List Term -> Maybe Term
>   typeH :: f -> Term


------------------------------------------------------------------------------

> type Term = Tm Sem LName
> type Tyrm = Tm Sym LName

> star :: Term
> star = TF Star

> pair :: Term -> Term -> Term
> pair x y = TF (Pair NormV x y)


------------------------------------------------------------------------------

> instance Functorial TmF where
>   g <^> Star       = fun Star
>   g <^> One        = fun One
>   g <^> Only       = fun Only
>   g <^> Zero       = fun Zero
>   g <^> Bot        = fun Bot
>   g <^> U_ i       = fun (U_ i)
>   g <^> JMEq (t1 ::: y1) (t2 ::: y2) =
>     fun JMEq (fun (:::) (g t1) (g y1)) (fun (:::) (g t2) (g y2))
>   g <^> JMRefl (t1 ::: y1) =
>     fun JMRefl (fun (:::) (g t1) (g y1))
>   g <^> Pair v x y = fun (Pair v) (g x) (g y)
>   g <^> (Con c unom nom tz)
>     = fun (Con c unom nom) (g <^> tz)
>   g <^> (Lbl lk l t) = fun (Lbl lk) (g <^> l) (g t)

> instance Functorial Label where
>   g <^> (Label (unom ::: t) tz ttz)
>     = fun Label (fun (unom :::) (g t)) (g <^> tz) (gg <^> ttz) where
>       gg (x ::: y) = fun (:::) (g x) (g y)

> instance Functorial Elim where
>   g <^> (A t)    = fun A (g t)
>   g <^> NoughtE y = fun NoughtE (g y)
>   g <^> P1       = fun P1
>   g <^> P2       = fun P2
>   g <^> Call l   = fun Call (g <^> l)
>   g <^> Ind x tz = fun (Ind x) (g <^> tz)
>   g <^> JM jt    = fun JM (g <^> jt)

> instance Functorial JMElim where
>   g <^> JMCoe    = fun JMCoe
>   g <^> JMCon t  = fun JMCon (g <^> t)
>   g <^> JMSym    = fun JMSym
>   g <^> JMResp (t ::: ty) = fun JMResp (fun (:::) (g t) (g ty))

> instance Functorial McKP where
>   g <^> F x = fun F (g x)
>   g <^> B i u = fun (B i u)

> instance Functorial (Hd Sym) where
>   g <^> Var x        = fun Var (g <^> x)
>   g <^> Hope x       = fun Hope (g x)
>   g <^> Wait x       = fun Wait (g x)
>   g <^> Blocked f az = fun (Blocked f) ((g <^>) <^> az)

> instance Functorial (Tm Sym) where
>   g <^> TF ft = fun TF ((g <^>) <^> ft)
>   g <^> TBind b d sc = fun (TBind b d) (g <^> sc)
>   g <^> TElim h ez
>     = fun TElim (g <^> h) (((g <^>) <^>) <^> ez)

----------------------------------------------------------------------------

> instance Functor TmF where
>   fmap g Star       = Star
>   fmap g One        = One
>   fmap g Only       = Only
>   fmap g Zero       = Zero
>   fmap g Bot        = Bot
>   fmap g (U_ i)     = U_ i
>   fmap g (JMEq (t1 ::: y1) (t2 ::: y2)) =
>     JMEq ((:::) (g t1) (g y1)) ((:::) (g t2) (g y2))
>   fmap g (JMRefl (t1 ::: y1)) =
>     JMRefl ((:::) (g t1) (g y1))
>   fmap g (Pair v x y) = (Pair v) (g x) (g y)
>   fmap g (Con c unom nom tz)
>     = (Con c unom nom) (fmap g tz)
>   fmap g (Lbl lk l t) = (Lbl lk) (fmap g l) (g t)

> instance Functor Label where
>   fmap g (Label (unom ::: t) tz ttz)
>     = Label ((unom :::) (g t)) (fmap g tz) (fmap gg ttz) where
>       gg (x ::: y) = (:::) (g x) (g y)

> instance Functor Elim where
>   fmap g (A t)    = A (g t)
>   fmap g (NoughtE y) = NoughtE (g y)
>   fmap g P1       = P1
>   fmap g P2       = P2
>   fmap g (Call l)   = Call (fmap g l)
>   fmap g (Ind x tz) = (Ind x) (fmap g tz)
>   fmap g (JM jt)    = JM (fmap g jt)

> instance Functor JMElim where
>   fmap g JMCoe    = JMCoe
>   fmap g (JMCon t)  = JMCon (fmap g t)
>   fmap g JMSym    = JMSym
>   fmap g (JMResp (t ::: ty)) = JMResp ((:::) (g t) (g ty))

> instance Functor McKP where
>   fmap g (F x) = F (g x)
>   fmap g (B i u) = (B i u)

> instance Functor (Hd Sym) where
>   fmap g (Var x)        = Var (fmap g x)
>   fmap g (Hope x)       = Hope (g x)
>   fmap g (Wait x)       = Wait (g x)
>   fmap g (Blocked f az) = (Blocked f) (fmap (fmap g) az)

> instance Functor (Tm Sym) where
>   fmap g (TF ft) = TF (fmap (fmap g) ft)
>   fmap g (TBind b d sc) = (TBind b d) (fmap g sc)
>   fmap g (TElim h ez)
>     = TElim (fmap g h) (fmap (fmap (fmap g)) ez)



******************************************************************************
Epigram's computational behaviour
******************************************************************************

> infixl 9 @@

> class Apply x s where
>   (@@) :: x -> s -> x

> instance Apply Term (Elim Term) where
>   TF Bot @@ _ = TF Bot -- failure propagation should not cause error
>   t @@ Ind gad iz | Just t' <- gElim gad iz t = t'
>   TElim (Blocked f as) Zip @@ A a =
>     let asa = as <+> (a :>: nil)
>     in  prefer (runH f asa) (TElim (Blocked f asa) Zip)
>   TElim h ez @@ e = TElim h (ez :<: e)
>   TBind Lam (unom,UnifV) s @@ A (TF (U_ _)) = TBind Lam (unom,NormV) s
>   TF (Pair UnifV x y) @@ A (TF (U_ _)) = TF (Pair NormV x y)
>   TF (Con c unom nt az) @@ A a = TF (Con c unom nt (az :<: a))
>   f @@ A (TF (U_ _)) = error $ "explicit object _ : " ++ show f
>   TBind Lam (_,NormV) (Sem _ f) @@ A a = f a
>   TF (Pair NormV x _) @@ P1 = x
>   TF (Pair NormV _ y) @@ P2 = y
>   TF (Lbl Return _ t) @@ Call _ = t
>   q @@ JM j = q @@ j
>   t @@ e = error . concat $ ["Bad Elim\n",show t,"\n",show e,"\n"]

> instance Apply Term (JMElim Term) where
>   TF (JMRefl (s ::: _)) @@ JMResp (f ::: TBind All (_,NormV) (Sem _ ran)) =
>     TF (JMRefl (f @@ s ::: ran s))
>   TF (JMRefl _) @@ JMCoe = TBind Lam dull (Sem Nothing id)
>   TF (JMRefl (TF (Con _ _ _ az) ::: _)) @@ JMCon (Just cty) =
>     injective cty az
>   t@(TF (JMRefl _)) @@ JMSym = t
>   TElim h ez @@ j = TElim h (ez :<: JM j)
>   t @@ e = error . concat $ ["Bad Elim\n",show t,"\n",show e,"\n"]

> peanom :: LName
> peanom = Long (Zip :<: ("Peano",0))

> injective :: Term -> Zip Term -> Term
> injective cty az =
>   let (pP,vP) = decl (peanom /// "P") (UN "P") Lam NormV star
>       methT :: Int -> Params -> Zip (Elim Term) -> Term -> List Term ->
>                  (Zip (Elim Term),Term)
>       methT _ del reflz _ (Tip _) = (reflz,discharge del vP)
>       methT i del reflz (TBind All (u,UnifV) s) (TF (U_ _) :>: as) =
>         methT i del reflz (TBind All (u,NormV) s) as
>       methT i del reflz
>        (TBind All (_,NormV) (Sem (Just dom) ran)) (a :>: as) =
>         let ad = a ::: dom
>             (pQ,_) = decl (peanom /// ("q",i)) (UN ("q" ++ show i)) All NormV
>                        $ TF (JMEq ad ad)
>         in  methT (i + 1) (del :<: pQ) (reflz :<: A (TF (JMRefl ad)))
>               (ran a) as
>       (em,tm) = methT 0 Zip Zip cty (az <>> nil)
>       (pm,vm) = decl (peanom /// "m") (UN "m") Lam NormV tm
>   in  discharge (Zip :<: pP :<: pm) (vm @@ em)

> instance Apply x (Elim Term) => Apply x Term where
>   f @@ s = f @@ A s

> instance Apply x s => Apply x (Zip s) where
>   x @@ sz = zPost (@@) x sz

> u_ :: Elim Term
> u_ = A (TF (U_ Hidden))

> pi1 :: Elim Term
> pi1 = P1

> pi2 :: Elim Term
> pi2 = P2

> instance Apply (Term ::: Term) (Elim Term) where
>   (x ::: t) @@ e = (x @@ e ::: bof t e) where
>     bof _ (NoughtE t) = t
>     bof (TBind b (unom,UnifV) s) (A (TF (U_ _))) = TBind b (unom,NormV) s
>     bof (TBind All (_,NormV) (Sem _ ran)) (A a) = ran a
>     bof (TBind Ex (_,NormV) (Sem (Just dom) _)) P1 = dom
>     bof (TBind Ex (_,NormV) (Sem _ ran)) P2 = ran (x @@ pi1)
>     bof _ (Ind gad iz) = gType gad iz x
>     bof (TF (Lbl LabTy _ t)) (Call _) = t
>     bof (TF (JMEq (x ::: _) (y ::: _)))
>         (JM (JMResp (f ::: TBind All (_,NormV) (Sem _ ran)))) =
>       TF (JMEq (f @@ x ::: ran x) (f @@ y ::: ran y))
>     bof (TF (JMEq (s ::: _) (t ::: _))) (JM JMCoe) =
>           TBind All dull (Sem (Just s) (const t))
>     bof _ (JM (JMCon Nothing)) = TBind All dull (Sem (Just star) id)
>     bof (TF (JMEq (TF (Con _ _ _ az1) ::: _) (TF (Con _ _ _ az2) ::: _)))
>         (JM (JMCon (Just cty))) = injectivity cty (eta (,) <$> az1 <$> az2)
>     bof (TF (JMEq sS tT)) (JM JMSym) = TF (JMEq tT sS)

> instance Apply (Term ::: Term) (JMElim Term) where
>   tty @@ j = tty @@ JM j

> injectivity :: Term -> Zip (Term,Term) -> Term
> injectivity cty aaz =
>   let (pP,vP) = decl (peanom /// "P") (UN "P") All NormV star
>       methT :: Int -> Params -> (Term,Term) -> List (Term,Term) -> Term
>       methT _ del _ (Tip _) = discharge del vP
>       methT i del (TBind All (u1,UnifV) s1,TBind All (u2,UnifV) s2)
>                    ((TF (U_ _),TF (U_ _)) :>: aas) =
>         methT i del (TBind All (u1,NormV) s1,TBind All (u2,NormV) s2) aas
>       methT i del (TBind All (_,NormV) (Sem (Just dom1) ran1),
>                    TBind All (_,NormV) (Sem (Just dom2) ran2))
>                   ((a1,a2) :>: aas) =
>         let (pQ,_) = decl (peanom /// ("q",i)) (UN ("q" ++ show i)) All NormV
>                        $ TF (JMEq (a1::: dom1) (a2 ::: dom2))
>         in  methT (i + 1) (del :<: pQ) (ran1 a1,ran2 a2) aas
>       mty = methT 0 Zip (cty,cty) (aaz <>> nil)
>       (pm,vm) = decl (peanom /// "m") (UN "m") All NormV mty
>   in  discharge (Zip :<: pP :<: pm) vP


******************************************************************************
Unapplication
******************************************************************************

> unapply :: Term -> Maybe (Term,Term)
> unapply (TF (Con c u n (az :<: a))) = return (TF (Con c u n az),a)
> unapply (TElim h (ez :<: A a))      = return (TElim h ez,a)
> unapply _ = m0

> unapplies :: Term -> (Term,List Term)
> unapplies (TF (Con c unom nom az)) = (TF (Con c unom nom Zip),az <>> nil)
> unapplies (TElim h ez) = rev ez nil where
>   rev (ez :<: A t) ts = rev ez (t :>: ts)
>   rev ez ts = (TElim h ez,ts)
> unapplies t = (t,nil)


******************************************************************************
Can you tell what it is yet?
******************************************************************************

> unclear :: Term -> Might
> unclear (TElim (Hope _) _) = Might True
> unclear (TElim (Wait _) _) = Might True
> unclear (TElim (Blocked f as) _) = unclear <!> as
> unclear _ = m0

> clearlyNotImplicit :: Term -> Bool
> clearlyNotImplicit (TBind Lam _ _) = False
> clearlyNotImplicit (TBind _ (_,UnifV) _) = False
> clearlyNotImplicit (TElim (Wait _) _) = False
> clearlyNotImplicit (TElim (Blocked f as) _) = (unclear <!> as) == Might True
> clearlyNotImplicit _ = True


******************************************************************************
Quotation
******************************************************************************

> class Quote e y | e -> y, y -> e where
>   quote :: Int -> List (LName,UName) -> e -> y
>                             -- the int is the index we've reached

> instance (Var (d LName),Quote (d LName) (d' LName),
>                         Quote (r LName) (r' LName))
>   => Quote (UName, Sem d r LName) (UName, Sym d' r' LName) where
>   quote i ns (u, Sem d f)
>     = (u, Sym i (fmap (quote i ns) d) (quote (i + 1) ns (f (var i u))))

> instance (Quote e1 y1,Quote e2 y2) => Quote (e1 ::: e2) (y1 ::: y2) where
>   quote i ns (e1 ::: e2) = quote i ns e1 ::: quote i ns e2

> instance Quote Term Tyrm where
>   quote i ns (TF x)         = TF (fmap (quote i ns) x)
>   quote i ns (TBind b d@(u, _) sc) = TBind b d (snd (quote i ns (u, sc)))
>   quote i ns (TElim h ez)   =
>     TElim (quote i ns h) ((fmap . fmap) (quote i ns) ez)

> instance Quote (Hd Sem LName) (Hd Sym LName) where
>   quote i ns (Var (F nom))
>     | Just (j, u) <- index ns nom = Var (B j u)
>     | otherwise                   = Var (F nom)
>   quote i ns (Var (B j u))        = Var (B j u)
>   quote i ns (Hope nom)
>     | Just (j, u) <- index ns nom = Var (B j u)
>     | otherwise                   = Hope nom
>   quote i ns (Wait nom)
>     | Just (j, u) <- index ns nom = Var (B j u)
>     | otherwise                   = Wait nom
>   quote i ns (Blocked f az)       = Blocked f (fmap (quote i ns) az)


******************************************************************************
Eval
******************************************************************************

> type EnvVal = Term

> type Env = (Int, Zip (UName, EnvVal), Alpha)

> class Var t where
>   var :: Int -> UName -> t
>   push :: t -> EnvVal
>   grab :: EnvVal -> t

> instance Var Term where
>   var j u = TElim (Var (B j u)) Zip
>   push = id
>   grab = id

> class Envy env where
>   epush :: UName -> EnvVal -> env -> env
>   eseek  :: Int -> env -> EnvVal
>   ealpha :: env -> UName -> UName
>   ename  :: env -> EnvVal -> Maybe UName
>   eempty :: env

> instance Envy Env where
>   epush pat t env@(n, gam, alph) =
>     (n + 1, gam :<: (targ, t), alph `coAlpha` mkAlpha pat targ) where
>       targ = prefer (ename env t) pat
>   eseek i (n, gam, _) =
>     track ("S" ++ show i ++ "/" ++ show n ++ "=" ++ show (zlen gam))
>     (snd (zTop (zPop (n - 1 - i) gam)))
>   ealpha (_, _, alph) = alpha alph
>   ename (n, gam, alph) (TElim (Var (F (Long siz))) _) = unpack siz where
>     unpack (siz :<: ("",_)) = Nothing
>     unpack (siz :<: (s,0)) = Just (UN s)
>     unpack (siz :<: (s,i)) = Just (UN (s ++ show i))
>     unpack _ = Nothing
>   ename (n, gam, alph) (TElim (Var (B i u)) _) = Just u
>   ename _ _ = Nothing
>   eempty = (0, Zip, idAlpha)


> class Eval y e | y -> e where
>   eval :: Envy g => g -> y -> e

> instance (Var (d LName),Eval (d' x) (d LName),
>                         Eval (r' x) (r LName))
>   => Eval (UName, Sym d' r' x) (UName, Sem d r LName) where
>   eval g (u, Sym _ d r)
>     = (u', Sem (fmap (eval g) d) (\ x -> eval (epush u' (push x) g) r))
>     where u' = ealpha g u

> class EvVar x where
>   vTerm :: (LName -> Hd Sem LName) -> x -> Term

> instance EvVar LName where
>   vTerm h nom = TElim (h nom) Zip

> instance EvVar x => Eval (Tm Sym x) Term where
>   eval g = ev where
>     ev (TF x)         = TF (fmap ev x)
>     ev (TBind b (u, v) sc) = TBind b (u', v) sc' where
>       (u', sc') = eval g (u, sc)
>     ev (TElim h ez)   = eval g h @@ (fmap . fmap) ev ez

> instance EvVar x => Eval (Hd Sym x) Term where
>   eval g = ev where
>     ev (Var (F x)) = vTerm (Var . F) x
>     ev (Var (B i _)) = grab (eseek i g)
>     ev (Blocked f pz)
>       | Just t <- runH f pz' = t
>       | otherwise            = TElim (Blocked f pz') Zip
>       where pz' = fmap (eval g) pz
>     ev (Hope x) = vTerm Hope x
>     ev (Wait x) = vTerm Wait x



******************************************************************************
Objects
******************************************************************************

> type Object = UName :=: (ObjKind,Term ::: Term)
> type Param = LName :=: Object
> type Params = Zip Param

> instance Show Object where
>   show (unom :=: (ok,tm ::: ty)) = case ok of
>     ObjWit vis -> def
>     ObjDefn -> def
>     _ -> dec
>     where
>       def = concat [show ok," ",show unom," => ",show (tm ::: ty)]
>       dec = concat [show ok," ",show unom," : ",show ty]


> nmTm :: LName -> Term
> nmTm nom = TElim (Var (F nom)) Zip

> obVal :: Object -> Term
> obVal (_ :=: (_,tm ::: _)) = tm

> parVal :: (LName :=: Object) -> Term
> parVal (_ :=: ob) = obVal ob

> obTy :: Object -> Term
> obTy (_ :=: (_,_ ::: ty)) = ty

> parTy :: (LName :=: Object) -> Term
> parTy (_ :=: ob) = obTy ob

> parFunc :: Params -> Term -> Zip Term -> Term
> parFunc del t az =
>   let (ns,num) = (\ (nom :=: u :=: _) -> ((nom, u) :>: nil,1)) <!> del
>       env = (num, fun dname del az, idAlpha)
>       dname (_ :=: u :=: _) a = (u, a)
>   in  eval env (quote num ns t)

> parArg :: Param -> Zip Term
> parArg (_ :=: _ :=: (ObjPar,tm ::: _)) = Zip :<: tm
> parArg (_ :=: _ :=: (ObjAbst b NormV,tm ::: _)) = Zip :<: tm
> parArg (_ :=: _ :=: (ObjAbst b UnifV,tm ::: _)) =
>   Zip :<: TF (U_ Hidden) :<: tm
> parArg _ = Zip

> parElim :: Param -> Zip (Elim Term)
> parElim (_ :=: _ :=: (ObjWit NormV,_)) = Zip :<: P2
> parElim (_ :=: _ :=: (ObjWit UnifV,_)) = Zip :<: u_ :<: P2
> parElim (_ :=: _ :=: (ObjAbst Ex NormV,tm ::: _)) = Zip :<: P2
> parElim (_ :=: _ :=: (ObjAbst Ex UnifV,tm ::: _)) = Zip :<: u_ :<: P2
> parElim p = fmap A (parArg p)

> instance Apply Term Param where
>   f @@ par = f @@ parElim par

Is ObjWit handled correctly?

> bify :: Bind -> Object -> Object
> bify b (unom :=: (ObjAbst _ v,tmty)) = unom :=: (ObjAbst b v,tmty)
> bify b (unom :=: (ObjPar,tmty)) = unom :=: (ObjAbst b NormV,tmty)
> bify _ x = x

> uify :: Object -> Object
> uify (unom :=: (ObjAbst b _,tmty)) = (unom :=: (ObjAbst b UnifV,tmty))
> uify x = x

> nify :: Object -> Object
> nify (unom :=: (ObjAbst b _,tmty)) = (unom :=: (ObjAbst b NormV,tmty))
> nify x = x

> pify :: Object -> Object
> pify = bify All

> pAll :: Params -> Params
> pAll = up (up (bify All))

> pLam :: Params -> Params
> pLam = up (up (bify Lam))

> pHide :: Params -> Params
> pHide = up (up uify)

> pShow :: Params -> Params
> pShow = up (up nify)

> type Cell = Term

> cell :: (Term ::: Term) -> Cell
> cell (tm ::: ty) = pair ty tm

> llec :: Cell -> (Term ::: Term)
> llec tytm = (tytm @@ (P2 :: Elim Term)) ::: (tytm @@ (P1:: Elim Term))

> cellType :: Term
> cellType = TBind Ex dull (Sem (Just star) id)

> decl :: LName -> UName -> Bind -> Visibility -> Term -> (Param,Term)
> decl nom unom b v dom =
>   let unom' = case (nom,unom) of
>                 (Long (_ :<: (s,0)),UN "") -> UN s
>                 (Long (_ :<: (s,i)),UN "") -> UN (s ++ show i)
>                 _ -> unom
>       tm = nmTm nom
>   in  (nom :=: unom' :=: (ObjAbst b v,tm ::: dom),tm)

> witp :: LName -> Visibility -> (Term ::: Term) -> Param
> witp nom v tmty = nom :=: UN "" :=: (ObjWit v,tmty)

> infix 4 .|

> (.|) :: LName -> Term -> ((Param,Term),Term)
> nom .| (TBind All (unom,vis) (Sem (Just dom) ran)) =
>   let pt@(_,t) = decl nom unom All vis dom
>   in  (pt,ran t)

> infix 4 -|

> (-|) :: (LName,String) -> Term -> (Params,Term)
> (nom,x) -| t = bof 0 (Zip,t) where
>   bof :: Int -> (Params,Term) -> (Params,Term)
>   bof i (del,t@(TBind All (unom@(UN s),vis) (Sem dom ran))) =
>     let ((p,_),r) = (nom /// (x,i) /// s) .| t
>     in  bof (i + 1) (del :<: p,r)
>   bof i dt = dt

> instance Apply Term ((Zip Term) ::: Params) where
>   f @@ (tz :<: TF (U_ _) ::: del) = f @@ (tz ::: del)
>   f @@ (tz :<: t ::: del :<: p) = f @@ (tz ::: del) @@ (t ::: p)
>   f @@ (Zip ::: Zip) = f
>   f @@ tsdel = error (show tsdel)

> instance Apply Term (Term ::: Param) where
>   f @@ (t ::: (_ :=: _ :=: (ObjAbst _ UnifV,_))) = f @@ u_ @@ t
>   f @@ (t ::: _) = f @@ t

> symDischarge :: Params -> Term -> Tyrm
> symDischarge del t = sd 0 nil (del <>> nil) t where
>   sd :: Int -> List (LName, UName) -> List Param -> Term -> Tyrm
>   sd i ns (Tip _) t = quote i ns t
>   sd i ns ((nom :=: unom :=: (k,x ::: d)) :>: ps) t = case k of
>     ObjWit v -> TF (Pair v (quote i ns x) (sd i ns ps t))
>     ObjDefn  -> sd i ns ps t
>     ObjAbst Lam v ->
>       TBind Lam (unom,v) (Sym i Nothing
>         (sd (i + 1) (ns <+> ((nom, unom) :>: nil)) ps t))
>     ObjAbst b v ->
>       TBind b (unom,v) (Sym i (Just (quote i ns d))
>         (sd (i + 1) (ns <+> ((nom, unom) :>: nil)) ps t))
>     ObjPar ->
>       TBind Lam (unom,NormV) (Sym i Nothing {-(quote i ns d)-}
>         (sd (i + 1) (ns <+> ((nom, unom) :>: nil)) ps t))
>     _ -> error "funny binder in synDischarge"


> -- strict use of symDischarge is much faster than code beneath.
> discharge :: Params -> Term -> Term
> discharge Zip t = t
> discharge del t = eval (eempty :: Env) $! (symDischarge del t) 


<> discharge :: Params -> Term -> Term
<> discharge Zip t = t
<> discharge del t = lif del (parFunc del t) where
<>   lif :: Params -> (Zip Term -> Term) -> Term
<>   lif Zip f = f Zip
<>   lif (del :<: (_ :=: _ :=: (ObjWit v,t ::: _))) f = lif del usp where
<>     usp tz = TF (Pair v t (f (tz :<: t)))
<>   lif (del :<: (_ :=: _ :=: (ObjDefn,t ::: _))) f = lif del usp where
<>     usp tz = f (tz :<: t)
<>   lif (del :<: (_ :=: unom :=: (ok,_ ::: s))) f = lif del usf where
<>     usf tz = TBind (mkb ok) (unom,mkv ok) $
<>                Sem (parFunc del s tz) (f . (tz :<:))
<>   mkb (ObjAbst b _) = b
<>   mkb ObjPar = Lam
<>   mkb _ = error "funny binder in lift!"
<>   mkv (ObjAbst _ v) = v
<>   mkv _ = NormV


******************************************************************************
ugly-print
******************************************************************************

> instance Show Tyrm where
>   show (TBind b (unom,vis) (Sym i dom ran)) = concat
>     ["(",show b," ",show i," ",show vis,show unom," : ",show dom," => ",
>       show ran,")"]
>   show (TF Star) = "*"
>   show (TF One) = "One"
>   show (TF Only) = "()"
>   show (TF Zero) = "Zero"
>   show (TF Bot) = "_|_"
>   show (TF (U_ _)) = "_"
>   show (TF (Pair v x y)) = concat ["(",show v,show x," ; ",show y,")"]
>   show (TF (Con _ unom _ Zip)) = show unom
>   show (TF (Con _ unom _ az)) = concat $
>     "(" : show unom : ((\ a -> [" ",show a]) <!> az) ++ [")"]
>   show (TF (Lbl LabTy (Label (f ::: _) az wwz) _)) = concat $
>     "{" : show f : ((\ a -> [" ",show a]) <!> az) ++ ["}"]
>   show (TF (Lbl Return _ t)) = concat ["(RET ",show t,")"]
>   show (TF (JMEq (x ::: _) (y ::: _))) = concat
>     ["(",show x," = ",show y,")"]
>   show (TF (JMRefl _)) = "REFL"
>   show (TElim h Zip) = show h
>   show (TElim h ez) = "(" ++ zPost blat (show h) ez ++ ")" where
>     blat s (A t) = s ++ " " ++ show t
>     blat s P1 = "(fst " ++ s ++ ")"
>     blat s P2 = "(snd " ++ s ++ ")"
>     blat s (Ind g _) = concat ["(",show (gKind g)," ",s,")"]
>     blat s (Call (Label (f ::: _) az _)) = concat $
>       "(" : show f : ((\ a -> [" ",show a]) <!> az) -- ++ [" := ",show s,")"]
>     blat s (NoughtE _) = concat ["(0e ",show s,")"]
>     blat s (JM JMCoe) = concat ["(Coe ",show s,")"]
>     blat s (JM (JMCon _)) = concat ["(Peano ",show s,")"]
>     blat s (JM JMSym) = concat ["(Sym ",show s,")"]
>     blat s (JM (JMResp (f ::: _))) = concat ["(Resp ",show f," ",show s,")"]


> instance Show (Hd Sym LName) where
>   show (Var (B i u)) = show i ++ show u
>   show (Var (F x)) = show x
>   show (Hope x) = "?" ++ show x
>   show (Wait x) = "~" ++ show x
>   show (Blocked f as) = concat ["(",show f," ",show as,")"]

> instance Show Term where
>   show = show . quote 0 nil 


******************************************************************************
base-funnels
******************************************************************************

(base-funnel "(Sem d r x)")

> instance Fun f => Funnel f (Sem d r x) (f (Sem d r x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Sym d r x)")

> instance Fun f => Funnel f (Sym d r x) (f (Sym d r x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Tm sc x)")

> instance Fun f => Funnel f (Tm sc x) (f (Tm sc x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(TmF t)")

> instance Fun f => Funnel f (TmF t) (f (TmF t)) where
>   fun    = eta
>   funnel = id

(base-funnel "(x ::: y)")

> instance Fun f => Funnel f (x ::: y) (f (x ::: y)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Label t)")

> instance Fun f => Funnel f (Label t) (f (Label t)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Hd sc x)")

> instance Fun f => Funnel f (Hd sc x) (f (Hd sc x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(McKP x)")

> instance Fun f => Funnel f (McKP x) (f (McKP x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(Elim t)")

> instance Fun f => Funnel f (Elim t) (f (Elim t)) where
>   fun    = eta
>   funnel = id

(base-funnel "(JMElim t)")

> instance Fun f => Funnel f (JMElim t) (f (JMElim t)) where
>   fun    = eta
>   funnel = id

