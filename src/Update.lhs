******************************************************************************
**********                                                          **********
**********     Epigram update                                       **********
**********                                                          **********
******************************************************************************

> module Update where

> import Utils
> import Category
> import Monadics
> import Logic
> import Zip
> import Name
> import ObjKind
> import Term
> import Boole

******************************************************************************
Modification Monad
******************************************************************************

> type Mod = State Id Might

> change :: x -> Mod x
> change x = do set (Might True) ; return x


******************************************************************************
Bulletin
******************************************************************************

> data Story
>   = LStory LName LStory
>   | UStory UName
>   deriving Show

> data LStory
>   = NewTerm (Either (Zip (Elim Term)) Term)
>   | NewBoole (Boole LName)
>   | UnitStory
>   deriving Show

> newtype Bulletin = Bulletin (Zip Story) deriving Show

> story :: Story -> Bulletin
> story = Bulletin . (Zip :<:)

> whatOf :: LName -> Bulletin -> Rightmost LStory
> whatOf nom (Bulletin sz) = chk <!> sz where
>   chk (LStory nam x) | nam == nom = return x
>   chk _ = m0

> heardOf :: UName -> Bulletin -> Might
> heardOf unom (Bulletin sz) = chk <!> sz where
>   chk (UStory unam) = Might (unam == unom)
>   chk _ = m0


******************************************************************************
Updatable
******************************************************************************

> infixl 9 <%>

> class Updatable x where
>   upd :: Bulletin -> x -> Mod x
>   upd _ = return
>   update :: Bulletin -> x -> (x,Might)
>   update (Bulletin Zip) x = (x,m0)
>   update bull x = un (un (upd bull x) m0)
>   (<%>) :: Bulletin -> x -> x
>   bull <%> x = fst (update bull x)

> data Trigger x = Trigger x deriving Show

> instance Updatable x => Updatable (Trigger x) where
>   upd bull (Trigger x) = change Trigger <$> upd bull x

> instance Updatable UName where
>   upd bull unom | Might True <- heardOf unom bull = change unom
>                 | otherwise                       = return unom

> instance Updatable LName
> instance Updatable ObjKind

> instance Updatable Story where
>   upd bull (LStory nom ls) = track ("CSUB: " ++ show nom) $
>     fun (LStory nom) (upd bull ls)
>   upd _ x = return x

> instance Updatable LStory where
>   upd bull (NewTerm x)  = fun NewTerm (upd bull x)
>   upd bull (NewBoole b) = fun NewBoole (upd bull b)
>   upd bull UnitStory = fun UnitStory

> instance (Updatable x,Updatable y) => Updatable (Either x y) where
>   upd bull (Left x)  = fun Left (upd bull x)
>   upd bull (Right y) = fun Right (upd bull y)

> instance (Updatable x,Updatable y) => Updatable (x,y) where
>   upd bull (x,y) = fun (,) (upd bull x) (upd bull y)

> instance (Updatable x,Updatable y) => Updatable (x ::: y) where
>   upd bull (x ::: y) = fun (:::) (upd bull x) (upd bull y)

> instance (Updatable x,Updatable y) => Updatable (x :=: y) where
>   upd bull (x :=: y) = fun (:=:) (upd bull x) (upd bull y)

> instance Updatable ()

> instance Updatable Int

 instance (Functorial g,Updatable x) => Updatable (g x) where
   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable (Maybe x) where
>   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable (Zip x) where
>   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable (List x) where
>   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable [x] where
>   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable (Elim x) where
>   upd bull gx = upd bull <^> gx

> instance Updatable x => Updatable (Label x) where
>   upd bull gx = upd bull <^> gx

> instance Updatable Term where
>   upd bull t = {-# SCC "updTerm" #-}
>     case un (blud 0 t) m0 of --un (blat <^> quote 0 nil t) m0 of
>       Id (_,Might False) -> return t
>       Id (t',_) -> change (eval (eempty :: Env) t')
>     where
>       blud :: Int -> Term -> Mod (Tm Sym Term)
>       blud i (TF t) = do
>         t' <- bludF i t
>         return (TF t')
>       blud i (TBind b d@(u, _) (Sem dom ran)) = do
>         dom' <- blud i <^> dom
>         ran' <- blud (i + 1) (ran (var i u))
>         return (TBind b d (Sym i dom' ran'))
>       blud i (TElim h ez) = do
>         h' <- bludH i h
>         ez' <- bludZ (bludE i) ez
>         return (TElim h' ez')
>       bludF :: Int -> TmF Term -> Mod (TmF (Tm Sym Term))
>       bludF i Star = return Star
>       bludF i One = return One
>       bludF i Only = return Only
>       bludF i Zero = return Zero
>       bludF i Bot = return Bot
>       bludF i (U_ j) = return (U_ j)
>       bludF i (JMEq ss tt) = do
>         ss' <- bludTT i ss
>         tt' <- bludTT i tt
>         return (JMEq ss' tt')
>       bludF i (JMRefl tt) = do
>         tt' <- bludTT i tt
>         return (JMRefl tt')
>       bludF i (Pair v x y) = do
>         x' <- blud i x
>         y' <- blud i y
>         return (Pair v x' y')
>       bludF i (Con c u l tz) = do
>         tz' <- bludZ (blud i) tz
>         return (Con c u l tz')
>       bludF i (Lbl k lbl t) = do
>         lbl' <- bludL i lbl
>         t' <- blud i t
>         return (Lbl k lbl' t')
>       bludH :: Int -> Hd Sem LName -> Mod (Hd Sym Term)
>       bludH i (Var (B j u)) = return (Var (B j u))
>       bludH i (Var (F x)) = bludV (Var . F) x
>       bludH i (Hope x) = bludV Hope x
>       bludH i (Wait x) = bludV Wait x
>       bludV :: (forall sc x . x -> Hd sc x) -> LName -> Mod (Hd Sym Term)
>       bludV f x = case whatOf x bull of
>         Rightmost (NewTerm (Left ez)) -> change (f (TElim (f x) ez))
>         Rightmost (NewTerm (Right t)) -> change (f t)
>         _ -> return (f (TElim (f x) Zip))
>       bludTT :: Int -> (Term ::: Term) -> Mod ((Tm Sym Term) ::: (Tm Sym Term))
>       bludTT i (t ::: y) = do
>         t' <- blud i t
>         y' <- blud i y
>         return (t' ::: y')
>       bludZ :: (s -> Mod t) -> Zip s -> Mod (Zip t)
>       bludZ b Zip = return Zip
>       bludZ b (xz :<: x) = do
>         xz' <- bludZ b xz
>         x' <- b x
>         return (xz' :<: x')
>       bludE :: Int -> Elim Term -> Mod (Elim (Tm Sym Term))
>       bludE i (A t) = do
>         t' <- blud i t
>         return (A t')
>       bludE i (NoughtE t) = do
>         t' <- blud i t
>         return (NoughtE t')
>       bludE i P1 = return P1
>       bludE i P2 = return P2
>       bludE i (Call lbl) = do
>         lbl' <- bludL i lbl
>         return (Call lbl')
>       bludE i (Ind g iz) = do
>         iz' <- bludZ (blud i) iz
>         return (Ind g iz')
>       bludE i (JM je) = do
>         je' <- bludJ i je
>         return (JM je')
>       bludJ :: Int -> JMElim Term -> Mod (JMElim (Tm Sym Term))
>       bludJ i JMCoe = return JMCoe
>       bludJ i (JMCon Nothing) = return (JMCon Nothing)
>       bludJ i (JMCon (Just t)) = do
>         t' <- blud i t
>         return (JMCon (Just t'))
>       bludJ i JMSym = return JMSym
>       bludJ i (JMResp tt) = do
>         tt' <- bludTT i tt
>         return (JMResp tt')
>       bludL :: Int -> Label Term -> Mod (Label (Tm Sym Term))
>       bludL i (Label (u ::: t) tz ttz) = do
>         t' <- blud i t
>         tz' <- bludZ (blud i) tz
>         ttz' <- bludZ (bludTT i) ttz
>         return (Label (u ::: t') tz' ttz')


       blat :: LName -> Mod (LName,Rightmost (Either (Zip (Elim Term)) Term))
       blat nom = case whatOf nom bull of
                    Rightmost (NewTerm x) -> change (nom,Rightmost x)
                    _ -> return (nom,Missing)

> instance EvVar Term where
>   vTerm _ t = t

> instance EvVar (LName,Rightmost (Either (Zip (Elim Term)) Term)) where
>   vTerm h (nom,Rightmost (Left ez)) = TElim (h nom) ez
>   vTerm h (nom,Rightmost (Right t)) = t
>   vTerm h (nom,_)                   = TElim (h nom) Zip

> instance Updatable (Boole LName) where
>   upd bull b =
>     case un (blat <^> b) m0 of
>       Id (_,Might False) -> return b
>       Id (b',_)          -> change (mmult b')
>     where
>       blat nom = case whatOf nom bull of
>                    Rightmost (NewBoole b) -> change b
>                    _ -> return (BVar nom)

> instance Monoidal Bulletin where
>   m0 = Bulletin Zip
>   Bulletin Zip <+> bull = bull
>   bull <+> Bulletin Zip = bull
>   xbull@(Bulletin xz) <+> ybull@(Bulletin yz)
>     = {-# SCC "compBulletin" #-} 
>     Bulletin (filt ybull <!> xz <+> xbull <%> yz)
>     where
>       filt ybull (LStory nom _) | Rightmost _ <- whatOf nom ybull = Zip
>       filt _ s = Zip :<: s


******************************************************************************
Reportable
******************************************************************************

> infixr 5 |-

> class Apply a Param =>
>   Reportable a where
>   wait :: LName -> a
>   report :: a -> LStory
>   (|-) :: Params -> a -> a
>   raiser :: LName -> a -> Params -> Bulletin
>   raiser _ _ Zip = m0
>   raiser nom _ del = story (LStory nom (report ((wait nom :: a) @@ del)))

> instance Apply (Boole LName) Param where
>   b @@ _ = b

> instance Reportable (Boole LName) where
>   wait = BVar
>   report = NewBoole
>   _ |- b = b

> instance Reportable Term where
>   wait nom = TElim (Wait nom) Zip
>   report = NewTerm . Right
>   (|-) = discharge
>   raiser nom tm Zip = m0
>   raiser nom tm del = story (LStory nom (NewTerm (Left (parElim <!> del))))

> instance Apply () Param where
>   x @@ _ = x

> instance Reportable () where
>   wait _ = ()
>   report _ = UnitStory
>   _ |- _ = ()


******************************************************************************
Dependency checking
******************************************************************************

> dep :: Updatable t => [LName] -> t -> Might
> dep noms t = snd (update bull t) where
>   bull = Bulletin $
>     (\ nom -> Zip :<: (LStory nom (NewTerm (Left Zip)))) <!> noms

> depSplit :: [Term] -> (Param -> Might) -> Params -> (Params,Params)
> depSplit ts chk Zip = (Zip,Zip)
> depSplit ts chk (del :<: par@(nom :=: obj))
>   | Might True <- dep [nom] ts <+> chk par
>   , (below,above) <- depSplit (obVal obj : obTy obj : ts) chk del
>   = (below :<: par,above)
>   | (below,above) <- depSplit ts chk del
>   = (below,above :<: par)


******************************************************************************
hOpen
*****************************************************************************

> hOpen :: Int -> Term -> Might
> hOpen i (TElim (Hope _) _) = Might True
> hOpen i (TElim (Wait _) _) = Might True
> hOpen i (TElim _ ez) = (hOpen i <!>) <!> ez
> hOpen i (TF t) = hOpen i <!> t
> hOpen i (TBind _ (u, _) (Sem dom ran)) =
>   (hOpen i <!> dom) <+> hOpen (i + 1) (ran (var i u))


******************************************************************************
Gubbins
******************************************************************************

(base-funnel "Story")

> instance Fun f => Funnel f Story (f Story) where
>   fun    = eta
>   funnel = id

(base-funnel "LStory")

> instance Fun f => Funnel f LStory (f LStory) where
>   fun    = eta
>   funnel = id

