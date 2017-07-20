******************************************************************************
**********                                                          **********
**********     Concrete.lhs --- raw concrete syntax; its parsers    **********
**********                                                          **********
******************************************************************************

> module Concrete where

> import Category
> import Name
> import Zip
> import ObjKind
> import Parser
> import Doc
> import Box
> import Emacs

******************************************************************************
Concrete syntax datatypes
******************************************************************************

> data CTerm x
>   = CApp (Zip (CHead x))
>   | CBind Bind (CSigs x) (CTerm x)
>   | CElim IndElim (CTerm x)
>   | CCast (Zip (CHead x)) (CTerm x)
>   | CArrow (Zip (CHead x)) (CTerm x)
>   | CWedge (Zip (CHead x)) (CTerm x)
>   | CEquals (Zip (CHead x)) (Zip (CHead x))
>  deriving Show

> data CHead x
>   = CVar Colour UName
>   | CStar
>   | CQM
>   | CUnder
>   | CZero
>   | COne
>   | CRefl
>   | CTuple [CTerm x]
>   | CTermoid x
>   deriving Show

> data CSigs x
>   = CEmpty
>   | CSig (CSig x)
>   | CSigs (CSigs x) (CSigs x)
>   | CSigsoid x
>   deriving Show

> data CSig x
>   = CSimple [CParam] (Maybe (CTerm x))
>   | CRule (CSigs x) (CCncl x) (CTerm x)
>   deriving Show

> data CCncl x
>   = CCncl (Zip CParam)
>   | CCncloid x
>   deriving Show

> data CParam
>   = CParam Bool Visibility UName
>   deriving Show

> data CDecl x
>   = CData (Maybe x) (CSigs x) (CSigs x)
>   | CLet (CSigs x) (Maybe (CProg x))
>   | CInspect (Maybe (CTerm x)) (CTerm x)
>   | CInclude String
>   | CBegin String
>   | CEnd String
>   | CSourcoid x
>   deriving Show

> data CProg x
>   = CProg (CLhs x) [CRhs x] (Maybe (CProgs x))
>   | CProgoid x
>   deriving Show

> data CLhs x
>   = CLhs (Zip (CHead x)) (Zip (CHead x))
>   | CLhsoid x
>   deriving Show

> data CRhs x
>   = CBy (CTerm x)
>   | CWith (CTerm x)
>   | CFrom [UName]
>   | CRet (CTerm x)
>   | CRhssoid x
>   deriving Show

> data CProgs x
>   = CProgs [CProg x]
>   | CProgsoid x
>   deriving Show

******************************************************************************
Parsers
******************************************************************************

> instance Parse Maybe Item (Zip (CHead Lexical)) where
>   blah = eta zippy <$> pSeq1 blah pE

> instance Parse Maybe Item (CTerm Lexical) where
>   blah = eta (flip ($)) <$> blah <$>
>            (eta (flip CCast) </> iP (pF COLON) <$> blah <+>
>             eta (flip CArrow) </> iP (pF ARROW) <$> blah <+>
>             eta (flip CWedge) </> iP (pF WEDGE) <$> blah <+>
>             eta (flip CEquals) </> iP (pF EQUALS) <$> blah <+>
>             eta CApp)
>      <+> eta CBind <$> blah <$> blah </> iPP (pF RET) <$> blah
>      <+> eta CElim <$> blah <$> blah
>      <+> eta CArrow <$> blah </> iP (pF ARROW) <$> blah
>      <+> eta CWedge <$> blah </> iP (pF WEDGE) <$> blah
>      <+> eta CEquals <$> blah </> iP (pF EQUALS) <$> blah

> realHead :: Parser Maybe Item (CHead Lexical)
> realHead = eta (CVar Black) <$> blah
>        <+> eta CStar </> pF STAR
>        <+> eta CQM </> pF QM
>        <+> eta CUnder </> pF UNDER
>        <+> eta CZero </> pF ZERO
>        <+> eta COne </> pF ONE
>        <+> eta CRefl </> pF REFL
>        <+> iGroup (eta CTuple <$> pSeq0 blah iLFs)

> instance Parse Maybe Item (CHead Lexical) where
>   blah = realHead
>      <+> eta CTermoid <$> blah

> instance Parse Maybe Item (CSigs Lexical) where
>   blah = eta sigon <$> sigone </> iSkip <$> blah
>      <+> eta CEmpty
>     where
>       sigone = eta CSig <$> blah
>            <+> eta CSigsoid <$> blah
>       sigon ss1 CEmpty = ss1
>       sigon ss1 ss2    = CSigs ss1 ss2

> instance Parse Maybe Item (CSig Lexical) where
>    blah = eta CSimple <$> pSeq1 blah (pF COMMA)
>                       <$> pMay (iPP (pF COLON) <\> blah)
>       <+> iGroup (eta CRule <$> iPP blah </> iP (pF RULE) <$>
>                     blah  </> iPP (pF COLON) <$> blah)

> instance Parse Maybe Item (CCncl Lexical) where
>    blah = eta (CCncl . zippy) <$> pSeq1 blah pE
>       <+> eta CCncloid <$> blah

> instance Parse Maybe Item CParam where
>    blah = eta (CParam False UnifV) </> pF UNDER <$> blah
>       <+> eta (CParam False NormV) <$> blah

> pFileName :: Parser Maybe Item String
> pFileName = eta "" </> iLFs
>         <+> eta (++) <$> pT toktext <$> pFileName
>         where toktext (I s) = return (show s)
>               toktext _     = m0

> instance Parse Maybe Item (CDecl Lexical) where
>   blah = eta (CData Nothing) </> iP (pF DATA) 
>            <$> blah </> iPP (pF WHERE) <$> blah
>      <+> eta CLet </> iP (pF LET)
>          <$> (eta CSig <$> blah <+> eta CSigsoid <$> blah)
>          </> iLFs <$> pMay blah
>      <+> eta (CInspect Nothing) </> iP (pF INSPECT)
>            <$> blah </> pSkipTo (I RULE)
>      <+> eta CSourcoid <$> blah
>      <+> iP (pF DATA) <\> eta
>           (CData Nothing (CSig (CRule (CSigsoid emptyEDoc)
>                                       (CCncloid emptyEDoc)
>                                       (CApp (Zip :<: CStar))))
>                          (CSigsoid emptyEDoc))
>      <+> iP (pF LET) <\> eta
>           (CLet (CSig (CRule (CSigsoid emptyEDoc)
>                              (CCncloid emptyEDoc)
>                              (CApp (Zip :<: CTermoid emptyEDoc))))
>                 Nothing)
>      <+> iP (pF INSPECT) <\> eta (CInspect Nothing
>                                 (CApp (Zip :<: (CTermoid emptyEDoc))))
>      <+> eta CInclude </> iP (pF INCLUDE) <$> pFileName
>      <+> eta CBegin </> iP (pF BEGIN) <$> pFileName
>      <+> eta CEnd </> iP (pF END) <$> pFileName

> instance Parse Maybe Item (CProg Lexical) where
>   blah = eta CProg <$> blah </> iSkip
>                    <$> pSeq1 blah iSkip <$> (eta Just <$> blah)
>      <+> eta CProgoid <$> blah

> instance Parse Maybe Item (CLhs Lexical) where
>   blah = eta CLhs <$> (eta zippy <$> pSeq1 realHead pE)
>                   <$> (eta zippy <$> pSeq0 (pF BAR <\> blah) pE)

> instance Parse Maybe Item (CRhs Lexical) where
>   blah = eta CBy </> iP (pF BY) <$> blah
>      <+> eta CWith </> iP (pF WITH) <$> blah
>      <+> eta CFrom </> iP (pF FROM) <$> pSeq1 blah pE
>      <+> eta CRet </> iP (pF RET) <$> blah
>      <+> eta CRhssoid <$> blah

> instance Parse Maybe Item (CProgs Lexical) where
>   blah = eta CProgs </> iPP (pF LBRACE) <$>
>            pSeq0 blah iLFs </> iSkip </> pF RBRACE
>      <+> eta (CProgs [])

> instance Parse Maybe Item UName where
>   blah = pT f where
>     f (I (ID x)) = eta (UN x)
>     f _          = m0

> instance Parse Maybe Item Bind where
>   blah = pF [(LAM,Lam),(ALL,All),(EX,Ex)]

> instance Parse Maybe Item IndElim where
>   blah = pF [(CASE,ICase),(MEMO,IMemo),(REC,IRec),(VIEW,IView),(GEN,IGen)]

> sourceParser :: Parser Maybe Item [CDecl Lexical]
> sourceParser = iP (pF RULE) <\> sourceParser
>            <+> eta (:) <$> iP blah <$> sourceParser
>            <+> eta []



******************************************************************************
Boxers
******************************************************************************

> gApp :: Boxings -> Boxings -> Boxings
> gApp = horvB _B Nothing (box0,PCT |?| _B)

> gDot :: Boxings -> Boxings -> Boxings
> gDot = horvB (_B |?| RET |?| _B) (Just (_B |?| RET,box0,__B))
>          (box0,RET |?| _B)

> gSig :: Boxings -> Boxings -> Boxings
> gSig = horvB (_B |?| LF |?| __B) Nothing (lineB,box0)

> gColon :: Boxings -> Boxings -> Boxings
> gColon = bhorvB (_B |?| COLON |?| _B) (Just (_B |?| COLON,box0,__B))
>            (box0,_B |?| COLON |?| _B)

> gComma :: Boxings -> Boxings -> Boxings
> gComma = horvB (COMMA |?| _B) (Just (box COMMA,box0,__B))
>            (box0,_B |?| COMMA |?| _B)

> gProg :: Boxings -> Boxings -> Boxings
> gProg  = horvB _B Nothing (box0,__B)

> gRhs :: Boxings -> Boxings -> Boxings
> gRhs = horvB _B Nothing (box0,box0)

> gBar :: Boxings -> Boxings -> Boxings
> gBar = horvB (_B |?| BAR |?| _B) Nothing (box0,PCT |?| _B |?| BAR |?| _B)

> gArrow :: Boxings -> Boxings -> Boxings
> gArrow = bhorvB (_B |?| ARROW |?| _B) (Just (_B |?| ARROW,box0,__B))
>            (box0,PCT |?| _B |?| ARROW |?| _B)

> gWedge :: Boxings -> Boxings -> Boxings
> gWedge = bhorvB (_B |?| WEDGE |?| _B) (Just (_B |?| WEDGE,box0,__B))
>            (box0,PCT |?| _B |?| WEDGE |?| _B)

> gEquals :: Boxings -> Boxings -> Boxings
> gEquals = bhorvB (_B |?| EQUALS |?| _B) (Just (_B |?| EQUALS,box0,__B))
>            (box0,_B |?| EQUALS |?| _B)


> gTurnstile :: Boxings -> Boxings -> Boxings
> gTurnstile = bhorvB (_B |?| "|-" |?| _B) Nothing (box "|-",box0)

> instance Boxes (Zip (CHead Boxings)) where
>   box hz = seqB gApp (fmap box (yppiz hz))

> instance Boxes (CTerm Boxings) where
>   box (CApp hz) = box hz
>   box (CBind bop ss t) = gDot (bop |?| _B |?| ss) (box t)
>   box (CElim el t) = gApp (box el) (box t)
>   box (CCast hz t) = box (CApp hz) `gColon` box t
>   box (CArrow s t) = box s `gArrow` box t
>   box (CWedge s t) = box s `gWedge` box t
>   box (CEquals s t) = box s `gEquals` box t

> instance Boxes (CHead Boxings) where
>   box (CVar Black unom) = box unom
>   box (CVar col unom) = faceB (Face Background OK col) (box unom)
>   box CStar = box STAR
>   box CQM = box QM
>   box CZero = faceB (Face Background OK Blue) (box ZERO)
>   box COne = faceB (Face Background OK Blue) (box ONE)
>   box CRefl = faceB (Face Background OK Red) (box REFL)
>   box CUnder = box UNDER
>   box (CTuple ts) = jack (bBracket ROUND) $ vertList (fmap box ts)
>   box (CTermoid b) = b

> instance Boxes (CSigs Boxings) where
>   box CEmpty = box0
>   box (CSig sig) = box sig
>   box (CSigs ss1 ss2) = skipSep gSig (box ss1) (box ss2)
>   box (CSigsoid b) = b

> bSimple :: [Boxings] -> Maybe Boxings -> Boxings
> bSimple ps (Just t) = gColon (seqB gComma ps) t
> bSimple ps Nothing  = seqB gComma ps

> instance Boxes (CSig Boxings) where
>   box (CSimple ps mt) = bSimple (up box ps) (up box mt)
>   box (CRule ss c t) = jack (bBracket ROUND) .
>                          jack bRule (box ss) $ gColon (box c) (box t)

> instance Boxes (CCncl Boxings) where
>   box (CCncl ps) = seqB gApp (up box (yppiz ps))
>   box (CCncloid b) = b

> instance Boxes CParam where
>   box (CParam False UnifV unom) = UNDER |?| box unom
>   box (CParam False NormV unom) = box unom
>   box (CParam True UnifV unom) = UNDER |?| box (ObjPar,unom)
>   box (CParam True NormV unom) = box (ObjPar,unom)

> instance Boxes (CDecl Boxings) where
>   box (CData mb fss css) =
>     horvB (__B |?| WHERE |?| _B) Nothing (lineB,WHERE |?| _B)
>     (db |?| _B |?| box fss) (box css)
>     where
>       db = case mb of
>         Nothing -> box DATA
>         Just b -> b
>   box (CLet ss (Just p)) = LET |?| __B |?| gSig (box ss) (box p)
>   box (CLet ss Nothing) = LET |?| __B |?| box ss
>   box (CInspect Nothing t) = INSPECT |?| _B |?| t
>   box (CInspect (Just v) t) =
>     INSPECT |?| _B |?| (box t `gProg` (box RET `gRhs` box v))
>   box (CSourcoid b) = b
>   box (CInclude str) = INCLUDE |?| _B |?| str
>   box (CBegin str)   = BEGIN |?| _B |?| str
>   box (CEnd str)     = END |?| _B |?| str

> instance Boxes (CProg Boxings) where
>   box (CProg l rs (Just ps)) =
>     gProg (box l) (seqB gRhs (fmap box rs)) -#- box ps
>   box (CProg l rs Nothing) =
>     gProg (box l) (seqB gRhs (fmap box rs))
>   box (CProgoid b) = b

> instance Boxes (CLhs Boxings) where
>   box (CLhs as ws) = seqB gBar
>                      (seqB gApp (up box (yppiz as)) : up box (yppiz ws))
>   box (CLhsoid b) = b

> instance Boxes (CRhs Boxings) where
>   box (CBy t) = gRhs (box BY) (box t)
>   box (CWith t) = gRhs (box WITH) (box t)
>   box (CFrom us) = gRhs (box FROM) (seqB gApp (fmap box us))
>   box (CRet t) = gRhs (box RET) (box t)
>   box (CRhssoid b) = b

> instance Boxes (CProgs Boxings) where
>   box (CProgs []) = box0
>   box (CProgs ps) =
>     LBRACE |?| _B |?| seqB (-#-) (fmap box ps) -#- box RBRACE
>   box (CProgsoid b) = b

> instance Boxes Bind where
>   box = box . show

> instance Boxes UName where
>   box = box . show

> instance Boxes IndElim where
>   box = box . show


******************************************************************************
base-funnels
******************************************************************************

(base-funnel "(CTerm x)")

> instance Fun f => Funnel f (CTerm x) (f (CTerm x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CHead x)")

> instance Fun f => Funnel f (CHead x) (f (CHead x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CSigs x)")

> instance Fun f => Funnel f (CSigs x) (f (CSigs x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CSig x)")

> instance Fun f => Funnel f (CSig x) (f (CSig x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CCncl x)")

> instance Fun f => Funnel f (CCncl x) (f (CCncl x)) where
>   fun    = eta
>   funnel = id

(base-funnel "CParam")

> instance Fun f => Funnel f CParam (f CParam) where
>   fun    = eta
>   funnel = id

(base-funnel "(CDecl x)")

> instance Fun f => Funnel f (CDecl x) (f (CDecl x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CProg x)")

> instance Fun f => Funnel f (CProg x) (f (CProg x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CLhs x)")

> instance Fun f => Funnel f (CLhs x) (f (CLhs x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CRhs x)")

> instance Fun f => Funnel f (CRhs x) (f (CRhs x)) where
>   fun    = eta
>   funnel = id

(base-funnel "(CProgs x)")

> instance Fun f => Funnel f (CProgs x) (f (CProgs x)) where
>   fun    = eta
>   funnel = id


******************************************************************************
Functoriality
******************************************************************************

> instance Functorial CTerm where
>   g <^> CApp hs = fun CApp (g <^^> hs)
>   g <^> CBind b ss ts = fun (CBind b) (g <^> ss) (g <^> ts)
>   g <^> CElim e t = fun (CElim e) (g <^> t)
>   g <^> CCast t y = fun CCast (g <^^> t) (g <^> y)
>   g <^> CArrow s t = fun CArrow (g <^^> s) (g <^> t)
>   g <^> CWedge s t = fun CWedge (g <^^> s) (g <^> t)
>   g <^> CEquals s t = fun CEquals (g <^^> s) (g <^^> t)

> instance Functorial CHead where
>   g <^> CVar c u = fun (CVar c u)
>   g <^> CStar  = fun CStar
>   g <^> CQM    = fun CQM
>   g <^> CUnder = fun CUnder
>   g <^> CZero  = fun CZero
>   g <^> COne   = fun COne
>   g <^> CRefl  = fun CRefl
>   g <^> CTuple ts = fun CTuple (g <^^> ts)
>   g <^> CTermoid x = fun CTermoid (g x)

> instance Functorial CSigs where
>   g <^> CEmpty = fun CEmpty
>   g <^> CSig s = fun CSig (g <^> s)
>   g <^> CSigs ss1 ss2 = fun CSigs (g <^> ss1) (g <^> ss2)
>   g <^> CSigsoid x = fun CSigsoid (g x)

> instance Functorial CSig where
>   g <^> CSimple ps t = fun (CSimple ps) (g <^^> t)
>   g <^> CRule ss c t = fun CRule (g <^> ss) (g <^> c) (g <^> t)

> instance Functorial CCncl where
>   g <^> CCncl ps = fun (CCncl ps)
>   g <^> CCncloid x = fun CCncloid (g x)

> instance Functorial CDecl where
>   g <^> CData gs fs cs = fun CData (g <^> gs) (g <^> fs) (g <^> cs)
>   g <^> CLet ss p = fun CLet (g <^> ss) (g <^^> p)
>   g <^> CInspect v t = fun CInspect (g <^^> v) (g <^> t)
>   g <^> CSourcoid x = fun CSourcoid (g x)
>   g <^> CInclude str = fun (CInclude str)
>   g <^> CBegin str = fun (CBegin str)
>   g <^> CEnd str = fun (CEnd str)

> instance Functorial CProg where
>   g <^> CProg l rs ps = fun CProg (g <^> l) (g <^^> rs) (g <^^> ps)
>   g <^> CProgoid x = fun CProgoid (g x)

> instance Functorial CLhs where
>   g <^> CLhs as ws = fun CLhs (g <^^> as) (g <^^> ws)
>   g <^> CLhsoid x = fun CLhsoid (g x)

> instance Functorial CRhs where
>   g <^> CBy t = fun CBy (g <^> t) 
>   g <^> CWith t = fun CWith (g <^> t)
>   g <^> CFrom us = fun (CFrom us)
>   g <^> CRet t = fun CRet (g <^> t)
>   g <^> CRhssoid x = fun CRhssoid (g x)

> instance Functorial CProgs where
>   g <^> CProgs ps = fun CProgs (g <^^> ps)
>   g <^> CProgsoid x = fun CProgsoid (g x)
