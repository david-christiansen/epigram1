******************************************************************************
**********                                                          **********
**********     Doc.lhs   Epigram editable documents                 **********
**********                                                          **********
******************************************************************************

> module Doc where

> import Utils
> import Category
> import Monadics
> import Zip
> import Parser
> import Logic
> import Array

> -- import Debug.Trace

> type WHD = (Int,(Int,Int))

> class Wide x where
>   width :: x -> Int

> data Sized x = Sized WHD x deriving Show

> instance Wide (Sized x) where
>   width (Sized (w,_) _) = w

> instance Wide Element where
>   width (EC _) = 1
>   width EMark = 0
>   width (EB _ sdoc) = 2 + width sdoc

> instance Wide (Zip (Sized (Zip Element))) where
>   width fl = action (\ x y -> max (width x) y) fl 0

> instance Wide (List (Sized (List Element))) where
>   width fl = action (\ x y -> max (width x) y) fl 0

> class Tall x where
>   tallness :: x -> Int

> instance Tall (Sized x) where
>   tallness (Sized (_,(h,d)) _) = h + d

> instance Tall x => Tall (Zip x) where
>   tallness xz = tallness <!> xz

> instance Tall x => Tall (List x) where
>   tallness xs = tallness <!> xs

> instance Monoidal (Sized (Zip Element)) where
>   m0 = Sized (0,(0,1)) Zip
>   Sized (w1,(h1,d1)) z1 <+> Sized (w2,(h2,d2)) z2 =
>     Sized (w1 + w2,(max h1 h2,max d1 d2)) (z1 <+> z2)


> data Bracket = ROUND | SQUARE deriving (Show,Eq)

(base-funnel "Bracket")

> instance Fun f => Funnel f Bracket (f Bracket) where
>   fun    = eta
>   funnel = id

> data Element
>   = EC Char
>   | EMark
>   | EB Bracket (Sized Doc)
>   deriving Show

> isMark :: Element -> Bool
> isMark EMark = True
> isMark _     = False

> data Doc = Doc
>   { above :: Zip (Sized (Zip Element))
>   , here  :: Sized (Cursor Element)
>   , below :: List (Sized (List Element))
>   } deriving Show

> instance Wide Doc where
>   width (Doc ab he be) = width ab `max` width he `max` width be

> instance Tall Doc where
>   tallness (Doc ab he be) = tallness ab + tallness he + tallness be

> emptyDoc :: Doc
> emptyDoc = Doc Zip (Sized (0,(0,1)) (Zip :*: nil)) nil

> data Sep
>   = Open Bracket
>   | Close Bracket
>   | Tab
>   | EoL
>   deriving Eq

(base-funnel "Sep")

> instance Fun f => Funnel f Sep (f Sep) where
>   fun    = eta
>   funnel = id

> instance Parse Maybe Char Sep where
>   blah = fun Open  (fun ROUND  </> pCon '(' <+> fun SQUARE </> pCon '[')
>      <+> fun Close (fun ROUND  </> pCon ')' <+> fun SQUARE </> pCon ']')
>      <+> fun Tab </> pCon '!'
>      <+> fun EoL </> eol

> instance Show Sep where
>   show (Open  ROUND)  = "("
>   show (Close ROUND)  = ")"
>   show (Open  SQUARE) = "["
>   show (Close SQUARE) = "]"
>   show Tab            = "!"
>   show EoL            = "\n"

> eol :: Parser Maybe Char ()
> eol = fun () </> (    pCon '\n' </> pMay (pCon '\r')
>                   <+> pCon '\r' </> pMay (pCon '\n'))

> type Body = Either Int String

> bcons :: Char -> Body -> Body
> bcons ' ' (Left i)   = Left (i + 1)
> bcons  c  (Left i)   = Right (c : take i spaces)
> bcons  c  (Right cs) = Right (c : cs)

> instance Parse Maybe Char (Body,Sep) where
>   blah = fun ((,) (Left 0)) blah
>      <+> fun (\ c (b,s) -> (bcons c b,s)) pI blah where {}

> chunk :: String -> Maybe [(Body,Sep)]
> chunk = reading (pSeq0 blah pE)

> type PState = (Int,Int)

> makeOn :: PState -> PState
> makeOn (i,0) = (i - 1,1)
> makeOn ij = ij

> type Done = Sized (Zip Element)

> type PSM = State Maybe PState

> data Plan
>   = PZone (Int,Body)
>   | POpen Int Plan (Bracket,(Zip Done,(PState,Plan))) Plan
>   | PClosed Int Plan (Bracket,Zip Done) Plan
>   deriving Show

(base-funnel "Plan")

> instance Fun f => Funnel f Plan (f Plan) where
>   fun    = eta
>   funnel = id

> zoneBody :: (Int,Body) -> Body -> (Int,Body)
> zoneBody (i,b) b' = (i + 1,f b b') where
>   f (Left x) (Left y) = Left (min x y)
>   f (Left _) b' = b'
>   f b _ = b

> planDone :: (Int,Int) -> Plan -> Maybe (Sized (Zip Element))
> planDone _ (POpen _ _ _ _) = m0
> planDone hd (PZone (_,Left w)) = eta $
>   Sized (w,hd) (zCrop w (eta (EC ' ')))
> planDone hd (PZone (_,Right s)) = eta $ (Sized (1,hd) . (Zip :<:) . EC) <!> s
> planDone (h,d) (PClosed i lp (br,dz) rp) =
>   do lz <- planDone (h - i,d) lp
>      rz <- planDone (h - i,d) rp
>      return (lz <+> (zdocSez br (h - i) dz) <+> rz)

> zadok :: Zip Done -> Doc
> zadok Zip = error "zadok the least"
> zadok (dz :<: Sized whd ez) = Doc
>   { above = dz
>   , here  = Sized whd (ez :*: nil)
>   , below = nil }

> zdocSez :: Bracket -> Int -> Zip Done -> Sized (Zip Element)
> zdocSez br h dz
>   | doc <- zadok dz
>   , w <- width doc
>   , t <- tallness doc
>   = Sized (w + 2,(h,t - h)) $ Zip :<: EB br (Sized (w,(h,t - h)) doc)

> plan0 :: Plan
> plan0 = PZone (0,Left 100)

> psGo :: (PState,Plan)
> psGo = ((1,0),plan0)

> planStep :: (Zip Done,(PState,Plan)) -> (Zip Done,(PState,Plan))
> planStep (dz,(st,p)) | Just d <- planDone (makeOn st) p = (dz :<: d,psGo)
> planStep (dz,(st,p)) = (dz,(nxt st,p)) where
>   nxt (i,0) = (i + 1,0)
>   nxt (i,j) = (i,j + 1)

> planBracket :: (Bracket,(Zip Done,(PState,Plan))) ->
>                Parser PSM (Body,Sep)
>                  (Either (Bracket,(Zip Done,(PState,Plan)))
>                          (Bracket,Zip Done))
> planBracket (br,(dz,(ist,ip))) =
>   do st <- doo $ get id
>      doo $ set ist
>      (ip',sep) <- planRead ip [Tab,Close br]
>      ist' <- doo $ get id
>      case (sep,planStep (dz,(ist',ip'))) of
>        (Tab,dzstip) ->
>          do doo $ set st
>             return (Left (br,dzstip))
>        (_,(dz,(_,PZone (0,_)))) ->
>          do doo $ set (makeOn st)
>             return (Right (br,dz))
>        _ -> m0

> planTab :: Plan -> Parser PSM (Body,Sep) Plan
> planTab p = fun fst (planRead p [Tab])

> planSkip :: Plan -> Parser PSM (Body,Sep) Plan
> planSkip p@(PZone _) = fun p
> planSkip (POpen i lp stuf rp) =
>   fun (reopen i) (planTab lp) (planBracket stuf) (planSkip rp)
> planSkip (PClosed i lp brdz rp) =
>   fun (PClosed i) (planSkip lp) (eta brdz) (planSkip rp)

> bodySep :: [Sep] -> Parser PSM (Body,Sep) (Body,Sep)
> bodySep seps = pT bst where
>   bst :: (Body,Sep) -> PSM (Body,Sep)
>   bst bs@(b,sep) =
>     do ensure (elem sep seps)
>        st <- get id
>        case (st,b) of
>          ((i,0),Right _) -> do set (i - 1,1) ; return bs
>          ((i,j),Right _) | j > 1 -> m0
>          _ -> return bs

> bodyOpen :: Parser PSM (Body,Sep) (Body,Bracket)
> bodyOpen =
>   do (b,Open br) <- bodySep [Open ROUND,Open SQUARE]
>      return (b,br)

> planRead :: Plan -> [Sep] -> Parser PSM (Body,Sep) (Plan,Sep)
> planRead (PZone ib) seps =
>   do (b,sep) <- bodySep seps
>      eta (PZone (zoneBody ib b),sep)
>   <+>
>   do (b,br) <- bodyOpen
>      brute <- planBracket (br,(Zip,psGo))
>      (rp,sep) <- planRead plan0 seps
>      return $ (reopen (fst ib) (PZone (1,b)) brute rp,sep)
> planRead (POpen i lp stuf rp) seps =
>   do lp' <- planTab lp
>      brute <- planBracket stuf
>      (rp',sep) <- planRead rp seps
>      return (reopen i lp' brute rp',sep)
> planRead (PClosed i lp brdz rp) seps =
>   do lp' <- planSkip lp
>      (rp',sep) <- planRead rp seps
>      return (PClosed i lp' brdz rp',sep)

> reopen :: Int -> Plan ->
>           Either (Bracket,(Zip Done,(PState,Plan))) (Bracket,Zip Done) ->
>           Plan -> Plan
> reopen bz lp (Left stuf) rp = POpen bz lp stuf rp
> reopen bz lp (Right dz) rp  = PClosed bz lp dz rp

> planDoc :: (Zip Done,Plan) -> Parser PSM (Body,Sep) (Zip Done)
> planDoc (dz0,p0) =
>   do (p1,_) <- planRead p0 [EoL]
>      st1 <- doo $ get id
>      let (dz2,(st2,p2)) = planStep (dz0,(st1,p1))
>      doo $ set st2
>      planDoc (dz2,p2) <+>
>        case p2 of
>          PZone _ -> pEmpty <\> fun dz2
>          _ -> m0

> getDoc :: [(Body,Sep)] -> Maybe Doc
> getDoc = up zadok . result (1,0) . reading (planDoc (Zip,plan0))




> type DocLayer = (Sized Doc,Bracket)

> type EditDoc = (Zip DocLayer,Sized Doc)

> emptyEDoc :: EditDoc
> emptyEDoc = (Zip,Sized (0,(0,1)) emptyDoc)

> outDoc :: Trans EditDoc
> outDoc (lz :<: (Sized whd doc,br),sdoc)
>   | Sized x (ez :*: es) <- here doc
>   = eta (lz,Sized whd $ doc { here = Sized x (ez :*: EB br sdoc :>: es) })
> outDoc _ = m0

> inDoc :: Trans EditDoc
> inDoc (lz,Sized whd doc)
>   | Sized x (ez :*: EB br sdoc :>: es) <- here doc
>   = eta (lz :<: (Sized whd $ doc { here = Sized x (ez :*: es)},br),sdoc)
> inDoc _ = m0

> leftDoc :: Trans EditDoc
> leftDoc (lz,Sized whd doc)
>   | Sized hwhd (ez :<: e :*: es) <- here doc
>   = eta (lz,Sized whd $ doc { here = Sized hwhd (ez :*: e :>: es) })
> leftDoc _ = m0

> rightDoc :: Trans EditDoc
> rightDoc (lz,Sized whd doc)
>   | Sized hwhd (ez :*: e :>: es) <- here doc
>   = eta (lz,Sized whd $ doc { here = Sized hwhd (ez :<: e :*: es) })
> rightDoc _ = m0

> upDoc :: Trans EditDoc
> upDoc (lz,Sized whd Doc 
>   { above = uz :<: Sized uwhd uez
>   , here  = Sized hwhd (ez :*: es)
>   , below = ds }) = eta (lz,Sized whd Doc
>   { above = uz
>   , here = Sized uwhd (uez :*: nil)
>   , below = Sized hwhd (ez <>> es) :>: ds })
> upDoc _ = m0

> downDoc :: Trans EditDoc
> downDoc (lz,Sized whd Doc 
>   { above = uz
>   , here = Sized hwhd (ez :*: es)
>   , below = Sized dwhd des :>: ds }) = eta (lz,Sized whd Doc
>   { above = uz :<: Sized hwhd (ez <>< es)
>   , here  = Sized dwhd (Zip :*: des)
>   , below = ds })
> downDoc _ = m0

> sizeDoc :: Doc -> Sized Doc
> sizeDoc doc = Sized (width doc,(0,tallness doc)) doc



******************************************************************************
Symbols
******************************************************************************

> data Symbol
>   = LF | COLON | DOT | COMMA | PCT | RULE
>   | RET | BY | WITH | FROM | BAR
>   | CARET | QM
>   | ARROW | STAR | EQUALS | WEDGE
>   | LBRACE | RBRACE | ELLIPSIS
>   | UNDER
>   | LET | DATA | WHERE | INSPECT | INCLUDE | BEGIN | END
>   | LAM | ALL | EX
>   | CASE | REC | VIEW | MEMO | GEN
>   | ONE | ZERO | REFL
>   | ID String
>   | INT Int
>   deriving Eq

(base-funnel "Symbol")

> instance Fun f => Funnel f Symbol (f Symbol) where
>   fun    = eta
>   funnel = id

> speshAList :: [(String,Symbol)]
> speshAList
>   = [(";",LF),(":",COLON),(".",DOT),(",",COMMA),("%",PCT),("---",RULE)
>     ,("=>",RET),("<=",BY),("||",WITH),("<-",FROM),("|",BAR)
>     ,("^",CARET),("?",QM),("/\\",WEDGE)
>     ,("->",ARROW),("*",STAR),("=",EQUALS)
>     ,("{",LBRACE),("}",RBRACE),("...",ELLIPSIS),("_",UNDER)
>     ]

> wordAList :: [(String,Symbol)]
> wordAList
>   = [("let",LET),("data",DATA),("where",WHERE),("inspect",INSPECT)
>     ,("include",INCLUDE),("begin",BEGIN),("end",END)
>     ,("lam",LAM),("all",ALL),("ex",EX)
>     ,("case",CASE),("rec",REC),("view",VIEW),("memo",MEMO),("gen",GEN)
>     ,("One",ONE),("Zero",ZERO),("refl",REFL)
>     ]

> symbolAList :: [(Symbol,String)]
> symbolAList = fmap swap speshAList ++ fmap swap wordAList
>   where swap (x,y) = (y,x)

> sym :: String -> Symbol
> sym s | Just x <- lookup s wordAList  = x
>       | Just x <- lookup s speshAList = x
>       | Just n <- numeral s           = INT n
>       | otherwise                     = ID s

> instance Show Symbol where
>   show (ID s)  = s
>   show (INT n) = show n
>   show x | Just s <- lookup x symbolAList = s
>   show _ = ""


******************************************************************************
Character classifications
******************************************************************************

> data CharCl = CSpace
>             | CAlpha
>             | CDigit
>             | CSpesh
>             | CSep
>             | CGroupy
>             deriving (Show,Eq,Enum,Ord)

(base-funnel "CharCl")

> instance Fun f => Funnel f CharCl (f CharCl) where
>   fun    = eta
>   funnel = id


> classify :: Char -> CharCl
> classify x = if inRange myRange x then charTable ! x else CSpace
>   where
>
>     classifications :: [(CharCl,[Char])]
>     classifications = 
>      [(CAlpha,'\'' : ['a'..'z'] ++ ['A'..'Z']),
>       (CDigit,['0'..'9']),
>       (CSpesh,".|\"$%^&*-=+@~<>/?{}`\\#"),
>       (CSep,";,_:"),
>       (CGroupy,"([])!\n\r")
>      ]
>
>     mkArray :: (Ix a) => (a -> b) -> (a,a) -> Array a b
>     mkArray f bnds = array bnds [(i,f i) | i <- range bnds]
>
>     myRange :: (Char,Char)
>     myRange = (toEnum 0,toEnum 127)
>
>     charTable :: Array Char CharCl
>     charTable = mkArray classy myRange
>       where classy :: Char -> CharCl
>             classy x = foldr check CSpace classifications
>               where check (cl,cs) b = if x `elem` cs then cl else b


******************************************************************************
Tokenizing (we keep the info about the space before each lexeme, hence...)
******************************************************************************

> smash :: String -> String
> smash "" = ""
> smash (c : cs) | classify c == CSpesh = c : smashing 2 cs where
>   smashing i (d : ds) | c == d =
>     if i > 0 then c : smashing (i - 1) ds else smashing 0 ds
>   smashing _ ds = smash ds
> smash (c : cs) = c : smash cs

> tokenize :: String -> [Symbol]
> tokenize "" = []
> tokenize (x : xs)
>   = case classify x of
>       CSpace  -> tokenize xs
>       CGroupy -> error "Groupy characters should be filtered before tokenize"
>       CSep    -> sym [x] : tokenize xs
>       CDigit -> tokMore id [x] [CDigit] xs
>       CAlpha -> tokMore id [x] [CAlpha,CDigit] xs
>       CSpesh -> tokMore smash [x] [CSpesh,CSep] xs
>   where
>     tokMore done ys cs (z : zs)
>       | elem (classify z) cs = tokMore done (z : ys) cs zs
>     tokMore done ys _ zs
>       | (ys',zs') <- sepTweak ys zs
>       = sym (done (reverse ys')) : tokenize zs'
>     sepTweak (y : ys) zs
>       | CSep <- classify y
>       = (ys,y : zs)
>     sepTweak ys zs = (ys,zs)


******************************************************************************
Items
******************************************************************************

> type Lexical = EditDoc

> data Item
>   = I Symbol
>   | Group Items
>   | Block Lexical
>   deriving Show

> instance Eq Item where
>   I x == I y = x == y
>   _ == _ = False

> newtype Items = Items [Item] deriving Show

> instance Unpack Items [Item] where
>   un (Items is) = is
>   nu = Items

> icons :: Item -> Items -> Items
> icons (I PCT) (Items (I LF : is)) = Items is
> icons (I LF) (Items (I PCT : is)) = Items is
> icons i (Items is) = Items (i : is)

> instance Monoidal Items where
>   m0 = Items []
>   Items is <+> ii = foldr icons ii is

> class Itemize x where
>   itemize :: x -> Items

> instance Itemize Symbol where
>   itemize x = Items [I x]

> instance Itemize String where
>   itemize s = itemize <!> tokenize s

> instance Itemize (List Element) where
>   itemize es | (cs,is) <- f es = itemize cs <+> is where
>     f (Tip _) = ("",Items [I LF])
>     f (EC c :>: es) | (cs,is) <- f es = (c : cs,is)
>     f (EMark :>: es) = f es
>     f (EB SQUARE sdoc :>: es) | (cs,is) <- f es =
>       ("",Items [Block (Zip,sdoc)] <+> itemize cs <+> is)
>     f (EB ROUND sdoc :>: es) | (cs,is) <- f es =
>       ("",Items [Group (itemize sdoc)] <+> itemize cs <+> is)

> instance Itemize x => Itemize (Sized x) where
>   itemize (Sized _ x) = itemize x

> instance Itemize (List x) => Itemize (Zip x) where
>   itemize z = itemize (z <>> nil)

> instance Itemize (List x) => Itemize (Cursor x) where
>   itemize (z :*: s) = itemize (z <>> s)

> instance Itemize Doc where
>   itemize (Doc ab he be) = itemize <!> ab <+> itemize he <+> itemize <!> be

> instance Itemize EditDoc where
>   itemize = itemize . snd . repeatedly outDoc 

> parseItemize :: Itemize y => Parser Maybe Item x -> y -> Maybe x
> parseItemize p y | Items is <- itemize y = reading p is


******************************************************************************
Parser pieces
******************************************************************************

> iInt :: Parser Maybe Item Int
> iInt = pT isi
>   where isi (I (INT i)) = return i
>         isi _ = m0

> instance ParseFrom Maybe Symbol Item () where
>   pF s = pT iss
>     where iss (I x) = ensure (s == x)
>           iss _ = m0

> iLFs :: Parser Maybe Item ()
> iLFs = pF LF </> (iSkip)

> iSkip :: Parser Maybe Item ()
> iSkip = iLFs <+> pE

> iP :: Parser Maybe Item x -> Parser Maybe Item x
> iP p = p </> iSkip

> iPP :: Parser Maybe Item x -> Parser Maybe Item x
> iPP p = iSkip <\> iP p

> iGroup :: Parser Maybe Item x -> Parser Maybe Item x
> iGroup p = pT f where
>   f (Group (Items is)) =
>     do (x,[]) <- un (iPP p) is
>        return x
>   f _ = m0


******************************************************************************
Lexical has a parser
******************************************************************************

> instance Parse Maybe Item Lexical where
>   blah = pT blk where
>     blk (Block x) = eta x
>     blk _         = m0


******************************************************************************
From String to Maybe [Item]
******************************************************************************

> lexer :: String -> Maybe [Item]
> lexer = up (un . itemize) . getDoc <.> chunk
