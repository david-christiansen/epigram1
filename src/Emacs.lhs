******************************************************************************
**********                                                          **********
**********     Emacs.lhs -- technology for talking to emacs         **********
**********                                                          **********
******************************************************************************

> module Emacs where

> import Utils
> import Name
> import ObjKind
> import Category

> data Emacs
>   = EA String
>   | EI Int
>   | ES String
>   | EL [Emacs]
>   | ELN [Emacs]
>   | EP [Emacs]
>   | EQT Emacs
>   | ED Emacs Emacs

> infix ~$

> (~$) :: String -> [Emacs] -> Emacs
> f ~$ as = EL (EA f : as)

> instance Show Emacs where
>   show (EA s) = s
>   show (EI i) = show i
>   show (ES s) = show s
>   show (EL []) = "()"
>   show (EL (e : es)) = "(" ++ show e ++ rest es
>     where rest [] = ")"
>           rest (x : xs) = " " ++ show x ++ rest xs
>   show (ELN es) = show (EL es) ++ "\n"
>   show (EP xs) = "(progn\n" ++ stuff xs ++ ")\n"
>     where stuff [] = ""
>           stuff (x : xs) = show x ++ "\n" ++ stuff xs
>   show (EQT e) = "'" ++ show e
>   show (ED a d) = "(" ++ show a ++ "." ++ show d ++ ")"

> class EMACS x where
>   emacs :: x -> Emacs

> instance EMACS Emacs where
>   emacs = id

> instance (EMACS x,EMACS y) => EMACS (x,y) where
>   emacs (x,y) = EP [emacs x,emacs y]

> emacsDOIT :: Emacs -> IO ()
> emacsDOIT x
>   = do putStrLn (show x)
>        putStrLn ";;; DOIT"

> horace :: EMACS x => x -> Emacs
> horace x = "horace" ~$ ["sneakily" ~$ [emacs x]]

> epigram :: EMACS x => x -> Emacs
> epigram x = "epigram" ~$ ["sneakily" ~$ [emacs x]]

> instance EMACS x => EMACS (Maybe x) where
>   emacs Nothing  = EL []
>   emacs (Just x) = emacs x


************************************************************************

> data Badness
>   = OK | Warning | Error deriving (Eq,Enum,Ord)

> instance Show Badness where
>   show OK = ""
>   show Warning = "Y"
>   show Error = "S"

> data Colour
>   = Black | Blue | Red | Green | Purple | Orange deriving (Eq,Enum)

> instance Show Colour where
>   show Black = ""
>   show Blue = "B"
>   show Red = "R"
>   show Green = "G"
>   show Purple = "P"
>   show Orange = "O"

> data Focus
>   = Background | Foreground deriving (Eq,Enum,Ord)

> instance Show Focus where
>   show Background = ""
>   show Foreground = "F"

> data Face = Face Focus Badness Colour deriving Eq

> fWarning :: Face
> fWarning = Face m0 Warning m0

> fError :: Face
> fError = Face m0 Error m0

> fForeground :: Face
> fForeground = Face Foreground m0 m0

> instance Monoidal Badness where
>   m0 = OK
>   (<+>) = max

> instance Monoidal Colour where
>   m0 = Black
>   c <+> Black = c
>   _ <+> c     = c

> instance Monoidal Focus where
>   m0 = Background
>   (<+>) = max

> instance Monoidal Face where
>   m0 = Face m0 m0 m0
>   Face f1 b1 c1 <+> Face f2 b2 c2 = Face (f1 <+> f2) (b1 <+> b2) (c1 <+> c2)

> bugFace :: Face
> bugFace = Face Background Error Orange

> instance Show Face where
>   show (Face f b c) = "E" ++ show f ++ show b ++ show c

> makeFace :: Face -> [Emacs]
> makeFace face
>   | fc <- foreCol face
>   , bc <- backCol face
>   = case bc of
>       "" -> base fc
>       bc -> base fc ++ ["set-face-background" ~$ [name,ES bc]]
>   where
>     base fc =
>       ["copy-face" ~$ [EQT (EA "default"),name],
>        "set-face-foreground" ~$ [name,ES (foreCol face)]]
>     name = EQT (EA (show face))
>     backCol (Face Background OK      _) = ""
>     backCol (Face Background Warning _) = "palegoldenrod"
>     backCol (Face Background Error   _) = "goldenrod"
>     backCol (Face Foreground OK      _) = "palegreen"
>     backCol (Face Foreground Warning _) = "yellow"
>     backCol (Face Foreground Error   _) = "darkgoldenrod"
>     foreCol (Face _ _ Black)            = "black"
>     foreCol (Face _ _ Blue)             = "darkblue"
>     foreCol (Face _ _ Red)              = "red"
>     foreCol (Face _ _ Green)            = "darkgreen"
>     foreCol (Face _ _ Purple)           = "purple"
>     foreCol (Face _ _ Orange)           = "darkorange"

> makeFaces :: Emacs
> makeFaces = EP . concat $
>   [makeFace (Face f b c)
>     | f <- [Background ..]
>     , b <- [OK ..]
>     , c <- [Black ..]
>   ]

> kindFace :: ObjKind -> Face
> kindFace (ObjDecl TypeCon)     = Face Background OK Blue
> kindFace (ObjDecl (DataCon _)) = Face Background OK Red
> kindFace  ObjDefn              = Face Background OK Green
> kindFace  ObjRec               = Face Background OK Green
> kindFace  ObjBad               = Face Background OK Black
> kindFace  _                    = Face Background OK Purple

> data TextElt
>   = Text String Face
>   | Space Int Face deriving Show

> tcons :: TextElt -> [TextElt] -> [TextElt]
> tcons (Space 0 _) ts = ts
> tcons (Space i f) (Space j g : ts) | f == g = Space (i + j) f : ts
> tcons (Text y g) (Space i f : ts)
>   | g == f && not (f == m0 && i > 5)
>   = tcons (Text (y ++ copies i ' ') f) ts
> tcons (Text x f) (Text y g : ts) | f == g = Text (x ++ y) f : ts
> tcons t ts = t : ts

> instance Monoidal [TextElt] where
>   m0 = []
>   xs <+> ys = foldr tcons ys xs

> instance EMACS TextElt where
>   emacs (Space i face) | face == m0 = EI i
>   emacs (Space i face) = ED (ES (take i spaces)) (EA (show face))
>   emacs (Text s face) | face == m0 = ES s
>   emacs (Text s face) = ED (ES s) (EA (show face))

> instance EMACS [TextElt] where
>   emacs xs = EL (EA "bung-out-line" : [EQT (EL (fmap emacs xs))])

> instance EMACS (Int,[[TextElt]]) where
>   emacs (i,xxs) = "bols" ~$ [EI i,EQT (EL (fmap (ELN . fmap emacs) xxs))]

> blank :: Int -> Face -> [TextElt]
> blank 0 f = []
> blank i f = [Space i f]

> text :: String -> Face -> [TextElt]
> text s f = [Text s f]


******************************************************************************
Event-related stuff
******************************************************************************

> data Event
>   = SelectEvent LName (Int,Int)
>   | ReselectEvent (Int,Int)
>   | DeselectEvent
>   | DoubleClickEvent
>   | CharEvent Char
>   | HoraceEvent LName
>   | SpecialKeyEvent SpecialKey [ModifierKey]
>   | StringEvent String
>   | RefreshEvent Int
>   | ActionEvent String
>   deriving (Show,Eq)

> data ModifierKey = Shift | Ctrl | Alt deriving (Show,Eq)

> modifierKey :: String -> [ModifierKey]
> modifierKey "shift" = [Shift]
> modifierKey "control" = [Ctrl]
> modifierKey "meta" = [Alt]
> modifierKey _ = []

> data SpecialKey
>   = ReturnKey
>   | EscapeKey
>   | TabKey
>   | BackspaceKey
>   | DeleteKey
>   | UpKey
>   | DownKey
>   | LeftKey
>   | RightKey
>   | ModChar Char
>   deriving (Show,Eq)

> specialKey :: String -> Maybe SpecialKey
> specialKey "return" = return ReturnKey
> specialKey "escape" = return EscapeKey
> specialKey "tab" = return TabKey
> specialKey "backspace" = return BackspaceKey
> specialKey "delete" = return DeleteKey
> specialKey "up" = return UpKey
> specialKey "down" = return DownKey
> specialKey "left" = return LeftKey
> specialKey "right" = return RightKey
> specialKey _ = m0

