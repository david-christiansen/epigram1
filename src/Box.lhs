******************************************************************************
**********                                                          **********
**********     Box.lhs --- box display gizmos                       **********
**********                                                          **********
******************************************************************************

> module Box where

> import Category
> import Monadics
> import Logic
> import Utils
> import Zip
> import Doc
> import Emacs
> import Name
> import ObjKind

> -- import Debug.Trace

******************************************************************************
Boxy structures
******************************************************************************

A Boxy structure is a rectangular region with a horizontal line across it.
It has a width, a height above the line, and a depth below the line.
Characters hang from the line

Invariants: all three are non-negative; the height is only positive if
the depth is positive also.

> infixr 3 |#|
> infixr 2 ^#^
> infixr 2 -#-
> class Boxy x where
>   box0 :: x
>   isBox0 :: x -> Bool
>   (|#|) :: BinOp x  -- horizontal composition, joining the lines
>   (^#^) :: BinOp x  -- second, with first on top (aka stacking)
>   (-#-) :: BinOp x  -- first, with second below  (aka hanging)


******************************************************************************
Box dimensions are Boxy
******************************************************************************

> instance Boxy WHD where
>   box0 = (0,(0,0))
>   isBox0 = (box0 ==)
>   (w1,(h1,d1)) |#| (w2,(h2,d2)) = (w1 + w2,(max h1 h2,max d1 d2))
>   (w1,(h1,d1)) ^#^ (w2,(h2,d2)) = (max w1 w2,(h1 + d1 + h2,d2))
>   (w1,(h1,d1)) -#- (w2,(h2,d2)) = (max w1 w2,(h1,d1 + h2 + d2))


******************************************************************************
Direction
******************************************************************************

> data Direction = Rightwards | Downwards deriving (Show,Eq)

> instance Boxy Direction where
>   box0 = Rightwards
>   isBox0 = (box0 ==)
>   _ |#| d = d
>   _ ^#^ _ = Downwards
>   _ -#- _ = Downwards


******************************************************************************
Box and Stuff
******************************************************************************

> data Box x
>   = Box {bSize :: WHD, bDir :: Direction, bStuff :: Stuff x}
>   deriving Show

> data Stuff x
>   = Stuff x
>   | Blank
>   | ReFace Face (Stuff x)
>   | DeFace (Stuff x)
>   | Tag LName (Stuff x)
>   | ReAlign (Box x)
>   | Box x :|#|: Box x   -- subboxes presumed to fit perfectly
>   | Box x :^#^: Box x
>   | Box x :-#-: Box x
>   | Glyph Glyph
>   deriving Show

> data Glyph
>   = GOpen Bracket | GClose Bracket | GRule | GLBrace | GRBrace
>   deriving Show

(base-funnel "(Box x)")

> instance Fun f => Funnel f (Box x) (f (Box x)) where
>   fun    = eta
>   funnel = id

> instance Wide (Box x) where
>   width b | (w,_) <- bSize b = w

> instance Tall (Box x) where
>   tallness b | (_,(h,d)) <- bSize b = h + d



******************************************************************************
Box algebra
******************************************************************************

Here, in establishing Boxy (Box x), we must maintain the invariant that
subboxes fit perfectly, by padding with blank boxes where necessary.

> bBlank :: WHD -> Box x
> bBlank s = Box s box0 Blank

> padHD :: WHD -> Box x -> Box x
> padHD (_,ehd@(eh,ed)) b@(Box (w,(h,d)) dir _)
>   = case (h < eh,d < ed) of
>       (False,False) -> b
>       (True ,False) -> Box (w,ehd) dir (bBlank (w,(0,eh - h)) :^#^: b)
>       (False,True ) -> Box (w,ehd) dir (b :-#-: bBlank (w,(0,ed - d)))
>       (True ,True ) ->
>         Box (w,ehd) dir (bBlank (w,(0,eh - h)) :^#^: 
>                          Box (w,(h,ed)) dir (b :-#-: bBlank (w,(0,ed - d))))

> padW :: WHD -> Box x -> Box x
> padW (ew,_) b@(Box (w,hd) dir _)
>   | w < ew = Box (ew,hd) dir (b :|#|: bBlank (ew - w,hd))
>   | otherwise = b

> instance Boxy (Box x) where
>   box0 = bBlank box0
>   isBox0 = isBox0 . bSize
>   b1@(Box s1 d1 _) |#| b2@(Box s2 d2 _)
>     | whd <- s1 |#| s2
>     = Box whd (d1 |#| d2) (padHD whd b1 :|#|: padHD whd b2)
>   b1@(Box s1 d1 _) ^#^ b2@(Box s2 d2 _)
>     | whd <- s1 ^#^ s2
>     = Box whd (d1 ^#^ d2) (padW whd b1 :^#^: padW whd b2)
>   b1@(Box s1 d1 _) -#- b2@(Box s2 d2 _)
>     | whd <- s1 -#- s2
>     = Box whd (d1 -#- d2) (padW whd b1 :-#-: padW whd b2)

> instance Monoidal (Box x) where  -- wrt vertical hanging
>   m0 = box0
>   (<+>) = (-#-)



******************************************************************************
Refacing for boxes
******************************************************************************

> bPush :: (Stuff x -> Stuff x) -> Box x -> Box x
> bPush f (Box s d x) = Box s d (f x)



******************************************************************************
Rendering boxes
******************************************************************************

> boxText :: Face -> Box String -> Cursor [TextElt]
> boxText f (Box _ _ (Stuff s)) = Zip :*: text s f :>: nil
> boxText f (Box (w,(h,d)) _ Blank)
>   = zCrop h (eta (blank w f)) :*: lCrop d (eta (blank w f))
> boxText f (Box s d (ReFace g x)) = boxText (f <+> g) (Box s d x)
> boxText _ (Box s d (DeFace x)) = boxText m0 (Box s d x)
> boxText f (Box s d (Tag nom x)) = boxText f (Box s d x)
> boxText f (Box (_,(h,_)) _ (ReAlign b))
>   | zz :*: ss <- boxText f b
>   = shift h (Zip :*: (zz <>> ss)) where
>     shift i (zz :*: s :>: ss) | i > 0 = shift (i - 1) (zz :<: s :*: ss)
>     shift _ zs = zs
> boxText f (Box s _ (b1 :|#|: b2))
>   = fun (<+>) (boxText f b1) (boxText f b2)
> boxText f (Box s _ (b1 :^#^: b2))
>   | zz1 :*: ss1 <- boxText f b1, zz2 :*: ss2 <- boxText f b2
>   = ((zz1 <>< ss1) <+> zz2) :*: ss2
> boxText f (Box s _ (b1 :-#-: b2))
>   | zz1 :*: ss1 <- boxText f b1, zz2 :*: ss2 <- boxText f b2
>   = zz1 :*: (ss1 <+> (zz2 <>> ss2))
> boxText f (Box (_,(0,d)) _ (Glyph (GOpen br)))
>   = Zip :*: text (show (Open br)) f
>         :>: lCrop (d - 1) (eta (text (show Tab) f))
> boxText f (Box (_,(h,d)) _ (Glyph (GOpen br)))
>   = ((Zip :<: text (show (Open br)) f)
>      <+> zCrop (h - 1) (eta (text (show Tab) f)))
>     :*: lCrop d (eta (text (show Tab) f))
> boxText f (Box (_,(h,d)) _ (Glyph (GClose br)))
>   = zCrop h (eta (text (show Tab) f)) :*:
>     lCrop (d - 1) (eta (text (show Tab) f)) <+>
>     text (show (Close br)) f :>: nil
> boxText f (Box (w,_) _ (Glyph GRule))
>   = Zip :*: text (copies w '-') f :>: nil
> boxText f (Box (w,(h,d)) _ (Glyph GLBrace))
>   | h > 0 = (Zip :<: br <+> zCrop (h - 1) (eta bl)) :*: lCrop d (eta bl)
>   | otherwise = Zip :*: br :>: lCrop (d - 1) (eta bl)
>   where br = text "{" f <+> blank (w - 1) f
>         bl = blank w f
> boxText f (Box (w,(h,d)) _ (Glyph GRBrace))
>   | d > 0 = zCrop h (eta bl) :*: (lCrop (d - 1) (eta bl) <+> br :>: nil)
>   | otherwise = zCrop (h - 1) (eta bl) :<: br :*: nil
>   where br = blank (w - 1) f <+> text "}" f
>         bl = blank w f



******************************************************************************
Useful box combinators
******************************************************************************

> bBracket :: Bracket -> Box x -> Box x
> bBracket br b@(Box (_,(h,d)) _ _)
>   = lbr |#| b |#| rbr where
>     lbr = Box (1,(h,max 1 d)) Rightwards (Glyph (GOpen br))
>     rbr = Box (1,(h,max 1 d)) Rightwards (Glyph (GClose br))

> bBrace :: Box x -> Box x
> bBrace b@(Box s _ _) =
>   case s of
>     (_,(0,0)) -> lbrace (0,1) |#| rbrace
>     (_,hd) -> lbrace hd |#| bBlank (1,(0,0)) |#| b -#- rbrace
>   where
>     rbrace = Box (1,(0,1)) Rightwards (Glyph GRBrace)
>     lbrace hd = Box (1,hd) Rightwards (Glyph GLBrace)

> bCentre :: Int -> Box x -> Box x
> bCentre w' b
>   | (w,_) <- bSize b, g <- div (w' - w) 2, p <- mod (w' - w) 2
>   = if w > w' then b else bBlank (g,(0,0)) |#| b |#| bBlank (g + p,(0,0))

> bRule :: Box x -> Box x -> Box x
> bRule hb cb
>   | (hw,_) <- bSize hb, (cw,_) <- bSize cb, w <- 2 + max hw cw
>   = (bCentre w hb ^#^ Box (w,(0,1)) Downwards (Glyph GRule)) -#- bCentre w cb

> bReAlign :: WHD -> Box x -> Box x
> bReAlign whd b@(Box _ d _) = Box whd d (ReAlign b)


******************************************************************************
Boxings
******************************************************************************

We work with streams of boxes which satisfy the invariants that
  (1) each successive box is strictly thinner and strictly taller
  (2) for each height, the box is the thinnest available

> type BoxS = Box String

> newtype Boxings = Bxs [BoxS] deriving Show

(base-funnel "Boxings")

> instance Fun f => Funnel f Boxings (f Boxings) where
>   fun    = eta
>   funnel = id

 instance ReFace Boxings where
   reFace f (Bxs x) = Bxs (reFace f x)

------------------------------------------------------------------------------

> instance Unpack Boxings [BoxS] where
>   un (Bxs x) = x
>   nu = Bxs

> pickABox :: Int -> Boxings -> BoxS
> pickABox _ (Bxs [])  = box0
> pickABox x (Bxs [b]) = b
> pickABox x (Bxs (b : bs))
>   | (w,_) <- bSize b, w <= x = b
>   | otherwise = pickABox x (Bxs bs)


------------------------------------------------------------------------------
We shall need to merge such streams, filtering out the poorer candidates.

> instance Monoidal Boxings where
>   m0 = Bxs []
>   Bxs bs1 <+> Bxs bs2 = Bxs (mergeBoxings Nothing bs1 bs2) where
>     mergeBoxings (Just m) (b : bs1) bs2
>       | (w,_) <- bSize b, m <= w = mergeBoxings (Just m) bs1 bs2
>     mergeBoxings (Just m) bs1 (b : bs2)
>       | (w,_) <- bSize b, m <= w = mergeBoxings (Just m) bs1 bs2
>     mergeBoxings _ [] bs = bs
>     mergeBoxings _ bs [] = bs
>     mergeBoxings _ bbs1@(b1 : bs1) bbs2@(b2 : bs2)
>       | hd1 < hd2 = b1 : mergeBoxings (Just w1) bs1 bbs2
>       | hd1 > hd2 = b2 : mergeBoxings (Just w2) bbs1 bs2
>       |  w1 < w2  = b1 : mergeBoxings (Just w1) bs1 bbs2
>       | otherwise = b2 : mergeBoxings (Just w2) bbs1 bs2
>         where
>           (w1,(h1,d1)) = bSize b1
>           hd1 = h1 + d1
>           (w2,(h2,d2)) = bSize b2
>           hd2 = h2 + d2


------------------------------------------------------------------------------
We shall also need to jack up box operations to boxing operations.

> class BoxJack s t | s -> t, t -> s where
>   jack :: s -> t

> instance BoxJack BoxS Boxings where
>   jack b = Bxs [b]

> instance (Monoidal t,BoxJack s t) => BoxJack (BoxS -> s) (Boxings -> t) where
>   jack f (Bxs bs) = (jack . f) <!> bs

> instance Boxy Boxings where
>   box0  = jack box0
>   isBox0 (Bxs bs) = un ((Might . isBox0) <!> bs)
>   (|#|) = jack (|#|)
>   (^#^) = jack (^#^)
>   (-#-) = jack (-#-)


******************************************************************************
Clicking, etc
******************************************************************************

Note that clicking relies on the fact that subboxes fit perfectly.
Coordinates are box coordinates (ie 0 is h lines down).

> clickTag :: (Int,Int) -> Bool -> Box x -> Rightmost (LName,(Int,Int))
> clickTag (x,y) nobel (Box (w,(h,d)) _ _)
>   | x < 0 || x >= w || y < -h || (y >= d && nobel)
>   = m0
> clickTag xy@(x,y) nobel (Box (w,(h,d)) _ z) = clk z where
>   clk (Tag nom z) = eta (nom,xy) <+> clk z
>   clk (ReFace _ z) = clk z
>   clk (DeFace z) = clk z
>   clk (ReAlign b@(Box (_,(h',_)) _ _)) = clickTag (x,h + y - h') nobel b
>   clk (b1 :|#|: b2) | (w,_) <- bSize b1
>     = clickTag xy nobel b1 <+> clickTag (x - w,y) nobel b2
>   clk (b1 :-#-: b2)
>     | (_,(h1,d1)) <- bSize b1
>     , (_,(h2,d2)) <- bSize b2
>     = clickTag xy True b1 <+> clickTag (x, y - d1 - h2) nobel b2
>   clk (b1 :^#^: b2)
>     | (_,(h1,d1)) <- bSize b1
>     , (_,(h2,d2)) <- bSize b2
>     = clickTag (x,y + h2 + d1) True b1 <+> clickTag xy nobel b2
>   clk _ = m0

> tagPos :: LName -> Box x -> Maybe (Int,Int)
> tagPos nom = tpb where
>   tpb (Box (_,(h,_)) _ z) = tp z where
>     slip h' = up ((0 :: Int,h' - h) <+>)
>     tp (Tag nam z)
>       | nam == nom = return m0
>       | nam < nom  = tp z
>       | otherwise  = Nothing
>     tp (ReFace _ z) = tp z
>     tp (DeFace z) = tp z
>     tp (ReAlign (Box (_,(h',_)) _ z))
>       = slip h' (tp z)
>     tp (b1 :|#|: b2) | (w,_) <- bSize b1
>       = tpb b1 <+> up ((w,0 :: Int) <+>) (tpb b2)
>     tp (b1 :^#^: b2)
>       | (_,(_,d1)) <- bSize b1
>       , (_,(h2,_)) <- bSize b2
>       = up ((0 :: Int,0 - d1 - h2) <+>) (tpb b1) <+> tpb b2
>     tp (b1 :-#-: b2)
>       | (_,(_,d1)) <- bSize b1
>       , (_,(h2,_)) <- bSize b2
>       = tpb b1 <+> up ((0 :: Int,d1 + h2) <+>) (tpb b2)
>     tp _ = Nothing


******************************************************************************
Standard boxing
******************************************************************************

> class Boxes x where
>   box :: x -> Boxings

> infixr 3 |?|
> infixr 2 ^?^
> infixr 2 -?-

> (|?|) :: (Boxes x,Boxes y) => x -> y -> Boxings
> x |?| y = box x |#| box y

> (^?^) :: (Boxes x,Boxes y) => x -> y -> Boxings
> x ^?^ y = box x ^#^ box y

> (-?-) :: (Boxes x,Boxes y) => x -> y -> Boxings
> x -?- y = box x -#- box y


> instance Boxes () where
>   box _ = box0

> instance Boxes x => Boxes (K x y) where
>   box (K x) = box x

> instance Boxes x => Boxes (Id x) where
>   box (Id x) = box x

> instance Boxes (f (g x)) => Boxes (Comp f g x) where
>   box (Comp x) = box x

> instance Boxes Boxings where
>   box = id

> instance Boxes String where -- no control chars
>   box s = Bxs [Box (length s,(0,1)) Rightwards (Stuff s)]

> instance Boxes (ObjKind,UName) where
>   box (ok,UN s) = faceB (kindFace ok) (box s)

> instance Boxes Symbol where
>   box = box . show


******************************************************************************
Boxing Docs
******************************************************************************

> instance Boxes Body where
>   box (Right s) = box s
>   box (Left i) = jack (bBlank (i,(0,1)))

> instance Boxes (Sized (List Element)) where
>   box (Sized _ es) | (x,b) <- f es = x |?| b where
>     f :: List Element -> (Body,Boxings)
>     f (Tip _) = (Left 0,box0)
>     f (EC c :>: es) | (x,b) <- f es = (bcons c x,b)
>     f (EMark :>: es) = f es -- not forever
>     f (EB br sdoc :>: es) | (x,b) <- f es =
>        (Left 0,jack (bBracket br) (box sdoc) |?| x |?| b)

> instance Boxes (Sized (Zip Element)) where
>   box (Sized whd ez) = box (Sized whd (ez <>> nil))

> instance Boxes (Sized (Cursor Element)) where
>   box (Sized whd (ez :*: es)) = box (Sized whd (ez <>> es))

> instance Boxes (Sized Doc) where
>   box (Sized whd (Doc ab he be)) = jack (bReAlign whd) $
>       flatB (-#-) ab -#- box he -#- flatB (-#-) be

> instance Boxes Lexical where
>   box = jack (bBracket SQUARE . bPush DeFace) . box . snd . repeatedly outDoc


******************************************************************************
Combinators
******************************************************************************

> faceB :: Face -> Boxings -> Boxings
> faceB f = jack (bPush (ReFace f))

> tagB :: LName -> Boxings -> Boxings
> tagB nom = jack (bPush (Tag nom))

> gapB :: Int -> Boxings
> gapB w = Bxs [bBlank (w,(0,0))]

> _B :: Boxings
> _B = gapB 1

> __B :: Boxings
> __B = gapB 2

> lineB :: Boxings
> lineB = Bxs [bBlank (0,(0,1))]

> horvB :: Boxings -> Maybe (Boxings,Boxings,Boxings) -> (Boxings,Boxings) ->
>          Boxings -> Boxings -> Boxings
> horvB = bhorvB

 horvB gap (skip,dent) (Bxs bs1) (Bxs bs2) = horv <!> bs1 <!> bs2
   where
     horv b1 b2 | bb1 <- jack b1, bb2 <- jack b2
       = when (bDir b1 == Rightwards) (bb1 |#| gap |#| bb2) <+>
         (bb1 -#- skip -#- dent |#| bb2)

> bhorvB :: Boxings -> Maybe (Boxings,Boxings,Boxings) -> (Boxings,Boxings) ->
>           Boxings -> Boxings -> Boxings
> bhorvB gap (Just (tip,skip,dent)) (hop,bop)
>   (Bxs bs1) (Bxs bs2) = horv <!> bs1 <!> bs2
>   where
>     horv b1 b2 | bb1 <- jack b1, bb2 <- jack b2
>       = when (bDir b1 == Rightwards)
>           (when (bDir b2 == Rightwards)
>              (bb1 |#| gap |#| bb2)
>            <+>
>            (bb1 |#| tip -#- skip -#- dent |#| bb2))
>         <+>
>         (bb1 -#- hop -#- bop |#| bb2)
> bhorvB gap Nothing (hop,bop)
>   (Bxs bs1) (Bxs bs2) = horv <!> bs1 <!> bs2
>   where
>     horv b1 b2 | bb1 <- jack b1, bb2 <- jack b2
>       = when (bDir b1 == Rightwards && bDir b2 == Rightwards)
>              (bb1 |#| gap |#| bb2)
>         <+>
>         (bb1 -#- hop -#- bop |#| bb2)

> seqB :: (Boxings -> Boxings -> Boxings) -> [Boxings] -> Boxings
> seqB f [] = box0
> seqB f bxss = foldl1 f bxss

> flatB :: (Functorial g, Boxes x) => (Boxings -> Boxings -> Boxings) ->
>                                     g x -> Boxings
> flatB c gx = action (c . box) gx box0

> zipB :: (Boxings -> Boxings -> Boxings) -> Zip Boxings -> Boxings
> zipB f = zPost f box0

> skipSep :: (Boxings -> Boxings -> Boxings) -> Boxings -> Boxings -> Boxings
> skipSep f x y
>   | isBox0 x  = y
>   | isBox0 y  = x
>   | otherwise = f x y

> sepB :: Boxings -> Boxings -> Boxings -> Boxings
> sepB sep x y = x |#| sep |#| y

> vertList :: [Boxings] -> Boxings
> vertList = seqB (sepB (_B |?| LF |?| __B)) <+> seqB (-#-)


******************************************************************************
Displaying
******************************************************************************

> emacsDelete :: BoxS -> IO ()
> emacsDelete b | (_,(h,d)) <- bSize b =
>   emacsDOIT . epigram . emacs $ ("kill-line" ~$ [EI (h + d)])

> emacsInsert :: BoxS -> IO ()
> emacsInsert b = emacsDOIT . epigram $ emacs (0 :: Int,un (boxText m0 b))

> emacsReplace :: BoxS -> BoxS -> IO ()
> emacsReplace b b' | (_,(h,d)) <- bSize b = chunk (h + d) (un (boxText m0 b'))
>   where
>     gulp :: Int
>     gulp = 5
>     chunk :: Int -> [[TextElt]] -> IO ()
>     chunk 0 [] = return ()
>     chunk i ess | (ess1,ess2) <- glom gulp ess = do
>       emacsDOIT . epigram $ emacs (min i gulp,ess1)
>       chunk (max 0 (i - gulp)) ess2
>     glom :: Int -> [a] -> ([a],[a])
>     glom _ [] = ([],[])
>     glom 0 xs = ([],xs)
>     glom n (x : xs) | (ys,zs) <- glom (n - 1) xs = (x : ys,zs)

> data RenderOp = RenIns | RenDel | RenSkip deriving Eq

 instance EMACS (RenderOp,BoxS) where
   emacs (RenIns,b)  = emacs (un (boxText m0 b))
   emacs (RenDel,b)  | (_,(h,d)) <- bSize b = "kill-line" ~$ [EI (h + d)]
   emacs (RenSkip,b) | (_,(h,d)) <- bSize b = "next-line" ~$ [EI (h + d)]

> type Render = State Id (Zip (RenderOp,BoxS))

> type NomBox = (String,Int) :=: BoxS

> rendo :: RenderOp -> NomBox -> Render NomBox
> rendo r sib@(_ :=: b) = tweak (`rsnoc` (r,b)) <\> eta sib where
>   rsnoc (rbz :<: (r1,b1)) (r2,b2) | r1 == r2 = rbz :<: (r1,b1 <+> b2)
>   rsnoc rbz rb = rbz :<: rb

> data DispMod = DOld | DMod | DNew

> reNomBox :: List NomBox -> List (DispMod,NomBox)
>              -> Render (List NomBox)
> reNomBox (sib :>: sibs) ((DOld,sib') :>: msibs) | sib == sib'
>   = fun (:>:) (rendo RenSkip sib) (reNomBox sibs msibs)
> reNomBox (sib :>: sibs) ((DMod,sib') :>: msibs) | sib == sib'
>   = rendo RenDel sib <\> reNomBox sibs ((DNew,sib') :>: msibs)
> reNomBox sibs ((DNew,sib) :>: msibs)
>   = fun (:>:) (rendo RenIns sib) (reNomBox sibs msibs)
> reNomBox (sib :>: sibs) msibs
>   = rendo RenDel sib <\> reNomBox sibs msibs
> reNomBox (Tip _) ((_,sib) :>: msibs)
>   = fun (:>:) (rendo RenIns sib) (reNomBox nil msibs)
> reNomBox (Tip _) (Tip _) = return nil

