******************************************************************************
**********                                                          **********
**********     EditDoc.lhs   Editing Epigram documents              **********
**********                                                          **********
******************************************************************************

> module EditDoc where

> import Utils
> import Category
> import Monadics
> import Logic
> import Zip
> import Parser
> import Logic
> import Data.Array
> import Doc
> import Igor
> import Box
> import Emacs

> -- import Debug.Trace

> data EditEffect = NoEdit | MoveEdit EditDoc | ChangeEdit EditDoc

> eDocXY :: EditDoc -> (Int,Int)
> eDocXY (dz,sdoc) = wrap dz (sXY sdoc) where
>   sXY (Sized (_,(dh,_)) (Doc ab (Sized (_,(h,_)) (ez :*: _)) _)) =
>     (width <!> ez,tallness ab + h - dh)
>   wrap Zip xy = xy
>   wrap (dz :<:
>         (Sized (_,(bh,_)) (Doc ab (Sized (_,(lh,_)) (ez :*: _)) _),_))
>        (x,y) =
>     wrap dz (1 + width <!> ez + x,tallness ab + lh + y - bh)

> clickEDoc :: (Int,Int) -> EditDoc -> EditDoc
> clickEDoc (x,y) edoc = vfind (0,-doch) uoedoc where
>   uoedoc@(_,Sized (_,(doch,_)) _) =
>     repeatedly upDoc . repeatedly outDoc $ edoc where
>   vfind (x0,y0) edoc0@(_,Sized _ (Doc _ he _))
>     | y >= y1 , Just edoc1 <- downDoc edoc0
>     = vfind (x0,y1) edoc1
>     | otherwise
>     = hfind (x0,y0) (repeatedly leftDoc edoc0)
>     where y1 = y0 + tallness he
>   hfind (x0,y0) edoc0@(_,Sized _ (Doc _ (Sized (_,(h,_)) (_ :*: e :>: _)) _))
>     | x >= x1, Just edoc1 <- rightDoc edoc0
>     = hfind (x1,y0) edoc1
>     | x > x0, Just edocI <- inDoc edoc0
>     , EB _ (Sized (_,(h',_)) _) <- e
>     = vfind (x0 + 1,y0 + h - h') (repeatedly upDoc edocI)
>     | otherwise
>     = edoc0
>     where x1 = x0 + width e
>   hfind _ edoc = edoc

> class Size x where
>   size :: x -> WHD

> instance Size Element where
>   size (EC _) = (1,(0,1))
>   size EMark  = box0
>   size (EB _ sdoc) = (2,(0,1)) |#| size sdoc

> instance Size (Sized x) where
>   size (Sized whd _) = whd

> instance Size DocLayer where
>   size (d,_) = size d

> hsize :: (Functorial g,Size x) => g x -> WHD
> hsize gx = action f gx (0,(0,1)) where f x s = size x |#| s

> vsize :: (Functorial g,Size x) => g x -> WHD
> vsize gx = action f gx box0 where f x s = size x -#- s

> recalibrateEDoc :: EditDoc -> EditDoc
> recalibrateEDoc (dz,Sized (_,(h,_)) doc) =
>   let sdoc' = szDoc h (0,(0,1)) doc
>   in  (szLayers (size sdoc') dz,sdoc')
>   where
>     szLine :: WHD -> Cursor Element -> Sized (Cursor Element)
>     szLine whd ec@(ez :*: es) = Sized (whd |#| hsize ez |#| hsize es) ec
>     szDoc :: Int -> WHD -> Doc -> Sized Doc
>     szDoc h whd (Doc ab (Sized _ he) be) =
>       let he' = szLine whd he
>           (w0,(h0,d0)) = size he' -#- vsize ab -#- vsize be
>           doc' = Doc ab he' be
>       in  if h < h0 + d0 then Sized (w0,(h,h0 + d0 - h)) doc'
>              else Sized (w0,(h0 + d0 -1,1)) doc'
>     szLayer :: WHD -> DocLayer -> DocLayer
>     szLayer whd (Sized (_,(h,_)) doc,br)
>       = (szDoc h (whd |#| (2,(0,1))) doc,br)
>     szLayers :: WHD -> Zip DocLayer -> Zip DocLayer
>     szLayers _ Zip = Zip
>     szLayers whd (dz :<: d) =
>       let d' = szLayer whd d
>       in  szLayers (size d') dz :<: d'
>     sdoc' = szDoc h (0,(0,1)) doc

> eDocBS :: EditDoc -> EditEffect
> eDocBS (dz,Sized whd (Doc ab (Sized lwhd (ez :<: e :*: es)) be))
>   = ChangeEdit $ recalibrateEDoc
>      (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be))
> eDocBS (dz,Sized whd (Doc (ab :<: Sized awhd ez)
>                           (Sized lwhd (Zip :*: es))
>                           be))
>   = ChangeEdit $ recalibrateEDoc
>       (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be))
> eDocBS edoc = NoEdit

> eDocDEL :: EditDoc -> EditEffect
> eDocDEL (dz,Sized whd (Doc ab (Sized lwhd (ez :*: e :>: es)) be))
>   = ChangeEdit $ recalibrateEDoc
>       (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be))
> eDocDEL (dz,Sized whd (Doc ab
>                            (Sized lwhd (ez :*: Tip ()))
>                            (Sized bwhd es :>: be)))
>   = ChangeEdit $ recalibrateEDoc
>       (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be))
> eDocDEL edoc = NoEdit

> eDocLF :: EditDoc -> EditEffect
> eDocLF (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be)) =
>   ChangeEdit $ recalibrateEDoc
>     (dz,Sized whd (Doc (ab :<: Sized (hsize ez) ez)
>                        (Sized (hsize es) (Zip :*: es))
>                        be))

> eDocLEFT :: EditDoc -> EditEffect
> eDocLEFT edoc@(_,Sized _ (Doc _ (Sized _ (ez :<: EC _ :*: _)) _))
>   = MoveEdit (unjust (leftDoc edoc))
> eDocLEFT edoc@(_,Sized _ (Doc _
>                  (Sized _ (ez :<: EB _ (Sized (_,(h,_)) _) :*: _)) _)) =
>   MoveEdit $ rtend h (repeatedly upDoc (unjust $ (inDoc <.> leftDoc) edoc))
>     where
>       rtend y edoc@(dz,Sized _ (Doc _ he _))
>         | y >= hey, Just edoc' <- downDoc edoc = rtend (y - hey) edoc'
>         | otherwise = repeatedly rightDoc edoc
>         where hey = tallness he
> eDocLEFT edoc = MoveEdit (try (outDoc <+> upDoc) edoc)

> eDocRIGHT :: EditDoc -> EditEffect
> eDocRIGHT edoc@(_,Sized _ (Doc _ (Sized _ (ez :*: EC _ :>: _)) _))
>   = MoveEdit (unjust (rightDoc edoc))
> eDocRIGHT edoc@(_,Sized _ (Doc _
>                  (Sized _ (ez :*: EB _ (Sized (_,(h,_)) _) :>: _)) _)) =
>   MoveEdit $ ltend h (repeatedly upDoc (unjust $ inDoc edoc)) where
>     ltend y edoc@(dz,Sized _ (Doc _ he _))
>       | y >= hey, Just edoc' <- downDoc edoc = ltend (y - hey) edoc'
>       | otherwise = repeatedly leftDoc edoc
>       where hey = tallness he
> eDocRIGHT edoc = MoveEdit (try ((rightDoc <.> outDoc) <+> downDoc) edoc)

> eDocUP :: EditDoc -> EditEffect
> eDocUP edoc
>   | Just (x,edoc') <- goup 0 edoc
>   = MoveEdit $ goin x (repeatedly leftDoc edoc')
>   where
>     goup x edoc@(_,Sized _ (Doc (_ :<: _) (Sized _ (ez :*: _)) _))
>       = Just (x + width <!> ez,unjust (upDoc edoc))
>     goup x edoc@(_,Sized _ (Doc _ (Sized _ (ez :*: _)) _))
>       | Just edoc' <- outDoc edoc
>       = goup (x + 1 + width <!> ez) edoc'
>     goup _ _ = Nothing
>     goin 0 edoc = edoc
>     goin x edoc@(_,Sized _ (Doc _ (Sized _ (_ :*: e :>: _)) _))
>       | x' >= 0 = goin x' (unjust (rightDoc edoc))
>       | Just edoc' <- inDoc edoc
>       = goin (x - 1) (repeatedly leftDoc (repeatedly downDoc edoc'))
>       where x' = x - width e
>     goin _ edoc = edoc
> eDocUP edoc = NoEdit

> eDocDOWN :: EditDoc -> EditEffect
> eDocDOWN edoc
>   | Just (x,edoc') <- godn 0 edoc
>   = MoveEdit $ goin x (repeatedly leftDoc edoc')
>   where
>     godn x edoc@(_,Sized _ (Doc _ (Sized _ (ez :*: _)) (_ :>: _)))
>       = Just (x + width <!> ez,unjust (downDoc edoc))
>     godn x edoc@(_,Sized _ (Doc _ (Sized _ (ez :*: _)) _))
>       | Just edoc' <- outDoc edoc
>       = godn (x + 1 + width <!> ez) edoc'
>     godn _ _ = Nothing
>     goin 0 edoc = edoc
>     goin x edoc@(_,Sized _ (Doc _ (Sized _ (_ :*: e :>: _)) _))
>       | x' >= 0 = goin x' (unjust (rightDoc edoc))
>       | Just edoc' <- inDoc edoc
>       = goin (x - 1) (repeatedly leftDoc (repeatedly upDoc edoc'))
>       where x' = x - width e
>     goin _ edoc = edoc
> eDocDOWN edoc = NoEdit

> eDocC :: Char -> EditDoc -> EditEffect
> eDocC '(' (dz,sd) =
>   ChangeEdit $ recalibrateEDoc (dz :<: (sd,ROUND),Sized (0,(0,1)) emptyDoc)
> eDocC ')' edoc = MoveEdit $ try (rightDoc <.> outDoc) edoc
> eDocC '[' (dz,sd) =
>   ChangeEdit $ recalibrateEDoc (dz :<: (sd,SQUARE),Sized (0,(0,1)) emptyDoc)
> eDocC ']' edoc = MoveEdit $ try (rightDoc <.> outDoc) edoc
> eDocC '!' edoc
>   | Just edoc' <- inDoc edoc = MoveEdit edoc'
>   | Just edoc' <- rightDoc edoc = eDocC '!' edoc'
>   | Just edoc' <- outDoc edoc = MoveEdit edoc'
>   | otherwise = NoEdit
> eDocC '-' (dz,
>            Sized (w,(h,d)) (Doc ab
>                        (Sized lwhd (ez@(_ :<: EC '-' :<: EC '-') :*: es))
>                        be))
>   = ChangeEdit $ recalibrateEDoc
>       (dz,
>        Sized (w,(h',h + d - h'))
>          (Doc ab (Sized lwhd (ez :<: EC '-' :*: es)) be))
>       where h' = tallness ab
> eDocC c (dz,Sized whd (Doc ab (Sized lwhd (ez :*: es)) be))
>   | ' ' <= c && c <= '~'
>   = ChangeEdit $ recalibrateEDoc
>       (dz,Sized whd (Doc ab (Sized lwhd (ez :<: EC c :*: es)) be))
> eDocC c edoc = NoEdit

> eDocLoad :: String -> EditDoc -> EditEffect
> eDocLoad s (Zip,Sized (0,(0,1)) _)
>   | Just doc <- (getDoc <.> chunk) s
>   = ChangeEdit (repeatedly leftDoc (repeatedly upDoc (Zip,sizeDoc doc)))
> eDocLoad _ _ = NoEdit

> simpleKeys :: [(SpecialKey,EditDoc -> EditEffect)]
> simpleKeys =
>   [(BackspaceKey,eDocBS),
>    (DeleteKey,eDocDEL),
>    (ReturnKey,eDocLF),
>    (LeftKey,eDocLEFT),
>    (RightKey,eDocRIGHT),
>    (UpKey,eDocUP),
>    (DownKey,eDocDOWN)]

> eDocEvent :: Event -> EditDoc -> EditEffect
> eDocEvent (CharEvent c) = eDocC c
> eDocEvent (SpecialKeyEvent k []) | Just e <- lookup k simpleKeys = e
> eDocEvent (ReselectEvent (x,y)) = MoveEdit . clickEDoc (x,y)
> eDocEvent (SelectEvent _ (x,y)) = MoveEdit . clickEDoc (x,y)
> eDocEvent (StringEvent s) = eDocLoad s
> eDocEvent _ = const NoEdit



