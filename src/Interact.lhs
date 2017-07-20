******************************************************************************
**********                                                          **********
**********     Interact.lhs --- the Epigram user interface          **********
**********                                                          **********
******************************************************************************

> module Interact where

> import Utils
> import Category
> import Monadics
> import Zip
> import Name
> import Parser
> import Doc
> import Emacs
> import Box
> import Igor
> import Elab
> import Emacs

> import Debug.Trace


******************************************************************************
initialization
******************************************************************************

> emptyCtxt :: Ctxt
> emptyCtxt =
>   Zip :<:
>   Layer (Long Zip,0) Zip cur0 (Prob Satisfied (Elab,QTerm) Gap)
>     (ImOld False box0)

> initCtxt :: Ctxt
> initCtxt = tryThis emptyCtxt $
>   do enter $ Name (button /// "Quit",0)
>       (Waiting m0 m0 $ Prob Satisfied (Elab,QTerm) (Button "{Quit}" "Quit"))
>       ImNew
>      enter $ Name (button /// "Reset",0)
>       (Waiting m0 m0 $
>          Prob Satisfied (Elab,QTerm) (Button "{Reset}" "Reset"))
>       ImNew
>      enter $ Name (button /// "Undo",0)
>       (Waiting m0 m0 $ Prob Satisfied (Elab,QTerm) (Button "{Undo}" "Undo"))
>       ImNew
>      enter $ Name (button /// "Blankety",0)
>       (Waiting m0 m0 $ Prob Satisfied (Elab,QTerm) Blankety) ImNew
>      private "Gap" Zip $ await (Elab,QDecl) Gap
>      (d,_) <- private "Decl" Zip $ await (Elab,QDecl) (From emptyEDoc Source)
>      private "Gap" Zip $ await (Elab,QDecl) Gap
>      tweak $ focus d
>      return ()

> initEpigram = Epigram {
>   epiCtxt = initCtxt,
>   epiDisplay = Zip,
>   epiUndo = eta initCtxt, -- cyclic
>   epiEditorWidth = 78,
>   epiNeedsIgor = True,
>   epiEventQueue = [],
>   epiLocalInfo = (Nothing,False),
>   epiLocalDisplay = box0
>   }


******************************************************************************
from strings sent by emacs to events
******************************************************************************

> inputEvents :: String -> Epigram -> [Event]
> inputEvents s epi = flip prefer [] $
>   do is <- lexer (s ++ "\n")
>      case is of
>        [I (ID "click"),I (ID "Epigram"),
>         I (INT 1),I (INT x),I (INT y),I LF] ->
>          return (clickEvents epi (x,y))
>        [I (ID "click"),I (ID "Epigram"),I (INT 2),_,_,I LF] ->
>          return [DoubleClickEvent]
>        [I (ID "click"),I (ID "Horace"),
>         I (INT 1),I (INT x),I (INT y),I LF] ->
>          return (clickLocalEvents epi (x,y))
>        [I (ID "key"),I (INT x),I (ID "nil"),I LF] ->
>          return [CharEvent (toEnum x)]
>        [I (ID "key"),I (ID "space"),I (ID "nil"),I LF] ->
>          return [CharEvent ' ']
>        [I (ID "key"),I (ID ks),I (ID "nil"),I LF] ->
>          do sk <- specialKey ks
>             return [SpecialKeyEvent sk []]
>        [I (ID "key"),I (ID ks),Group (Items is),I LF] ->
>          do sk <- specialKey ks
>             return [SpecialKeyEvent sk $
>                       do I (ID s) <- is
>                          modifierKey s]
>        [I (ID "key"),I (INT x),Group (Items is),I LF] ->
>          do let sk = ModChar (toEnum x)
>             return [SpecialKeyEvent sk $
>                       do I (ID s) <- is
>                          modifierKey s]
>        [I DATA,I LF] ->
>          return [StringEvent ""]
>        [I (ID "refresh"),I (INT x),I LF] | x >= 42 ->
>          return [RefreshEvent (x - 2)]
>        _ -> return []

> clickEvents :: Epigram -> (Int,Int) -> [Event]
> clickEvents epi (x,y) =
>   case fish True bxs of
>     Left _ -> track "fishy" []
>     Right (b,bxy) -> track "fished" $
>       case clickTag bxy False b of
>         Missing -> track "hiss" []
>         Rightmost (cur',cxy) -> track (show cur') $
>           if cur == cur' then [ReselectEvent cxy]
>             else track "DE" [DeselectEvent,SelectEvent cur' cxy]
>   where
>     cur = whereAmI (epiCtxt epi)
>     bxs = epiDisplay epi
>     fish :: Bool -> Zip ((String,Int),BoxS) -> Either Int (BoxS,(Int,Int))
>     fish _ Zip = Left 0
>     fish last (bz :<: (_,b)) =
>       case fish False bz of
>         Right ans -> Right ans
>         Left oy ->
>           let (w,(h,d)) = bSize b
>               oy' = oy + h + d
>           in  if y < oy' || last then Right (b,(x,y - oy - h)) else Left oy'

> clickLocalEvents :: Epigram -> (Int,Int) -> [Event]
> clickLocalEvents epi xy
>   | Rightmost (nom,nxy) <- clickTag xy True (epiLocalDisplay epi)
>   = [HoraceEvent nom]
>   | otherwise = []


> testLoop :: Interactive ()
> testLoop =
>   do doo . emacsDOIT . epigram $ ("delete-buffer-contents" ~$ [])
>      igor
>      epigramDisplay
>      continue
>   where
>     continue =
>       do s <- doo getLine
>          es <- get (inputEvents s)
>          doo (print es)
>          case es of
>            [CharEvent 'q'] -> return ()
>            _ -> continue


> expandEvents :: Event -> Maybe [Event]
> expandEvents (SpecialKeyEvent EscapeKey [Alt]) =
>   Just [ActionEvent "Quit"]
> expandEvents (SpecialKeyEvent EscapeKey [Ctrl]) =
>   Just [ActionEvent "Quit"]
> expandEvents (SpecialKeyEvent ReturnKey [Ctrl,Alt]) =
>   Just [ActionEvent "Reset"]
> expandEvents (SpecialKeyEvent ReturnKey [Alt,Ctrl]) =
>   Just [ActionEvent "Reset"]
> expandEvents (SpecialKeyEvent BackspaceKey [Alt]) =
>   Just [ActionEvent "Undo"]
> expandEvents (SpecialKeyEvent EscapeKey []) =
>   Just [ActionEvent "Elab"]
> expandEvents _ = Nothing


******************************************************************************
the main interactive cycle
******************************************************************************

> eventLoop :: Interactive Bool
> eventLoop = do
>   es <- get epiEventQueue
>   case es of
>     [] -> return False
>     e : es -> do
>       tweak $ \ x -> x {epiEventQueue = es}
>       b <- handle e
>       if b then return True
>            else eventLoop
>   where
>     handle e | Just es <- expandEvents e = do
>       epigramPostEvents es
>       return False
>     handle (ActionEvent "Quit") = return True
>     handle (ActionEvent "Reset") = do
>       epigramUndoMark
>       ud <- get epiUndo
>       tweak $ \ x -> x {epiCtxt = initCtxt,
>                         epiDisplay = Zip,
>                         epiNeedsIgor = True}
>       igor
>       epigramUndoMark
>       epigramUndo
>       return False
>     handle e@(HoraceEvent nom) = do
>       ctxt@(_ :<: Layer (cur,_) _ _ _ _) <- get epiCtxt
>       tweak $ \ x -> x {epiCtxt = focus nom ctxt}
>       epigramEvent e
>       tweak $ \ x -> x {epiCtxt = focus cur ctxt}
>       return False
>     handle (RefreshEvent ew') = do
>       epigramUndoMark
>       tweak $ \ x -> x {epiEditorWidth = ew'}
>       epigramUndo
>       return False
>     handle (ActionEvent "Undo") =
>       do epigramUndo
>          return False
>     handle (SpecialKeyEvent BackspaceKey [Ctrl]) =
>       do doo . emacsDOIT . emacs $
>            "epigram-queue-input" ~$
>              ["concat" ~$
>                [ES "refresh ",
>                 "number-to-string" ~$ ["frame-width" ~$ []]
>                ]
>              ]
>          return False
>     handle (SpecialKeyEvent ReturnKey [Alt]) =
>       do ctxt <- get epiCtxt
>          doo $ print ctxt
>          return False
>     handle e@(SelectEvent nom _) =
>       do ctxt <- get epiCtxt
>          tweak $ \ x -> x {epiCtxt = focus nom ctxt}
>          epigramEvent e
>          epigramGetLocalInfo
>          return False
>     handle DeselectEvent = do
>       ctxt <- get epiCtxt
>       tweak $ \ x -> x {epiCtxt = killLocalInfo ctxt}
>       epigramEvent DeselectEvent
>       return False
>     handle (StringEvent _) =
>       do ss <- doo getSs
>          epigramEvent (StringEvent ss)
>          return False
>       where
>         getSs = do
>           s <- getLine
>           if s == "][][][][][" then return []
>              else do
>                ss <- getSs
>                return (s ++ "\n" ++ ss)
>     handle e =
>       do epigramEvent e
>          return False

> eventsPlease :: Interactive ()
> eventsPlease =
>   do s <- doo getLine
>      es <- get (inputEvents s)
>      if null es then eventsPlease
>                 else epigramPostEvents es

> mainLoop :: Interactive ()
> mainLoop =
>   do igor
>      epigramDisplay
>      epigramLocalDisplay
>      epigramCursor
>      eventsPlease
>      stop <- eventLoop
>      if stop then return () else mainLoop
