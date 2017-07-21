******************************************************************************
**********                                                          **********
**********     Main.lhs --- this is Epigram !                       **********
**********                                                          **********
******************************************************************************

> module Main where

> import System.IO (hSetBuffering, BufferMode(..), stdin, stdout)

<> import System(exitFailure)
<> import System.Posix.Signals(sigALRM, installHandler, emptySignalSet)

> import Monadics
> import Emacs
> import Igor
> import Interact


> epigramInit :: IO ()
> epigramInit =
>   do 
>      emacsDOIT makeFaces
>      emacsDOIT ("start-epigram" ~$ [])

> main :: IO ()
> main =
>   do 
>      hSetBuffering stdin  LineBuffering
>      hSetBuffering stdout LineBuffering
>      -- installHandler sigALRM (Catch exitFailure) (Just emptySignalSet)
>		-- for controlled exit in prof.
>      epigramInit
>      result initEpigram mainLoop


