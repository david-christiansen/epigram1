******************************************************************************
**********                                                          **********
**********     Utils.lhs --- miscellaneous futility unctions        **********
**********                                                          **********
******************************************************************************

> module Utils where

> import Debug.Trace

******************************************************************************
tracing
******************************************************************************

> track :: String -> x -> x
> -- track s = trace (';' : s)
> track s = id

> {-# RULES  "track/id"  forall s x . track s x = x
> #-}

******************************************************************************
padding
******************************************************************************

> copies :: Int -> a -> [a]
> copies i = take i . repeat

> spaces :: [Char]
> spaces = repeat ' '


******************************************************************************
reading numbers can go wrong
******************************************************************************

> digit :: Char -> Maybe Int
> digit '0' = Just 0
> digit '1' = Just 1
> digit '2' = Just 2
> digit '3' = Just 3
> digit '4' = Just 4
> digit '5' = Just 5
> digit '6' = Just 6
> digit '7' = Just 7
> digit '8' = Just 8
> digit '9' = Just 9
> digit  _  = Nothing

> isDigit :: Char -> Bool
> isDigit c | Just _ <- digit c = True
> isDigit _ = False

> numeral :: String -> Maybe Int
> numeral (c : cs)
>   = do i <- digit c
>        num i cs
>          where
>            num i "" = return i
>            num i (c : cs)
>              = do j <- digit c
>                   num (i * 10 + j) cs
> numeral "" = Nothing


******************************************************************************
IO stuff
******************************************************************************

> getLines :: IO String
> getLines
>   = do s <- getLine
>        if s == "" then return ""
>                   else do t <- getLines
>                           return (s ++ "\n" ++ t)

> putString :: String -> IO ()
> putString [] = return ()
> putString (x : xs) = do
>   putChar x
>   putString xs

> test :: Show x => (String -> x) -> IO ()
> test cook
>   = do s <- getLines
>        print (cook s)

