module Main (main) where

import System.Environment
import Test.DocTest

main :: IO ()
main = getArgs >>= doctest . (++ ["src"])
