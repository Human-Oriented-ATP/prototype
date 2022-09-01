{-# OPTIONS_GHC -Wno-unused-imports #-}
module Main where

import Control.Monad.State
import Data.Foldable
import Text.Megaparsec

import Lib
import Parser
--import Problem
--import Zipper

-- | Run the parsing examples.
{-
runExamplesMain :: IO ()
runExamplesMain = for_ exampleStrings $ \test -> do
  putStrLn $ "Running test case: " ++ test
  case evalState (runParserT (parseExpr <* eof) "example" test) (mempty, 0) of
    Left e -> putStr (errorBundlePretty e)
    Right x -> do
      putStr "Internal expression: "
      print x
      putStrLn $ "Pretty printed expression: " ++ pprintExpr x
      putStr "\n"
-}
main :: IO ()
main = return ()