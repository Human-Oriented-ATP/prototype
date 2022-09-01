{-|
A parser for a basic Lisp-like syntax into an internal expression.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

module Parser where

import Control.Applicative hiding (many, some)
import Control.Monad.State
import Data.Foldable
import Data.Functor.Identity
import Data.HashMap.Strict (HashMap)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.HashMap.Strict as M

import Debug.Trace

import Lib
import PPrinting

-- Uses megaparsec with a custom state to keep track of local bindings
-- See https://markkarpov.com/tutorial/megaparsec.html for a tutorial on
-- megaparsec. In the future, might want to change the monad from StateT to
-- something else which runs mutably, but should test to see. STRef or IORef
-- might be more efficient, but also might give overheads (and IORef restricts
-- how it can be used).
type Parser =
    ParsecT Void String
    (StateT (HashMap String InternalName, Int) Identity)

exampleStrings :: [String]
exampleStrings =
  [ "succ"
      -- test constants
  , "succ(zero)"
      -- test application + constants
  , "not(eq(succ(zero))(zero))"
      -- test more complex application
  , "not(eq(succ(zero), zero))"
      -- test n-ary application
  , "forall x:TopSpace, not(eq(succ(zero), zero))"
      -- test binders
  , "forall x:TopSpace, not(eq(succ(x), zero))"
      -- test binding (peano one)
  , "forall x:TopSpace, forall y:Point, implies(eq(succ(x), succ(y)), eq(x, y))"
      -- test multiple binding (peano two)
  ]

-- This is the syntax I want to parse
-- expr := expr(args)
--       | forall x, expr
--       | con
--       | free
-- args := expr[,expr]*
--
-- To remove left-recursion, transform it into this syntax
-- expr     := expr-non(args)*
-- expr-non := forall x, expr
--           | con
--           | free

-- | The general expression parser.
parseExpr :: Parser Expr
parseExpr = do
  f <- parseExprNon
  i <- many parseApps
  return $ foldl' apps f i

parseExprNon :: Parser Expr
parseExprNon = parseForall <|> parseCon <|> parseFree

-- | Parse a sequence of arguments
parseApps :: Parser [Expr]
parseApps = char '(' *> sepBy1 parseExpr (string ", ") <* char ')'

-- | Register a new identifier, and return its internal name
registerIdent :: MonadState (HashMap String InternalName, Int) m
              => String -> m InternalName
registerIdent s = do
  (m, i) <- get
  put (M.insert s i m, i + 1)
  return i



-- | Parse a forall expression
parseForall :: Parser Expr
parseForall = do
  _ <- string "forall "
  i <- parseIdent
  nm <- registerIdent i
  _ <- string ":"
  varType <- parseIdent
    -- ^ it's important that this runs before the e <- parseExpr
  _ <- string ", "
  e <- parseExpr
  return (forall (Just (ExternalName i)) nm e)

-- | Parse a free variable (must be known from the context)
parseFree :: Parser Expr
parseFree = try $ do
  i <- parseIdent
  (m, _) <- get
  case m M.!? i of
    Just n -> return $ Free n
    Nothing -> fail "unrecognised identifier"
      -- the name used wasn't recognised
      -- not sure if this error can even happen?

-- | Parse a constant
parseCon :: Parser Expr
parseCon = try (Con <$> some letterChar)
  -- this try might be unnecessary but if the syntax changes it could become
  -- crucial

-- | Parse an identifier (doesn't register it!)
parseIdent :: Parser String
parseIdent = try (some letterChar)

-- | Run the parser in the IO monad - mostly for testing.  This assumes an
-- empty context - if we already know for example that "x" means something
-- and has an existing internal name, then this doesn't apply.
parseTestT :: Show a => Parser a -> String -> IO ()
parseTestT p inp =
  case evalState (runParserT p "example" inp) (M.empty, 0) of
      -- change the (M.empty, 0) to change the context
    Left e -> putStr (errorBundlePretty e)
    Right x -> print x

-- | Run the parser, returning Just _ on success, and `Nothing` on failure.
-- This assumes an empty context - if we already know for example that "x"
-- means something and has an existing internal name, then this doesn't apply.
parseSimple :: Parser Expr -> String -> Maybe Expr
parseSimple p inp =
  case evalState (runParserT p "example" inp) (M.empty, 0) of
    Left _ -> Nothing
    Right x -> Just x

-- | Run the examples.
runExamples :: IO ()
runExamples = for_ exampleStrings $ \test -> do
  putStrLn $ "Running test case: " ++ test
  case evalState (runParserT (parseExpr <* eof) "example" test) (M.empty, 0) of
    Left e -> putStr (errorBundlePretty e)
    Right x -> do
      putStr "Internal expression: "
      print x
      putStrLn $ "Pretty printed expression: " ++ pprintExpr x
      putStr "\n"
