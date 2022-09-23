{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use zipWith" #-}
module ExistentialMoves where

import Lib
import TableauFoundation
import Poset
import BasicMoves
import Data.Maybe
import Data.List
import Control.Monad
import qualified Data.HashMap.Strict as M
import PPrinting
import HoleExpr
import Debug.Trace
import Parser

-- Instantiate an existentially quantified variable, x, in the QZone with a given expression
-- We need to ensure that none of the free variables in the expression must come after x
-- We then need to update the dependencies so that all variables which had to come after x must now come after all free variables in the expression
instantiateExistentialNoParse :: InternalName -> Expr -> Tableau -> Maybe Tableau
instantiateExistentialNoParse inNm expr (Tableau qZone@(Poset set deps) rootBox) = do
    let relevantQVars = filter (\qVar -> qVarGetInternalName qVar == inNm) set
    guard $ not (null relevantQVars) -- Ensure the given InternalName is actually in the QZone

    let qVar = head relevantQVars
    guard $ qVarGetQuantifier qVar == "Exists" -- Ensure the given InternalName is existentially quantified

    let freeVarsInExpr = getFreeVars expr
    guard $ inNm `notElem` freeVarsInExpr -- Can't try to substitute a variable for something which contains itself

    let qVarsInExpr = concatMap (\inNm -> filter (\qVar -> qVarGetInternalName qVar == inNm) set) freeVarsInExpr -- IMPROVEMENT - Technically not safe, but should be practically unless QZone becomes ill-formed
    guard $ all (\x -> not $ isAfter qZone x qVar) qVarsInExpr -- Ensure dependencies are valid

    -- Now we have the all-clear to make the instantiation, and update dependencies
    let previousDependents = [y | y <- set, isAfter qZone y qVar]
    let newDeps = [(x, y) | y <- previousDependents, x <- qVarsInExpr]
    newQZone <- addRels (removeMember qZone qVar) newDeps

    let
        instantiateInExpr :: Expr -> Expr
        instantiateInExpr (App a b) = App (instantiateInExpr a) (instantiateInExpr b)
        instantiateInExpr (Abs exNm (Sc sc)) = Abs exNm (Sc (instantiateInExpr sc))
        instantiateInExpr (Con con) = Con con
        instantiateInExpr (B i) = B i
        instantiateInExpr (Free i) = if i == inNm then expr else Free i

    return $ Tableau newQZone (fmap instantiateInExpr rootBox)


-- Takes a string giving the show-ExternalName of the relevant variable, then a string specifying the term we want to instantiate it for
-- Parses the information to hand onto instantiateExistentialNoParse
instantiateExistential :: String -> String -> Tableau -> Maybe Tableau
instantiateExistential exNmStr exprStr tab@(Tableau qZone@(Poset set rel) boxes) = do
    let showMap = getShowMap $ getStartingPrintState qZone (PS mempty mempty 0)
    let inNms = filter (\n -> M.lookup n showMap == Just (ExternalName exNmStr)) (map qVarGetInternalName set)
    guard $ length inNms == 1
    let (inNm:_) = inNms
    expr <- parseWithQZone qZone exprStr
    instantiateExistentialNoParse inNm expr tab

