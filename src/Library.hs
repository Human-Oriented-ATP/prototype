{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Library where

import Box
import Poset
import Lib
import TableauFoundation
import PPrinting
import Data.List


-- | The type of expressions with the addition of variables in the sense of unification.
data HoleExpr
  = HoleApp HoleExpr HoleExpr
    -- ^ A function application. Note that the function itself can be an expression.
  | HoleAbs (Maybe ExternalName) HoleScoped
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | HoleFree InternalName
    -- ^ A free variable.
  | HoleCon ConstantString
    -- ^ A constant (eg the naturals, or the sin function).
  | HoleB Int
    -- ^ A bound variable
  | Hole InternalName
    -- ^ A hole variable to be filled
  deriving (Eq, Show) 

newtype HoleScoped = HoleSc HoleExpr
  deriving (Eq, Show)

-- | Takes an expression and gives the corresponding holed expression
exprToHoleExpr :: Expr -> HoleExpr
exprToHoleExpr (App e e') = HoleApp (exprToHoleExpr e) (exprToHoleExpr e')
exprToHoleExpr (Abs exNm (Sc sc)) = HoleAbs exNm (HoleSc (exprToHoleExpr sc))
exprToHoleExpr (Free n) = HoleFree n
exprToHoleExpr (Con con) = HoleCon con
exprToHoleExpr (B i) = HoleB i

-- | Takes an expression and gives the holed expression obtained by turning all free variables into holes
holeFreeVars :: Expr -> HoleExpr
holeFreeVars (App e e') = HoleApp (holeFreeVars e) (holeFreeVars e')
holeFreeVars (Abs exNm (Sc sc)) = HoleAbs exNm (HoleSc (holeFreeVars sc))
holeFreeVars (Free n) = Hole n
holeFreeVars (Con con) = HoleCon con
holeFreeVars (B i) = HoleB i

-- | Takes a holed expression without holes and returns an expression (Maybe because there might be holes)
holeExprToExpr :: HoleExpr -> Maybe Expr
holeExprToExpr (HoleApp e e') = do
    a <- holeExprToExpr e
    b <- holeExprToExpr e'
    return $ App a b
holeExprToExpr (HoleAbs exNm (HoleSc sc)) = do
    a <- holeExprToExpr sc
    return $ Abs exNm (Sc a)
holeExprToExpr (HoleFree n) = Just $ Free n
holeExprToExpr (HoleCon con) = Just $ Con con
holeExprToExpr (HoleB i) = Just $ B i
holeExprToExpr (Hole i) = Nothing


-- We're simply going to force free variables to be equated for now
-- probably change to HashMap later, but will keep as list for now
type Substitution = [(InternalName, Expr)]

-- Check that all InternalNames map to things which agree, then union
-- (there are more efficient ways to do this, of course)
mergeSubstitutions :: Substitution -> Substitution -> Maybe Substitution
mergeSubstitutions s1 s2 = 
    let attempt = nub (s1 ++ s2)
        agree = map fst attempt == nub (map fst attempt)
    in if agree then Just attempt else Nothing

-- The idea is to check that an expressions is a TERM not a formula
checkIsTerm :: Expr -> Bool
checkIsTerm (App e1 e2) = checkIsTerm e1 && checkIsTerm e2
checkIsTerm (Abs _ _) = False
checkIsTerm (Free _) = True
checkIsTerm (B _) = True
checkIsTerm (Con (Operator _)) = True
checkIsTerm (Con (Obj _)) = True
checkIsTerm _ = False

-- Asks if we can get the second expression from the first by substituting terms for holes correctly.
matchExpressions :: HoleExpr -> Expr -> Maybe Substitution
matchExpressions (HoleApp e1 e2) (App e1' e2') = do
    sub1 <- matchExpressions e1 e1'
    sub2 <- matchExpressions e2 e2'
    mergeSubstitutions sub1 sub2
matchExpressions (HoleAbs _ (HoleSc sc1)) (Abs _ (Sc sc2)) = matchExpressions sc1 sc2
matchExpressions (HoleCon s) (Con s') = if s == s' then Just [] else Nothing
matchExpressions (HoleB i) (B i') = if i == i' then Just [] else Nothing
matchExpressions (HoleFree n) (Free n') = if n == n' then Just [] else Nothing
matchExpressions (Hole i) expr = if checkIsTerm expr then Just [(i, expr)] else Nothing
matchExpressions _ _ = Nothing

-- Performs a given substitution on an expression
applySubstitution :: Substitution -> HoleExpr -> HoleExpr
applySubstitution [] expr = expr
applySubstitution ((inNm, subExpr):rest) expr = applySubstitution rest (singleSub inNm subExpr expr) where
    singleSub :: InternalName -> Expr -> HoleExpr -> HoleExpr
    singleSub i e (Hole j) = if i == j then exprToHoleExpr e else Hole j
    singleSub i e (HoleApp e1 e2) = HoleApp (singleSub i e e1) (singleSub i e e2)
    singleSub i e (HoleAbs exNm (HoleSc sc)) = HoleAbs exNm (HoleSc (singleSub i e sc))
    singleSub i e (HoleFree j) = HoleFree j
    singleSub i e (HoleCon conS) = HoleCon conS
    singleSub i e (HoleB j) = HoleB j

