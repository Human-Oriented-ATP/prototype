module Unification where

import Box
import Poset
import Lib
import TableauFoundation
import PPrinting
import Data.List

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

-- Asks if we can get the second expression from the first by substituting free variables from the first for expressions correctly.
matchExpressions :: Expr -> Expr -> Maybe Substitution
matchExpressions (App e1 e2) (App e1' e2') = do
    sub1 <- matchExpressions e1 e1'
    sub2 <- matchExpressions e2 e2'
    mergeSubstitutions sub1 sub2
matchExpressions (App e1 e2) _ = Nothing
matchExpressions (Abs _ (Sc sc1)) (Abs _ (Sc sc2)) = matchExpressions sc1 sc2
matchExpressions (Con s) (Con s') = if s == s' then Just [] else Nothing
matchExpressions (B i) (B i') = if i == i' then Just [] else Nothing
matchExpressions (Free i) expr = if checkIsTerm expr then Just [(i, expr)] else Nothing
matchExpressions _ _ = Nothing

    









-- <<< TESTING >>>

-- subset_of(f(A), B)
-- 0 : f
-- 1 : A
-- 2 : B
expression1a :: Expr
expression1a = BApp (Pred "subset_of") (App (Free 0) (Free 1)) (Free 2)
expression1b = BApp (Pred "subset_of") (Free 1) (App (UApp (Operator "func_inv") (Free 0)) (Free 2))

-- subset_of(f(cl(A)), cl(f(A)))
expression2 = BApp (Pred "subset_of") (App (Free 0) (UApp (Operator "closure") (Free 1))) (UApp (Operator "closure") (App (Free 0) (Free 1)))

-- Performs a given substitution on an expression
applySubstitution :: Substitution -> Expr -> Expr
applySubstitution [] expr = expr
applySubstitution ((inNm, subExpr):rest) expr = applySubstitution rest (singleSub inNm subExpr expr) where
    singleSub :: InternalName -> Expr -> Expr -> Expr
    -- IMPROVEMENT - Broken - need to lock things in somehow. Might have to use the "Variable"'s / "Hole"'s to fix this.
    singleSub i e (Free j) = if i == j then e else Free j
    singleSub i e (App e1 e2) = App (singleSub i e e1) (singleSub i e e2)
    singleSub i e (Abs exNm (Sc sc)) = Abs exNm (Sc (singleSub i e sc))
    singleSub i e (Con conS) = Con conS
    singleSub i e (B j) = B j

Just sub = matchExpressions expression1a expression2
result = applySubstitution sub expression1b
