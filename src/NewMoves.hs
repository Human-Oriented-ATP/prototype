{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}
module NewMoves where

import Lib
import TableauFoundation
import Poset
import Data.Maybe
import Data.List
import Control.Monad
import PPrinting
import Unification
import Debug.Trace


-- Takes a QBox (a box with quantification info) and returns an updated QBox. Maybe because the move could fail
type BoxMove = QBox -> Maybe QBox
-- Takes a Tableau and returns an updated Tableau. Again, Maybe because the move could fail.
type TableauMove = Tableau -> Maybe Tableau

-- Takes a BoxMove and performs it on the i-th box in a Tableau
boxToTabMove :: BoxMove -> Int -> TableauMove
boxToTabMove _ _ (Tableau qZone []) = Just $ Tableau qZone []
boxToTabMove move i (Tableau qZone boxes)
    | i < 0 || i >= length boxes = Nothing
    | otherwise = do
        let (as, box:bs) = splitAt i boxes
        moveResult <- move (qZone, box)
        let (newQZone, newBox) = moveResult
        return $ Tableau newQZone (as ++ newBox : bs)


-- Gets an unused InternalName from a QZone
getNewInternalName :: QZone -> InternalName
getNewInternalName (Poset set rel) = freshName (map qVarGetInternalName set)
    where
        freshName :: [InternalName] -> InternalName
        freshName [] = 0
        freshName usedNames = maximum usedNames + 1

findFreshExNm :: [ExternalName] -> ExternalName
findFreshExNm usedNames = head $ filter (`notElem` usedNames) options
    where options = [ExternalName (x : replicate n '\'') | n <- [0..], x <- ['a'..'z']]

getNewExternalNamePeel :: Maybe ExternalName -> QZone -> Maybe ExternalName
getNewExternalNamePeel exNm (Poset set rel) = case exNm of
    Just nm -> if nm `elem` (mapMaybe qVarGetExternalName set) then Just $ findFreshExNm (mapMaybe qVarGetExternalName set) else exNm
    _ -> Just $ findFreshExNm (mapMaybe qVarGetExternalName set)


-- Although it's inefficient to append to the end of a list, it's far more intuitive to add hypotheses to the end than the start.
-- This also avoids issues of hypotheses changing index mid-move.
-- Maybe because it makes Monadic chaining with updating easier.
addHyp :: Hyp -> QBox -> Maybe QBox
addHyp hyp (qZone, Box hyps targs) = Just (qZone, Box (hyps++[hyp]) targs)

addTarg :: Hyp -> QBox -> Maybe QBox
addTarg targ (qZone, Box hyps targs) = Just (qZone, Box hyps (targs++[targ]))

-- Removes hyps/targs. Should out-of-bounds index give unchanged or Nothing? Not sure yet.
-- IMPROVEMENT - think about whether out-of-bounds index should return unchanged or Nothing
removeHyp :: Int -> QBox -> Maybe QBox
removeHyp i (qZone, Box hyps targs)
    | i < 0 || i >= length hyps = Just (qZone, Box hyps targs)
    | otherwise =
        let (as, (hyp:bs)) = splitAt i hyps
            updatedHyps = as++bs
        in Just (qZone, Box updatedHyps targs)

removeTarg :: Int -> QBox -> Maybe QBox
removeTarg i (qZone, Box hyps targs)
    | i < 0 || i >= length targs = Just (qZone, Box hyps targs)
    | otherwise =
        let (as, (targ:bs)) = splitAt i targs
            updatedTargs = as++bs
        in Just (qZone, Box hyps updatedTargs)

-- Updates the i-th hypothesis. Maybe because it might not exist.
updateHyp :: Int -> Targ -> QBox -> Maybe QBox
updateHyp i newHyp (qZone, Box hyps targs)
    | i < 0 || i >= length hyps = Nothing
    | otherwise = Just (qZone, Box newHyps targs) where
    newHyps = let (as, hyp:bs) = splitAt i hyps in (as ++ newHyp : bs)

updateTarg :: Int -> Targ -> QBox -> Maybe QBox
updateTarg i newTarg (qZone, Box hyps targs)
    | i < 0 || i >= length targs = Nothing
    | otherwise = Just (qZone, Box hyps newTargs) where
    newTargs = let (as, targ:bs) = splitAt i targs in (as ++ newTarg : bs)

-- Gets the i-th hypothesis. Maybe because it might not exist
getHyp :: Int -> [Hyp] -> Maybe Hyp
getHyp i hyps
    | i < 0 || i >= length hyps = Nothing
    | otherwise = Just $ hyps!!i

getTarg :: Int -> [Targ] -> Maybe Targ
getTarg i targs
    | i < 0 || i >= length targs = Nothing
    | otherwise = Just $ targs!!i


-- Gets the i-th box from a list of boxes, returning a QBox (qZone given by that of Tableau). Maybe beacuse it might not exist
getBox :: Int -> Tableau -> Maybe QBox
getBox i tab@(Tableau qZone boxes)
    | i < 0 || i >= length boxes = Nothing
    | otherwise = Just $ (qZone, boxes!!i)

-- Adds a box to a Tableau. We presume that it's correctly quantified by the Tableau's qZone
addBox :: Box -> Tableau -> Maybe Tableau
addBox box tab@(Tableau qZone boxes) = Just $ (Tableau qZone (boxes++[box]))

-- Removes a box from a Tableau. Same issue as removing hyp/targ - should this return nothing if out-of-bounds?
removeBox :: Int -> Tableau -> Maybe Tableau
removeBox boxInd tab@(Tableau qZone boxes)
    | boxInd < 0 || boxInd >= length boxes = Just tab
    | otherwise =
        let (as, (box:bs)) = splitAt boxInd boxes
            updatedBoxes = as ++ bs
        in Just $ (Tableau qZone updatedBoxes)

-- Updated a box in a Tableau.
updateBox :: Int -> Box -> Tableau -> Maybe Tableau
updateBox boxInd updatedBox tab@(Tableau qZone boxes)
    | boxInd < 0 || boxInd >= length boxes = Nothing
    | otherwise =
        let (as, (box:bs)) = splitAt boxInd boxes
            updatedBoxes = as ++ (updatedBox:bs)
        in Just $ (Tableau qZone updatedBoxes)

-- Clear empty boxes
clearEmptyBoxes :: Tableau -> Maybe Tableau
clearEmptyBoxes tab@(Tableau qZone boxes) = 
    let filteredBoxes = filter (\(Box hyps targs) -> targs /= []) boxes
    in Just $ (Tableau qZone filteredBoxes)

-- Peels universal target
-- targ i : forall x, P(x)
-- IMPROVEMENT - update how dependencies work so that consecutively peeled forall's don't have forced order when they in fact commute
peelUniversalTargBox :: Int -> BoxMove
peelUniversalTargBox i qBox@(qZone, Box hyps targs) = do
    (expr@(Forall exNm sc), freeVars) <- getTarg i targs
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateTarg i (instantiate (Free peeledName) sc, peeledVariable:freeVars) qBox
    return $ (newQZone, newBox)

-- Peels existential target, creating a metavariable
-- targ i : exists x, P(x)
peelExistentialTargBox :: Int -> BoxMove
peelExistentialTargBox i qBox@(qZone, Box hyps targs) = do
    (expr@(Exists exNm sc), freeVars) <- getTarg i targs
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateTarg i (instantiate (Free peeledName) sc, peeledVariable:freeVars) qBox
    return $ (newQZone, newBox)

-- Peels existential hypothesis
-- hyp i : forall x, P(x)
-- IMPROVEMENT - currently find new external name to prevent confusing outputs after a single move, but maybe this should happen at the print stage? Think about this.
peelExistentialHypBox :: Int -> BoxMove
peelExistentialHypBox i qBox@(qZone, Box hyps targs) = do
    (expr@(Exists exNm sc), freeVars) <- getHyp i hyps
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateHyp i (instantiate (Free peeledName) sc, peeledVariable:freeVars) qBox
    return $ (newQZone, newBox)

-- Tidies implication in target
-- targ i : P \implies Q
-- IMPROVEMENT (!!IMPORTANT!!) - actually need to create a new box when we do this technically, if there are multiple targets
-- IMPROVEMENT - could be stricter with tracking free variables here
tidyImplInTarg :: Int -> Int -> TableauMove
tidyImplInTarg i boxInd tab@(Tableau qZone boxes) = do
    qBox@(qZone, Box hyps targs) <- getBox boxInd tab
    (Implies p q, freeVars) <- getTarg i targs
    let newHyps = hyps ++ [(p, freeVars)]
    let newTargs = [(q, freeVars)]
    let newBox = Box newHyps newTargs
    (_, remainingBox) <- removeTarg i qBox
    updateBox boxInd remainingBox tab >>= addBox newBox >>= clearEmptyBoxes

-- Splits and hypotheses up
-- hyp i : P ^ Q
-- IMPROVEMENT - could be stricter with tracking free variables here
tidyAndInHypBox :: Int -> BoxMove
tidyAndInHypBox i qBox@(qZone, Box hyps targ) = do
    (And p q, freeVars) <- getHyp i hyps
    updateHyp i (p, freeVars) qBox >>= addHyp (q, freeVars)

tidyAndInTargBox :: Int -> BoxMove
tidyAndInTargBox i qBox@(qZone, Box hyps targs) = do
    (And p q, freeVars) <- getTarg i targs
    updateTarg i (p, freeVars) qBox >>= addTarg (q, freeVars)


-- Performs modus ponens on hypotheses i and j
-- hyp i : forall x, P(x) \implies Q(x)
-- hyp j : P(y)
-- conclude : Q(y)
modusPonensBox :: Int -> Int -> BoxMove
modusPonensBox i j qBox@(qZone, Box hyps targs) = do
    (expr@(Forall exNm (Sc (Implies px qx))), freeVars) <- getHyp i hyps
    (py, freeVars'@(freeVar':rest')) <- getHyp j hyps
    let toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
    guard $ not (null toInstantiate')
    guard $ (expr /= py)
    let successes = filter (\var -> instantiate (Free . qVarGetInternalName $ var) (Sc px) == py) toInstantiate'
    guard $ length successes == 1
    let newHyp = (instantiate (Free . qVarGetInternalName . head $ successes) (Sc qx), freeVars)
    addHyp newHyp qBox

-- Performs backwards reasoning on hypothesis i and target j
-- hyp i  : P \implies Q
-- targ j : Q
-- replace targ j with P
backwardsReasoningHypBox :: Int -> Int -> BoxMove
backwardsReasoningHypBox i j qBox@(qZone, Box hyps targs) = do
    (expr@(Implies p q), freeVars) <- getHyp i hyps
    (q', freeVars) <- getTarg j targs
    guard $ q == q'
    updateTarg j (p, freeVars) qBox

-- For now, a LibraryEquivalence is a QZone, a set of hypotheses (conditions under which the equivalence holds)
-- And finally a pair of expressions which are equivalent in that context.
-- IMPROVEMENT - at the moment, these equivalences actually only go one way, and can only be an equivalence between two terms.
-- Not hard to make it go the other way, too, but think about how exactly (and at what level) we want this to happen.
data LibraryEquivalence = LibraryEquivalence QZone [Expr] (Expr, Expr)

-- For now, a LibraryEquivalence is basically a Tableau (though we won't store the FreeVar info. Maybe we shouldn't be storing this in general, and simply computing it when we need it)
-- IMPROVEMENT - think about whether we need to store FreeVar information all the time in Hyps/Targs
data LibraryImplication = LibraryImplication QZone [Expr] [Expr]

-- Takes a library equivalence and a QBox and applies the library equivalence to the i-th target
-- IMPROVEMENT - I need to think more about what the rules regarding the state of the QZone is
-- IMPROVEMENT - probably in the future, we will search for matches ourself at a higher level. At that point
-- it probably makes more sense to feed the substitution we find and want to use into this function, and have it use this, rather than making it re-find substitutions.
-- can re-use this code at the higher level of finding substitutions, though!
-- IMPROVEMENT - the way this is currently implemented, this actually does forward reasoning implications too
matchLibraryEquivalenceTargBox :: LibraryEquivalence  -> Int -> QBox -> Maybe QBox
matchLibraryEquivalenceTargBox (LibraryEquivalence libQZone conds (e, e')) i qBox@(qZone, Box hyps targs) = do
    (targExpr, freeVars) <- getTarg i targs
    initialSub <- matchExpressions e targExpr -- Match the suggested equivalence with the suggested target
    -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
    let condSubs = map fst $ findConsistentSubs (zip [0..] conds) (zip [0..] $ map fst hyps)

    -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
    let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
    if null possibleSubs then Nothing
    else let
        sub = head possibleSubs
        newFreeVars = freeVars -- IMPROVEMENT - should really do this by mapping substitutions over the free variables in the library statement, but need a few things which are missing
        -- One option would be to have library statements also contain the FreeVariable info, another would be to write a function to get a list of FreeVariables from a statement (not at all hard)
        -- The bigger issue is that we need [QuantifiedVariable], and so we need to use the QZone context to get the quantification info
        -- Still need to figure out how the QZone works with all of this.
        newTarg = (applySubstitution sub e', newFreeVars)
        in updateTarg i newTarg qBox

-- IMPROVEMENT - should we prevent the hypothesis which will be matched from being one of the conditions?
matchLibraryEquivalenceHypBox :: LibraryEquivalence -> Int -> QBox -> Maybe QBox
matchLibraryEquivalenceHypBox (LibraryEquivalence libQZone conds (e, e')) i qBox@(qZone, Box hyps targs) = do
    (hypExpr, freeVars) <- getHyp i hyps
    initialSub <- matchExpressions e hypExpr -- Match the suggested equivalence with the suggested target
    -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
    let condSubs = map fst $ findConsistentSubs (zip [0..] conds) (zip [0..] $ map fst hyps)

    -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
    let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
    if null possibleSubs then Nothing
    else let
        sub = head possibleSubs
        newFreeVars = freeVars -- IMPROVEMENT - should really do this by mapping substitutions over the free variables in the library statement, but need a few things which are missing
        -- One option would be to have library statements also contain the FreeVariable info, another would be to write a function to get a list of FreeVariables from a statement (not at all hard)
        -- The bigger issue is that we need [QuantifiedVariable], and so we need to use the QZone context to get the quantification info
        -- Still need to figure out how the QZone works with all of this.
        newHyp = (applySubstitution sub e', newFreeVars)
        in updateHyp i newHyp qBox


-- Finds consistent substitutions (if any exists). We also specify the way hypotheses were matched to one another
findConsistentSubs :: [(Int, Expr)] -> [(Int, Expr)] -> [(Substitution, [(Int, Int)])]
findConsistentSubs [] _ = [([], [])]
findConsistentSubs conds@((condIndex, h1):remainingConds) labelledHypExprs
    | length conds > length labelledHypExprs = []
    | otherwise =
        let possibleH1Subs = mapMaybe (\(i, e) -> case (i, matchExpressions h1 e) of
                (n, Just sub) -> Just (n, sub)
                (n, Nothing) -> Nothing) labelledHypExprs

            -- Takes a substitution, and the hypothesis-index which has been matched
            -- along with the old conditions and old hypotheses, then generates a new set of
            -- conditions and hypotheses formed by removing 
            generateNewProblem :: [(Int, Expr)] -> [(Int, Expr)] -> (Int, Substitution) -> ([(Int, Expr)], [(Int, Expr)])
            generateNewProblem [] _ _ = ([], []) -- This pattern should never be matched because the empty condition case is dealt with
            -- There should never be more conditions than hypotheses because this is guarded out initially
            generateNewProblem (_:newCondsPreSub) oldLabelledHyps (ij, sj) =
                -- Do all the substitutions and get rid of first condition and relevant, ij-th, hyp
                let newLabelledHypsPreSub = filter (\(n, exp) -> n /= ij) oldLabelledHyps
                    newLabelledHyps = map (\(n, exp) -> (n, applySubstitution sj exp)) newLabelledHypsPreSub
                    newConds = map (\(n, exp) -> (n, applySubstitution sj exp)) newCondsPreSub
                in (newConds, newLabelledHyps)

            -- These are the remaining problems to solve. We store them as pairs, the first part reprsenting the substitution done (given by a substitution and the hypothesis-index matched)
            -- The second part reprsenting the remaining problem after applying that substitution.
            remainingProblems = map (\s -> (s, generateNewProblem conds labelledHypExprs s)) possibleH1Subs

            -- This takes a remaining problem, recursively finds the solution, and combines it with the initial substitution to give us the final result
            findFutureCombinedSolutions :: ((Int, Substitution), ([(Int, Expr)], [(Int, Expr)])) -> [(Substitution, [(Int, Int)])]
            findFutureCombinedSolutions newProblem =
                let ((i1, s1), (newConds, newLabelledHyps)) = newProblem
                    futureSolutions = findConsistentSubs newConds newLabelledHyps
                    combinedFutureSolutions = mapMaybe (\(s, mapping) -> case mergeSubstitutions s1 s of
                        Just sub -> Just (sub, (condIndex, i1):mapping)
                        _ -> Nothing) futureSolutions
                in combinedFutureSolutions

        -- The final result can be obtained from any of the remainingProblems we generated, thus we need to concatMap.
        in concatMap findFutureCombinedSolutions remainingProblems


-- <<< MOVE TESTING >>>

-- IMPROVEMENT - currently have extremely hacky solution using negative indices for library results
-- The idea is that negative indices represent "hole variables". If we don't do this, substitutions don't work properly
-- because, for instance substituting (Free 1 -> Free 2) then (Free 2 -> Free 3) makes (Free 1, Free 2) into (Free 3, Free 3) incorrectly
-- can solve this less hackily using another "Free" type, like the HExpr's in the UnificationPaper file
openSetDefQZone = Poset [QVar "Forall" (Just $ ExternalName "M") (-1)
    , QVar "Forall" (Just $ ExternalName "d") (-2)
    , QVar "Forall" (Just $ ExternalName "A") (-3)] []
openSetDefH1 = BApp (Pred "metric_on") (Free (-2)) (Free (-1))
openSetDefe = TApp (Pred "open_in_metric") (Free (-3)) (Free (-2)) (Free (-1))
openSetDefe' = forall (Just $ ExternalName "x") (-10) $
    Implies (BApp (Pred "element_of") (Free (-10)) (Free (-3))) $
    exists (Just $ ExternalName "delta") (-20) $
    And (BApp (Pred "real_greater_than") (Free (-20)) (Con $ Obj "0")) $
    forall (Just $ ExternalName "y") (-30) $
    Implies (BApp (Pred "element_of") (Free (-30)) (Free (-1))) $
    Implies (BApp (Pred "real_lesser_than") (App (App (Free (-2)) (Free (-10))) (Free (-30))) (Free (-20))) $
    BApp (Pred "element_of") (Free (-30)) (Free (-3))
openSetDefinition = LibraryEquivalence openSetDefQZone [openSetDefH1] (openSetDefe, openSetDefe')
openSetDefinitionQBox = (openSetDefQZone, Box [(openSetDefH1, [])] [(openSetDefe, []), (openSetDefe', [])])

intersectionDefQZone = Poset [ QVar "forall" (Just $ ExternalName "x") (-1)
    , QVar "forall" (Just $ ExternalName "A") (-2)
    , QVar "forall" (Just $ ExternalName "B") (-3)] []
intersectionDefe = BApp (Pred "element_of") (Free (-1)) (BApp (Operator "set_intersection") (Free (-2)) (Free (-3)))
intersectionDefe' = And (BApp (Pred "element_of") (Free (-1)) (Free (-2))) (BApp (Pred "element_of") (Free (-1)) (Free (-3)))
intersectionDef = LibraryEquivalence intersectionDefQZone [] (intersectionDefe, intersectionDefe')

-- IMPROVEMENT - for now we're storing this as an equivalence because the above code would be identical for an implication, but
-- need to clarify how we want either to work and implement separately.
-- Probably the most sensible way is to store equivalences as suggested, except with a set rather than a pair. Then appropriate function should take two indices giving which two expressions we want to exchange, and the appropriate substitution
-- then checks this is correct and performs equivalence on the desired expression. I guess we also want to specify the condition/hypothesis-mapping, but have the option for it to compute this manually?
-- we could trust that the substitution works if provided, but this would allow the function to create non-sound moves, so probably best not to do this.
-- Similarly, one way implications can just be stored as Tableau's, and we can implement library forward-reasoning and backward-reasoning separately in a similar way?
lesserThanTransQZone = Poset [QVar "Forall" (Just $ ExternalName "a") (-1)
    , QVar "Forall" (Just $ ExternalName "b") (-2)
    , QVar "Forall" (Just $ ExternalName "c") (-3)] []
lesserThanTransH1 = BApp (Pred "real_lesser_than") (Free (-1)) (Free (-2))
lesserThanTranse = BApp (Pred "real_lesser_than") (Free (-1)) (Free (-3))
lesserThanTranse' = BApp (Pred "real_leq") (Free (-2)) (Free (-3))
lesserThanTrans = LibraryEquivalence lesserThanTransQZone [lesserThanTransH1] (lesserThanTranse, lesserThanTranse')

-- Intersection of open sets is open
f1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "d") (1) $
    forall (Just $ ExternalName "U") (2) $
    forall (Just $ ExternalName "V") (3) $
    Implies (TAnd
        (BApp (Pred "metric_on") (Free 1) (Free 0))
        (TApp (Pred "open_in_metric") (Free 2) (Free 1) (Free 0))
        (TApp (Pred "open_in_metric") (Free 3) (Free 1) (Free 0))) $
    TApp (Pred "open_in_metric") (BApp (Operator "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
fQZone = Poset [] []
fBox = Box [] [(f1, [])]
fQBox = (fQZone, fBox)
fTab = Tableau fQZone [fBox]

Just fResult = 
    boxToTabMove (peelUniversalTargBox 0) 0 fTab >>= boxToTabMove (peelUniversalTargBox 0) 0 >>= boxToTabMove (peelUniversalTargBox 0) 0 >>= boxToTabMove (peelUniversalTargBox 0) 0 >>= tidyImplInTarg 0 0 >>= boxToTabMove (tidyAndInHypBox 0) 0 >>= boxToTabMove (tidyAndInHypBox 0) 0
    >>= boxToTabMove (matchLibraryEquivalenceTargBox openSetDefinition 0) 0 >>= boxToTabMove (matchLibraryEquivalenceHypBox openSetDefinition 1) 0 >>= boxToTabMove (matchLibraryEquivalenceHypBox openSetDefinition 2) 0
    >>= boxToTabMove (peelUniversalTargBox 0) 0 >>= tidyImplInTarg 0 0 >>= boxToTabMove (peelExistentialTargBox 0) 0 >>= boxToTabMove (tidyAndInTargBox 0) 0 >>= boxToTabMove (peelUniversalTargBox 1) 0 >>= tidyImplInTarg 1 0 >>= tidyImplInTarg 0 1
    >>= boxToTabMove (matchLibraryEquivalenceTargBox intersectionDef 0) 1 >>= boxToTabMove (matchLibraryEquivalenceHypBox intersectionDef 3) 1 >>= boxToTabMove (tidyAndInHypBox 3) 1 >>= boxToTabMove (tidyAndInTargBox 0) 1
    >>= boxToTabMove (modusPonensBox 1 6) 1 >>= boxToTabMove (modusPonensBox 2 3) 1 >>= boxToTabMove (peelExistentialHypBox 7) 1 >>= boxToTabMove (peelExistentialHypBox 8) 1 >>= boxToTabMove (tidyAndInHypBox 7) 1 >>= boxToTabMove (tidyAndInHypBox 8) 1
    >>= boxToTabMove (modusPonensBox 9 4) 1 >>= boxToTabMove (backwardsReasoningHypBox 11 1) 1
    >>= boxToTabMove (modusPonensBox 10 4) 1 >>= boxToTabMove (backwardsReasoningHypBox 12 0) 1
    >>= boxToTabMove (matchLibraryEquivalenceTargBox lesserThanTrans 0) 1 >>= boxToTabMove (matchLibraryEquivalenceTargBox lesserThanTrans 1) 1

at1 = exists (Just $ ExternalName "x") 0 (forall (Just $ ExternalName "y") 0 (exists (Just $ ExternalName "z") 1 (Eq (Free 0) (Free 1))))
aBox = Box [] [(at1, [])]
aHead = Poset [] []
aQBox = (aHead, aBox)
Just aResult = (peelExistentialTargBox 0) aQBox >>= (peelUniversalTargBox 0) >>= (peelExistentialTargBox 0)
aStr = pprintQBox aResult


-- Universal modus ponens with hyp
bh1 = forall (Just $ ExternalName "x") 0 $
    Implies (Eq (UApp (Operator "succ") (Free 0)) (Con (Obj "1"))) (Eq (Free 0) (Con (Obj "0")))

bh2= Eq (UApp (Operator "succ") (Free 1)) (Con (Obj "1"))

bTestHead = Poset [QVar "Forall" (Just $ ExternalName "y") 1] []
bTestBox = Box [(bh1, []), (bh2, [QVar "Forall" (Just $ ExternalName "y") 1])] []
bTestQBox = (bTestHead, bTestBox)
Just bResult = modusPonensBox 0 1 bTestQBox
bBeforeStr = pprintQBox bTestQBox
bStr = pprintQBox bResult


-- Implication in target tidy
ct1 = Implies (Eq (UApp (Operator "succ") (Free 0)) (UApp (Operator "succ") (Free 1))) (Eq (Free 0) (Free 1))
cTestHead = Poset [QVar "Forall" (Just $ ExternalName "x") 0, QVar "Forall" (Just $ ExternalName "y") 1] []
cTestBox = Box [] [(ct1, [QVar "Forall" (Just $ ExternalName "x") 0, QVar "Forall" (Just $ ExternalName "y") 1])]
cTestQBox = (cTestHead, cTestBox)
cTestTab = Tableau cTestHead [cTestBox]
Just cResult = tidyImplInTarg 0 0 cTestTab
cStr = pprintTab cResult