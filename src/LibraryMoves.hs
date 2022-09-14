{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use zipWith" #-}
module LibraryMoves where

import Lib
import TableauFoundation
import Poset
import BasicMoves
import Data.Maybe
import Data.List
import Control.Monad
import PPrinting
import HoleExpr
import Debug.Trace


-- A list of conditions under which the equivalences hold, and a list of statements which are equivalent (equivalents).
data LibraryEquivalence = LibraryEquivalence QZone [HoleExpr] [HoleExpr]

-- Basically just a QBox. A list of hypotheses and then a list of conclusions which hold under the hypotheses.
-- IMPROVEMENT - could we need multiple QBoxes, as with a Tableau?
data LibraryImplication = LibraryImplication QZone [HoleExpr] [HoleExpr]



-- <<< EQUIVALENCES >>>

-- Condition map given by list of pairs (i, j) which specify that condition i is mapped to hypothesis j
libEquivTargCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, Int)] -> Int -> QBox -> Maybe QBox
libEquivTargCondMap (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) condMap targInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        targExpr <- getTarg targInd targs
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e targExpr
        let conditionsAndHyps = zip (map ((conditions!!) . fst) condMap) (map ((hyps !!) . snd) condMap) -- This should never error because we guard against the out-of-bounds case above
        let subs = map (uncurry matchExpressions) conditionsAndHyps

        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just initialSub) subs
        finalSub <- finalSubMaybe
        newTarg <- holeExprToExpr $ applySubstitution finalSub e'
        updateTarg targInd newTarg qBox

libEquivHypCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, Int)] -> Int -> QBox -> Maybe QBox
libEquivHypCondMap (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) condMap hypInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp hypInd hyps
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e hypExpr
        let conditionsAndHyps = zip (map ((conditions!!) . fst) condMap) (map ((hyps !!) . snd) condMap) -- This should never error because we guard against the out-of-bounds case above
        let subs = map (uncurry matchExpressions) conditionsAndHyps

        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just initialSub) subs
        finalSub <- finalSubMaybe
        newHyp <- holeExprToExpr $ applySubstitution finalSub e'
        updateHyp hypInd newHyp qBox


-- Allows the specification of both the condition map and the substitution we want. Function verifies that the substitution is legitimate
libEquivTargFull :: LibraryEquivalence -> (Int, Int) -> [(Int, Int)] -> Substitution -> Int -> QBox -> Maybe QBox
libEquivTargFull (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) condMap substitution targInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        targExpr <- getTarg targInd targs
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr

        let subedConditions = mapMaybe (holeExprToExpr . applySubstitution substitution . (conditions!!) . fst) condMap  -- This should never error because we guard against the out-of-bounds case above
        let chosenHyps = map ((hyps !!) . snd) condMap
        guard $ subedConditions == chosenHyps

        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateTarg targInd newTarg qBox

libEquivHypFull :: LibraryEquivalence -> (Int, Int) -> [(Int, Int)] -> Substitution -> Int -> QBox -> Maybe QBox
libEquivHypFull (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) condMap substitution hypInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp hypInd hyps
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr

        let subedConditions = mapMaybe (holeExprToExpr . applySubstitution substitution . (conditions!!) . fst) condMap  -- This should never error because we guard against the out-of-bounds case above
        let chosenHyps = map ((hyps !!) . snd) condMap
        guard $ subedConditions == chosenHyps

        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp hypInd newHyp qBox

-- Allows the specification of the substitution without that of the condition map.
libEquivTargSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> Int -> QBox -> Maybe QBox
libEquivTargSub (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) substitution targInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        targExpr <- getTarg targInd targs
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr

        let a = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust a

        let subedConditions = catMaybes a
        guard $ all (`elem` hyps) subedConditions -- No need to worry about multiset nonsense

        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateTarg targInd newTarg qBox

libEquivHypSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> Int -> QBox -> Maybe QBox
libEquivHypSub (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) substitution hypInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        hypExpr <- getHyp hypInd hyps
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr

        let a = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust a

        let subedConditions = catMaybes a
        guard $ all (`elem` hyps) subedConditions -- No need to worry about multiset nonsense

        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp hypInd newHyp qBox

-- Takes a library equivalence and a QBox and applies the library equivalence to the i-th target
libEquivTarg :: LibraryEquivalence -> (Int, Int) -> Int -> QBox -> Maybe QBox
libEquivTarg (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) targInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        targExpr <- getTarg targInd targs
        initialSub <- matchExpressions e targExpr -- Match the suggested equivalence with the suggested target
        -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
        let condSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

        -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
        let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
        guard $ (not . null) possibleSubs

        let (sub:_) = possibleSubs
        newTarg <- holeExprToExpr $ applySubstitution sub e'
        updateTarg targInd newTarg qBox


-- IMPROVEMENT - should we prevent the hypothesis which will be matched from being one of the conditions? Not really, but what's happened if so? Guess this can't really happen?
libEquivHyp :: LibraryEquivalence -> (Int, Int) -> Int -> QBox -> Maybe QBox
libEquivHyp (LibraryEquivalence libQZone conditions equivalents) (originalEquivalentInd, newEquivalentInd) hypInd qBox@(qZone, Box hyps targs)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        hypExpr <- getHyp hypInd hyps
        initialSub <- matchExpressions e hypExpr -- Match the suggested equivalence with the suggested target
        -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
        let condSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

        -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
        let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
        guard $ (not . null) possibleSubs

        let (sub:_) = possibleSubs
        newHyp <- holeExprToExpr $ applySubstitution sub e'
        updateHyp hypInd newHyp qBox


-- Finds consistent substitutions (if any exists). We also specify the way hypotheses were matched to one another
findConsistentSubs :: [(Int, HoleExpr)] -> [(Int, Expr)] -> [(Substitution, [(Int, Int)])]
findConsistentSubs [] _ = [([], [])]
findConsistentSubs conds@((condIndex, h1):remainingConds) labelledHypExprs
    | length conds > length labelledHypExprs = []
    | otherwise =
        let possibleH1Subs = mapMaybe (\(i, e) -> case (i, matchExpressions h1 e) of
                (n, Just sub) -> Just (n, sub)
                (n, Nothing) -> Nothing) labelledHypExprs

            -- Takes a substitution, and the hypothesis-index which has been matched
            -- along with the old conditions and old hypotheses, then generates a new set of
            -- conditions and hypotheses formed by removing the hypothesis/condition and substiuting as appropriate
            generateNewProblem :: [(Int, HoleExpr)] -> [(Int, Expr)] -> (Int, Substitution) -> ([(Int, HoleExpr)], [(Int, Expr)])
            generateNewProblem [] _ _ = ([], []) -- This pattern should never be matched because the empty condition case is dealt with
            -- There should never be more conditions than hypotheses because this is guarded out initially
            generateNewProblem (_:newCondsPreSub) oldLabelledHyps (ij, sj) =
                -- Do all the substitutions and get rid of first condition and relevant, ij-th, hyp
                let newLabelledHyps = filter (\(n, exp) -> n /= ij) oldLabelledHyps
                    newConds = map (\(n, exp) -> (n, applySubstitution sj exp)) newCondsPreSub
                in (newConds, newLabelledHyps)

            -- These are the remaining problems to solve. We store them as pairs, the first part reprsenting the substitution done (given by a substitution and the hypothesis-index matched)
            -- The second part reprsenting the remaining problem after applying that substitution.
            remainingProblems = map (\s -> (s, generateNewProblem conds labelledHypExprs s)) possibleH1Subs

            -- This takes a remaining problem, recursively finds the solution, and combines it with the initial substitution to give us the final result
            findFutureCombinedSolutions :: ((Int, Substitution), ([(Int, HoleExpr)], [(Int, Expr)])) -> [(Substitution, [(Int, Int)])]
            findFutureCombinedSolutions newProblem =
                let ((i1, s1), (newConds, newLabelledHyps)) = newProblem
                    futureSolutions = findConsistentSubs newConds newLabelledHyps
                    combinedFutureSolutions = mapMaybe (\(s, mapping) -> case mergeSubstitutions s1 s of
                        Just sub -> Just (sub, (condIndex, i1):mapping)
                        _ -> Nothing) futureSolutions
                in combinedFutureSolutions

        -- The final result can be obtained from any of the remainingProblems we generated, thus we need to concatMap.
        in concatMap findFutureCombinedSolutions remainingProblems





-- <<< FORWARD REASONING >>>

-- If the conditions for a given library implication are present as hypotheses, we can deduce the consequences as new hypotheses
libForwardReasoningFull:: LibraryImplication -> [(Int, Int)] -> Substitution -> QBox -> Maybe QBox
libForwardReasoningFull (LibraryImplication libQZone conditions consequents) condMap substitution qBox@(qZone, Box hyps targs)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        let subedConditions = mapMaybe (holeExprToExpr . applySubstitution substitution . (conditions!!) . fst) condMap  -- This should never error because we guard against the out-of-bounds case above
        let chosenHyps = map ((hyps !!) . snd) condMap
        guard $ subedConditions == chosenHyps

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        foldl' (\maybeQBox consequent -> case maybeQBox of
            Just something -> addHyp consequent something
            _ -> Nothing) (Just qBox) subedConsequents

libForwardReasoningCondMap :: LibraryImplication -> [(Int, Int)] -> QBox -> Maybe QBox
libForwardReasoningCondMap (LibraryImplication libQZone conditions consequents) condMap qBox@(qZone, Box hyps targs)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap = Nothing
    | otherwise = do
        let conditionsAndHyps = zip (map ((conditions!!) . fst) condMap) (map ((hyps !!) . snd) condMap) -- This should never error because we guard against the out-of-bounds case above
        let subs = map (uncurry matchExpressions) conditionsAndHyps
        guard $ all isJust subs
        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just []) subs
        finalSub <- finalSubMaybe

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution finalSub) consequents
        foldl' (\maybeQBox consequent -> case maybeQBox of
            Just something -> addHyp consequent something
            _ -> Nothing) (Just qBox) subedConsequents

libForwardReasoningSub :: LibraryImplication -> Substitution -> QBox -> Maybe QBox
libForwardReasoningSub (LibraryImplication libQZone conditions consequents) substitution qBox@(qZone, Box hyps targs) = do
        let subedMaybeConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust subedMaybeConditions

        let subedConditions = catMaybes subedMaybeConditions
        guard $ all (`elem` hyps) subedConditions -- No need to worry about multiset nonsense, because condition repeated twice is meaningless

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        foldl' (\maybeQBox consequent -> case maybeQBox of
            Just something -> addHyp consequent something
            _ -> Nothing) (Just qBox) subedConsequents

libForwardReasoning :: LibraryImplication -> QBox -> Maybe QBox
libForwardReasoning (LibraryImplication libQZone conditions consequents) qBox@(qZone, Box hyps targs) = do
    let possibleSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

    guard $ (not . null) possibleSubs

    let (substitution:_) = possibleSubs
    let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
    foldl' (\maybeQBox consequent -> case maybeQBox of
        Just something -> addHyp consequent something
        _ -> Nothing) (Just qBox) subedConsequents




-- <<< BACKWARD REASONING >>>

-- Specify condMap (telling us which conditions map to which hypotheses - this will be missing some conditions, which are precisely the conditions that will become the new target)
-- along with a targMap (telling us which consequents map to which targets - not all consequents need a match)
-- and finally a substitution which gives the library-problem analogy
-- then performs backwards reasoning by replacing the matched targets with the missing conditions from the library statement
libBackwardReasoningFull :: LibraryImplication -> [(Int, Int)] -> [(Int, Int)] -> Substitution -> QBox -> Maybe QBox
libBackwardReasoningFull (LibraryImplication libQZone conditions consequents) condMap targMap substitution qBox@(qZone, Box hyps targs)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap
        || any ((\i -> i < 0 || i >= length consequents) . fst) targMap || any ((\i -> i < 0 || i >= length targs) . snd) targMap = Nothing
    | otherwise = do
        let chosenSubedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution . (consequents!!) . fst) targMap  -- This should never error because we guard against the out-of-bounds case above
        let chosenTargs = map ((targs !!) . snd) targMap
        guard $ chosenSubedConsequents == chosenTargs

        let chosenSubedConds = mapMaybe (holeExprToExpr . applySubstitution substitution . (conditions!!) . fst) condMap
        let chosenHyps = map ((hyps !!) . snd) condMap
        guard $ chosenSubedConds == chosenHyps

        let missingSubedMaybeConds = [holeExprToExpr $ applySubstitution substitution (conditions!!condInd) | condInd <- [0..length conditions-1], condInd `notElem` map fst condMap]
        guard $ all isJust missingSubedMaybeConds

        let missingSubedConds = catMaybes missingSubedMaybeConds
        let targIndsToRemove = map snd targMap
        removeTargs targIndsToRemove qBox >>= addTargs missingSubedConds

-- Only need to specify condMap and targMap
libBackwardReasoningCondMapTargMap :: LibraryImplication -> [(Int, Int)] -> [(Int, Int)] -> QBox -> Maybe QBox
libBackwardReasoningCondMapTargMap (LibraryImplication libQZone conditions consequents) condMap targMap qBox@(qZone, Box hyps targs)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length hyps) . snd) condMap
        || any ((\i -> i < 0 || i >= length consequents) . fst) targMap || any ((\i -> i < 0 || i >= length targs) . snd) targMap = Nothing
    | otherwise = do
        let conditionsAndHyps = zip (map ((conditions!!) . fst) condMap) (map ((hyps !!) . snd) condMap) -- This should never error because we guard against the out-of-bounds case above
        let consequentsAndTargs = zip (map ((consequents!!) . fst) targMap) (map ((targs !!) . snd) targMap)
        let subs = map (uncurry matchExpressions) conditionsAndHyps ++ map (uncurry matchExpressions) consequentsAndTargs

        let -- Attempt to merge substitutions
            foldFunction :: Maybe Substitution -> Maybe Substitution -> Maybe Substitution
            foldFunction subA subB = do
                a <- subA
                b <- subB
                mergeSubstitutions a b
            finalSubMaybe = foldl' foldFunction (Just []) subs
        finalSub <- finalSubMaybe
        
        let missingSubedMaybeConds = [holeExprToExpr $ applySubstitution finalSub (conditions!!condInd) | condInd <- [0..length conditions-1], condInd `notElem` map fst condMap]
        guard $ all isJust missingSubedMaybeConds
        let missingSubedConds = catMaybes missingSubedMaybeConds
        let targIndsToRemove = map snd targMap
        removeTargs targIndsToRemove qBox >>= addTargs missingSubedConds

-- Only need to specify the desired substitution. Will replace as many targets as possible with as few conditions as possible
libBackwardReasoningSub :: LibraryImplication -> Substitution -> QBox -> Maybe QBox
libBackwardReasoningSub (LibraryImplication libQZone conditions consequents) substitution qBox@(qZone, Box hyps targs) = do
    let subedMaybeConditions = map (holeExprToExpr . applySubstitution substitution) conditions
    guard $ all isJust subedMaybeConditions
    let subedConditions = catMaybes subedMaybeConditions

    let subedMaybeConsequents = map (holeExprToExpr . applySubstitution substitution) consequents
    guard $ all isJust subedMaybeConsequents
    let subedConsequents = catMaybes subedMaybeConsequents

    -- Find as many targets which are consequents as possible - these will be removed
    let targIndsToRemove = [targInd | (targInd, targ) <- zip [(0::Int)..] targs, targ `elem` subedConsequents]

    -- Find the conditions missing as hypotheses - these will replace the removed targets
    let missingSubedConds = [subedCond | subedCond <- subedConditions, subedCond `notElem` hyps]

    removeTargs targIndsToRemove qBox >>= addTargs missingSubedConds


-- No need to specify anything. Will ensure that at least one target is matched (otherwise move fails).
-- Subject to this, will find the substitution minimising the number of missing conditions THEN maximising the number of targets matched
-- IMPROVEMENT - think about this, perhaps it's not always the correct approach (though obviously is if there are no conditions missing - an important case)
libBackwardReasoning :: LibraryImplication -> QBox -> Maybe QBox
libBackwardReasoning libImpl@(LibraryImplication libQZone conditions consequents) qBox@(qZone, Box hyps targs) = do
    let
        exploreSubstitutionTree :: [(Int, HoleExpr)] -> [(Int, Expr)] -> Substitution -> [(([(Int, HoleExpr)], [(Int, Expr)]), Substitution)]
        exploreSubstitutionTree labelledConds labelledHyps previousSub = do
            (condInd, cond) <- labelledConds
            (hypInd, hyp) <- labelledHyps
            let subMaybe = matchExpressions cond hyp
            guard $ isJust subMaybe
            let Just sub = subMaybe
            guard $ isJust (mergeSubstitutions previousSub sub)
            let Just newSub = mergeSubstitutions previousSub sub
            let newState = (filter (\(i, _) -> i /= condInd) labelledConds
                            , filter (\(i, _) -> i /= hypInd) labelledHyps)
            let futureStates = uncurry exploreSubstitutionTree newState newSub
            if null futureStates then return ((labelledConds, labelledHyps), previousSub)
            else futureStates
    
    let validConsequentSubs = catMaybes [matchExpressions consequent targ | consequent <- consequents, targ <- targs]
    guard $ not (null validConsequentSubs)
    let possibleCondSubs = concatMap (exploreSubstitutionTree (zip [0..] conditions) (zip [0..] hyps)) validConsequentSubs
    let bestVal = minimum $ map (length . fst . fst) possibleCondSubs
    let bestCondSubs = map snd $ filter ((==bestVal) . length . fst . fst) possibleCondSubs

    let possibleConsequentSubs = concatMap (exploreSubstitutionTree (zip [0..] consequents) (zip [0..] targs)) bestCondSubs
    let bestVal = minimum $ map (length . fst . fst) possibleConsequentSubs
    let bestConsSubs = map snd $ filter ((==bestVal) . length . fst . fst) possibleConsequentSubs
    
    guard $ not (null bestConsSubs)
    let (sub:_) = bestConsSubs
    libBackwardReasoningSub libImpl sub qBox

