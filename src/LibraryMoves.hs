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
libEquivTargCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivTargCondMap (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap targBoxNumber targInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        targExpr <- getPureTarg targBoxNumber targInd tab
        let e = equivalents !! originalEquivalentInd
            e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e targExpr
        let hypIndsWithConds = map (\(condInd, hypInd) -> (hypInd, conditions!!condInd)) condMap
        (hypsWithConds, deepestBox) <- getHypsWithData hypIndsWithConds tab
        guard $ isPrefix deepestBox targBoxNumber
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds

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
        updatePureTarg targBoxNumber targInd newTarg tab

libEquivHypCondMap :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivHypCondMap (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap hypBoxNumber hypInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp hypBoxNumber hypInd tab
        let e = equivalents !! originalEquivalentInd
            e' = equivalents !! newEquivalentInd
        initialSub <- matchExpressions e hypExpr
        let hypIndsWithConds = map (\(condInd, hypInd) -> (hypInd, conditions!!condInd)) condMap
        (hypsWithConds, deepestBox) <- getHypsWithData hypIndsWithConds tab
        guard $ isPrefix deepestBox hypBoxNumber
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds

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
        updateHyp hypBoxNumber hypInd newHyp tab


-- Allows the specification of both the condition map and the substitution we want. Function verifies that the substitution is legitimate
libEquivTargFull :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> Substitution -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivTargFull (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap substitution
    targBoxNumber targInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        targExpr <- getPureTarg targBoxNumber targInd tab
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr
        (hypsWithConds, deepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix targBoxNumber deepestBox
        guard $ all (\(hyp, cond) -> Just hyp == holeExprToExpr (applySubstitution substitution cond)) hypsWithConds
        
        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updatePureTarg targBoxNumber targInd newTarg tab

-- Allows the specification of both the condition map and the substitution we want. Function verifies that the substitution is legitimate
libEquivHypFull :: LibraryEquivalence -> (Int, Int) -> [(Int, (BoxNumber, Int))] -> Substitution -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivHypFull (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) condMap substitution
    hypBoxNumber hypInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents
        || any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        hypExpr <- getHyp hypBoxNumber hypInd tab
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr
        (hypsWithConds, deepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypBoxNumber deepestBox
        guard $ all (\(hyp, cond) -> Just hyp == holeExprToExpr (applySubstitution substitution cond)) hypsWithConds
        
        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp hypBoxNumber hypInd newHyp tab


-- Allows the specification of the substitution without that of the condition map.
libEquivTargSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivTargSub (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) substitution
    targBoxNumber targInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        targExpr <- getPureTarg targBoxNumber targInd tab
        subedTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedTarg == targExpr

        let maybeSubedConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust maybeSubedConditions
        let subedConditions = catMaybes maybeSubedConditions

        let deepestBoxes = checkHypsExistCompatibly subedConditions tab
        guard $ any (isPrefix targBoxNumber) deepestBoxes

        newTarg <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updatePureTarg targBoxNumber targInd newTarg tab


libEquivHypSub :: LibraryEquivalence -> (Int, Int) -> Substitution -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivHypSub (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd) substitution
    hypBoxNumber hypInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        hypExpr <- getHyp hypBoxNumber hypInd tab
        subedHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! originalEquivalentInd)
        guard $ subedHyp == hypExpr

        let maybeSubedConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust maybeSubedConditions
        let subedConditions = catMaybes maybeSubedConditions

        let deepestBoxes = checkHypsExistCompatibly subedConditions tab
        guard $ any (isPrefix hypBoxNumber) deepestBoxes

        newHyp <- holeExprToExpr $ applySubstitution substitution (equivalents !! newEquivalentInd)
        updateHyp hypBoxNumber hypInd newHyp tab


libEquivTarg :: LibraryEquivalence -> (Int, Int) -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivTarg (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd)
    targBoxNumber targInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        targExpr <- getPureTarg targBoxNumber targInd tab
        initialSub <- matchExpressions e targExpr -- Match the suggested equivalence with the suggested target
        -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
        hyps <- getHypsUsableInBoxNumber targBoxNumber rootBox
        let condSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

        -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
        let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
        guard $ (not . null) possibleSubs

        let (sub:_) = possibleSubs
        newTarg <- holeExprToExpr $ applySubstitution sub e'
        updatePureTarg targBoxNumber targInd newTarg tab


-- IMPROVEMENT - should we prevent the hypothesis which will be matched from being one of the conditions? Not really, but what's happened if so? Guess this can't really happen?
libEquivHyp :: LibraryEquivalence -> (Int, Int) -> BoxNumber -> Int -> Tableau -> Maybe Tableau
libEquivHyp (LibraryEquivalence libQZone conditions equivalents)
    (originalEquivalentInd, newEquivalentInd)
    hypBoxNumber hypInd tab@(Tableau qZone rootBox)
    | originalEquivalentInd < 0 || originalEquivalentInd >= length equivalents || newEquivalentInd < 0 || newEquivalentInd >= length equivalents = Nothing
    | otherwise = do
        let e = equivalents !! originalEquivalentInd
        let e' = equivalents !! newEquivalentInd
        hypExpr <- getHyp hypBoxNumber hypInd tab
        initialSub <- matchExpressions e hypExpr -- Match the suggested equivalence with the suggested target
        -- Now we need to ensure all conditions in the result can match to a hypothesis consistently
        hyps <- getHypsUsableInBoxNumber hypBoxNumber rootBox
        let condSubs = map fst $ findConsistentSubs (zip [0..] conditions) (zip [0..] hyps)

        -- IMPROVEMENT - Currently gives multiple, but actually isn't the substitution forced by the target? Not sure, for now will just take the head if it exists
        let possibleSubs = mapMaybe (mergeSubstitutions initialSub) condSubs
        guard $ (not . null) possibleSubs

        let (sub:_) = possibleSubs
        newHyp <- holeExprToExpr $ applySubstitution sub e'
        updateHyp hypBoxNumber hypInd newHyp tab


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
libForwardReasoningFull:: LibraryImplication -> [(Int, (BoxNumber, Int))] -> Substitution -> Tableau -> Maybe Tableau
libForwardReasoningFull (LibraryImplication libQZone conditions consequents)
    condMap substitution tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        let hypIndsWithConds = map (\(condInd, (hypBoxNumber, hypInd)) -> ((hypBoxNumber, hypInd), conditions!!condInd)) condMap
        (hypsWithConds, deepestBoxNumber) <- getHypsWithData hypIndsWithConds tab
        guard $ all (\(hyp, cond) -> holeExprToExpr (applySubstitution substitution cond) == Just hyp) hypsWithConds

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

libForwardReasoningCondMap :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> Tableau -> Maybe Tableau
libForwardReasoningCondMap (LibraryImplication libQZone conditions consequents)
    condMap tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap = Nothing
    | otherwise = do
        let hypIndsWithConds = map (\(condInd, (hypBoxNumber, hypInd)) -> ((hypBoxNumber, hypInd), conditions!!condInd)) condMap
        (hypsWithConds, deepestBoxNumber) <- getHypsWithData hypIndsWithConds tab
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConds
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
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

libForwardReasoningSub :: LibraryImplication -> Substitution -> Tableau -> Maybe Tableau
libForwardReasoningSub (LibraryImplication libQZone conditions consequents)
    substitution tab@(Tableau qZone rootBox) = do
        let subedMaybeConditions = map (holeExprToExpr . applySubstitution substitution) conditions
        guard $ all isJust subedMaybeConditions

        let subedConditions = catMaybes subedMaybeConditions
        let deepestBoxNumbers = checkHypsExistCompatibly subedConditions tab
        guard $ not $ null deepestBoxNumbers
        let (deepestBoxNumber:_) = sortBy (\a b -> length a `compare` length b) deepestBoxNumbers

        let subedConsequents = mapMaybe (holeExprToExpr . applySubstitution substitution) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab

libForwardReasoning :: LibraryImplication -> Tableau -> Maybe Tableau
libForwardReasoning (LibraryImplication libQZone conditions consequents) tab@(Tableau qZone rootBox) = let
    findAllPossibleSubs :: Substitution -> [HoleExpr] -> [Expr] -> [(Substitution, ([HoleExpr], [Expr]))]
    findAllPossibleSubs startSub condsToMatch hyps = let
        trivialSub = (startSub, (condsToMatch, hyps))
        allCombinations = catMaybes [case matchExpressions cond hyp of
            Just sub -> Just (sub, (filter (/=cond) condsToMatch, filter (/=hyp) hyps))
            Nothing -> Nothing
            | cond <- condsToMatch, hyp <- hyps]
        filteredCombinations = mapMaybe (\(s, b) -> case mergeSubstitutions s startSub of
            Just newSub -> Just (newSub, b)
            Nothing -> Nothing) allCombinations
        finalCombinations = map (\(sub, (holeExprs, exprs)) -> (sub, (map (applySubstitution sub) holeExprs, exprs))) filteredCombinations
        futurePossibilities = concatMap (\(s, (a, b)) -> findAllPossibleSubs s a b) finalCombinations
        in nub $ trivialSub:futurePossibilities
    
    exploreTree :: Substitution -> [HoleExpr] -> BoxNumber -> BoxZipper Expr -> [(Substitution, BoxNumber)]
    exploreTree currentSub [] currentBoxNumber _ = [(currentSub, currentBoxNumber)]
    exploreTree currentSub condsToMatch currentBoxNumber boxZipper@(Box hyps targs, _) = do
        (newSub, (newConds, _)) <- findAllPossibleSubs currentSub condsToMatch hyps
        if null newConds then [(newSub, currentBoxNumber)]
        else do
            (BoxTarg boxTarg, targInd) <- zip targs [0..]
            let newBoxNumber = currentBoxNumber++[targInd]
            case toBoxNumberFromZipper [targInd] boxZipper of
                Just newBoxZipper -> exploreTree newSub newConds newBoxNumber newBoxZipper
                Nothing -> []
    
    in do
        let possibleSolutions = exploreTree [] conditions [] (rootBox, [])
        guard $ not $ null possibleSolutions
        let ((finalSub, deepestBoxNumber):_) = sortBy (\a b -> snd a `compare` snd b) possibleSolutions
            subedConsequents = mapMaybe (holeExprToExpr . applySubstitution finalSub) consequents
        addHyps (zip (repeat deepestBoxNumber) subedConsequents) tab




-- <<< BACKWARD REASONING >>>

-- Specify condMap (telling us which conditions map to which hypotheses - this will be missing some conditions, which are precisely the conditions that will become the new target)
-- along with a targMap (telling us which consequents map to which targets - not all consequents need a match)
-- and finally a substitution which gives the library-problem analogy
-- then performs backwards reasoning by replacing the matched targets with the missing conditions from the library statement
libBackwardReasoningFull :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> [(Int, (BoxNumber, Int))] -> Substitution -> Tableau -> Maybe Tableau
libBackwardReasoningFull (LibraryImplication libQZone conditions consequents)
    condMap targMap substitution tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length consequents) . fst) targMap = Nothing
    | otherwise = do
        (targsWithConsequents, targsShallowestBox) <- getTargsWithData (map (\(consInd, b) -> (b, consequents!!consInd)) targMap) tab
        (hypsWithConditions, hypsDeepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypsDeepestBox targsShallowestBox
        guard $ all (\(targ, cons) -> holeExprToExpr (applySubstitution substitution cons) == Just targ) targsWithConsequents
        guard $ all (\(hyp, cond) -> holeExprToExpr (applySubstitution substitution cond) == Just hyp) hypsWithConditions

        let missingSubedMaybeConds = [holeExprToExpr $ applySubstitution substitution (conditions!!condInd) | condInd <- [0..length conditions-1], condInd `notElem` map fst condMap]
        guard $ all isJust missingSubedMaybeConds

        let missingSubedConds = catMaybes missingSubedMaybeConds
        let targIndsToRemove = map snd targMap
        removePureTargs targIndsToRemove tab >>= addPureTargs (zip (repeat targsShallowestBox) missingSubedConds)

-- Only need to specify condMap and targMap
libBackwardReasoningCondMapTargMap :: LibraryImplication -> [(Int, (BoxNumber, Int))] -> [(Int, (BoxNumber, Int))] -> Tableau -> Maybe Tableau
libBackwardReasoningCondMapTargMap (LibraryImplication libQZone conditions consequents)
    condMap targMap tab@(Tableau qZone rootBox)
    | any ((\i -> i < 0 || i >= length conditions) . fst) condMap || any ((\i -> i < 0 || i >= length consequents) . fst) targMap = Nothing
    | otherwise = do
        (targsWithConsequents, targsShallowestBox) <- getTargsWithData (map (\(consInd, b) -> (b, consequents!!consInd)) targMap) tab
        (hypsWithConditions, hypsDeepestBox) <- getHypsWithData (map (\(condInd, b) -> (b, conditions!!condInd)) condMap) tab
        guard $ isPrefix hypsDeepestBox targsShallowestBox
        let subs = map (\(hyp, cond) -> matchExpressions cond hyp) hypsWithConditions ++ map (\(targ, cons) -> matchExpressions cons targ) targsWithConsequents

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
        removePureTargs targIndsToRemove tab >>= addPureTargs (zip (repeat targsShallowestBox) missingSubedConds)

{-
-- Only need to specify the desired substitution. Will replace as many targets as possible with as few conditions as possible
libBackwardReasoningSub :: LibraryImplication -> Substitution -> Tableau -> Maybe Tableau
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
libBackwardReasoning :: LibraryImplication -> Tableau -> Maybe Tableau
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
            if null futureStates then return ((labelledConds, labelledHyps), newSub)
            else futureStates
    
    let validConsequentSubs = catMaybes [matchExpressions consequent targ | consequent <- consequents, targ <- targs]
    guard $ not (null validConsequentSubs)
    let possibleCondSubs = concatMap (exploreSubstitutionTree (zip [0..] conditions) (zip [0..] hyps)) [[]]
    let bestVal = minimum $ map (length . fst . fst) possibleCondSubs
    let bestCondSubs = map snd $ filter ((==bestVal) . length . fst . fst) possibleCondSubs

    let possibleConsequentSubs = concatMap (exploreSubstitutionTree (zip [0..] consequents) (zip [0..] targs)) bestCondSubs
    let bestVal = minimum $ map (length . fst . fst) possibleConsequentSubs
    let bestConsSubs = map snd $ filter ((==bestVal) . length . fst . fst) possibleConsequentSubs
    
    guard $ not (null bestConsSubs)
    let (sub:_) = bestConsSubs
    libBackwardReasoningSub libImpl sub qBox

-}