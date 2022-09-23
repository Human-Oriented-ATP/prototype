{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}

module BasicMoves where

import Data.Maybe
import Data.List
import Control.Monad
import Debug.Trace

import Lib
import TableauFoundation
import Poset
import PPrinting
import HoleExpr

-- <<< FOUNDATIONAL CODE >>>

-- Takes a Tableau and returns an updated Tableau. Again, Maybe because the move could fail.
type Move = Tableau -> Maybe Tableau

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



addHyp :: BoxNumber -> Expr -> Tableau -> Maybe Tableau
addHyp boxNumber hyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addHypToZipper hyp boxZipper
    Just $ Tableau qZone (unzipBox newZipper)

addPureTarg :: BoxNumber -> Expr -> Tableau -> Maybe Tableau
addPureTarg boxNumber targ (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addPureTargToZipper targ boxZipper
    Just $ Tableau qZone (unzipBox newZipper)

addBoxTarg :: BoxNumber -> Box Expr -> Tableau -> Maybe Tableau
addBoxTarg boxNumber boxTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    let newZipper = addBoxTargToZipper boxTarg boxZipper
    Just $ Tableau qZone (unzipBox newZipper)


addHyps :: [(BoxNumber, Expr)] -> Tableau -> Maybe Tableau
addHyps addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddHyps :: [(BoxNumber, Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddHyps [] currentZipper = Just currentZipper
        followAndAddHyps ((direction, hyp):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addHypToZipper hyp newZipper
    
    addedHypsZipper <- followAndAddHyps boxRoute zippedBox
    let newRootBox = unzipBox addedHypsZipper
    Just $ Tableau qZone newRootBox


addPureTargs :: [(BoxNumber, Expr)] -> Tableau -> Maybe Tableau
addPureTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddPureTargs :: [(BoxNumber, Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddPureTargs [] currentZipper = Just currentZipper
        followAndAddPureTargs ((direction, pureTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addPureTargToZipper pureTarg newZipper
    
    addTargsZipper <- followAndAddPureTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    Just $ Tableau qZone newRootBox

addBoxTargs :: [(BoxNumber, Box Expr)] -> Tableau -> Maybe Tableau
addBoxTargs addSchedule (Tableau qZone rootBox) = do
    (boxRoute, _) <- boxNumbersToDirections addSchedule
    
    let zippedBox = (rootBox, [])
        followAndAddBoxTargs :: [(BoxNumber, Box Expr)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndAddBoxTargs [] currentZipper = Just currentZipper
        followAndAddBoxTargs ((direction, boxTarg):rest) currentZipper = do
            newZipper <- toBoxNumberFromZipper direction currentZipper
            Just $ addBoxTargToZipper boxTarg newZipper
    
    addTargsZipper <- followAndAddBoxTargs boxRoute zippedBox
    let newRootBox = unzipBox addTargsZipper
    Just $ Tableau qZone newRootBox



-- Removes hyps/targs. Should out-of-bounds index give unchanged or Nothing? Not sure yet.
-- IMPROVEMENT - think about whether out-of-bounds index should return unchanged or Nothing
removeHyp :: BoxNumber -> Int -> Tableau -> Maybe Tableau
removeHyp boxNumber hypInd (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeHypFromZipper hypInd boxZipper
    Just (Tableau qZone (unzipBox newBoxZipper))

removeTarg :: BoxNumber -> Int -> Tableau -> Maybe Tableau
removeTarg boxNumber targInd (Tableau qZone boxes) = do
    boxZipper <- toBoxNumberFromRoot boxNumber boxes
    newBoxZipper <- removeTargFromZipper targInd boxZipper
    Just (Tableau qZone (unzipBox newBoxZipper))

removeAllTargs :: BoxNumber -> Tableau -> Maybe Tableau
removeAllTargs boxNumber (Tableau qZone boxes) = do
    (Box hyps targs, crumbs) <- toBoxNumberFromRoot boxNumber boxes
    Just (Tableau qZone (unzipBox (Box hyps [], crumbs)))

-- Slightly more time-efficient solutions exist, but not sure the constant overhead is worth it?
{-
removeHyps :: BoxNumber -> [Int] -> Tableau -> Maybe Tableau
removeHyps [] qBox = Just qBox
removeHyps inds qBox@(qZone, Box hyps targs)
    | any (\i -> i < 0 || i >= length hyps) inds = Nothing
    | otherwise = removeHypsNoSort 0 (sort inds) qBox where
        removeHypsNoSort :: BoxNumber -> Int -> [Int] -> Tableau -> Maybe Tableau
        removeHypsNoSort counter inds qBox = do
            let (ind:rest) = inds
            newBox <- removeHyp (ind-counter) qBox
            removeHypsNoSort (counter+1) rest newBox

removeTargs :: BoxNumber -> [Int] -> Tableau -> Maybe Tableau
removeTargs [] qBox = Just qBox
removeTargs inds qBox@(qZone, Box hyps targs)
    | any (\i -> i < 0 || i >= length targs) inds = Nothing
    | otherwise = removeTargsNoSort 0 (sort inds) qBox where
        removeTargsNoSort :: BoxNumber -> Int -> [Int] -> Tableau -> Maybe Tableau
        removeTargsNoSort counter [ind] qBox = removeTarg (ind-counter) qBox
        removeTargsNoSort counter inds qBox = do
            let (ind:rest) = inds
            newBox <- removeTarg (ind-counter) qBox
            removeTargsNoSort (counter+1) rest newBox
-}

removeFromListMaybe :: [a] -> Int -> Maybe [a]
removeFromListMaybe l i
    | i < 0 || i <= length l = Nothing
    | otherwise = let
        (as, _:bs) = splitAt i l
        in Just $ as++bs

removeHyps :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removeHyps removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveHyps :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveHyps [] boxZipper = Just boxZipper
        followAndRemoveHyps ((boxNumber, hypInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            newHyps <- removeFromListMaybe hyps hypInd
            followAndRemoveHyps rest (Box newHyps targs, crumbs)
    finalZipper <- followAndRemoveHyps orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))

removePureTargs :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removePureTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = Just boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            PureTarg targ <- getFromListMaybe targs targInd
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))

removeBoxTargs :: [(BoxNumber, Int)] -> Tableau -> Maybe Tableau
removeBoxTargs removeSchedule tab@(Tableau qZone rootBox) = do
    (orderedRemoveSchedule, _) <- boxNumbersToDirectionsWithInt removeSchedule
    let
        followAndRemoveTargs :: [(BoxNumber, Int)] -> BoxZipper Expr -> Maybe (BoxZipper Expr)
        followAndRemoveTargs [] boxZipper = Just boxZipper
        followAndRemoveTargs ((boxNumber, targInd):rest) boxZipper = do
            (Box hyps targs, crumbs) <- toBoxNumberFromZipper boxNumber boxZipper
            BoxTarg targ <- getFromListMaybe targs targInd
            newTargs <- removeFromListMaybe targs targInd
            followAndRemoveTargs rest (Box hyps newTargs, crumbs)
    finalZipper <- followAndRemoveTargs orderedRemoveSchedule (rootBox, [])
    Just $ (Tableau qZone (unzipBox finalZipper))



updateHyp :: BoxNumber -> Int -> Expr -> Tableau -> Maybe Tableau
updateHyp boxNumber hypInd newHyp (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateHypInZipper hypInd newHyp boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)

updatePureTarg :: BoxNumber -> Int -> Expr -> Tableau -> Maybe Tableau
updatePureTarg boxNumber targInd newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updatePureTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)

updateBoxTarg :: BoxNumber -> Int -> Box Expr -> Tableau -> Maybe Tableau
updateBoxTarg boxNumber targInd newTarg (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    newBoxZipper <- updateBoxTargInZipper targInd newTarg boxZipper
    let newBox = unzipBox newBoxZipper
    Just (Tableau qZone newBox)


getFromListMaybe :: [a] -> Int -> Maybe a
getFromListMaybe l i
    | i < 0 || i >= length l = Nothing
    | otherwise = Just $ l!!i

getHyp :: BoxNumber -> Int -> Tableau -> Maybe Expr
getHyp boxNumber hypInd (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getHypInZipper hypInd boxZipper

getPureTarg :: BoxNumber -> Int -> Tableau -> Maybe Expr
getPureTarg boxNumber targInd (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getPureTargInZipper targInd boxZipper

getBoxTarg :: BoxNumber -> Int -> Tableau -> Maybe (Box Expr)
getBoxTarg boxNumber targInd (Tableau qZone rootBox) = do
    boxZipper <- toBoxNumberFromRoot boxNumber rootBox
    getBoxTargInZipper targInd boxZipper

-- Efficiently gets the list of hyps. Data is stored with each hyp, and this is preserved.
-- Also returns the deepest BoxNumber from the boxes
getHypsWithData :: [((BoxNumber, Int), a)] -> Tableau -> Maybe ([(Expr, a)], BoxNumber)
getHypsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, hypInd), dat) -> (boxNumber, (hypInd, dat))) getSchedule
    (directions, deepestBox) <- boxNumbersToDirections boxNumbersWithData
    let
        followAndGetHyps :: [(BoxNumber, (Int, a))] -> BoxZipper Expr -> Maybe [(Expr, a)]
        followAndGetHyps [] _ = Just []
        followAndGetHyps ((boxNumber, (hypInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            hyp <- getHypInZipper hypInd newBoxZipper
            otherHyps <- followAndGetHyps rest newBoxZipper
            Just ((hyp, dat):otherHyps)
    extractedHyps <- followAndGetHyps boxNumbersWithData (rootBox, [])
    Just (extractedHyps, deepestBox)

-- Returns the shallowest BoxNumber from the boxes. Reason being that shallower is worse for boxes, whereas deeper is worse for hyps.
getTargsWithData :: [((BoxNumber, Int), a)] -> Tableau -> Maybe ([(Expr, a)], BoxNumber)
getTargsWithData getSchedule tab@(Tableau qZone rootBox) = do
    let boxNumbersWithData = map (\((boxNumber, targInd), dat) -> (boxNumber, (targInd, dat))) getSchedule
    (directions, shallowestBox) <- boxNumbersToDirectionsFlipped boxNumbersWithData
    let
        followAndGetTargs :: [(BoxNumber, (Int, a))] -> BoxZipper Expr -> Maybe [(Expr, a)]
        followAndGetTargs [] _ = Just []
        followAndGetTargs ((boxNumber, (targInd, dat)):rest) boxZipper = do
            newBoxZipper <- toBoxNumberFromZipper boxNumber boxZipper
            targ <- getPureTargInZipper targInd newBoxZipper
            otherTargs <- followAndGetTargs rest newBoxZipper
            Just ((targ, dat):otherTargs)
    extractedTargs <- followAndGetTargs boxNumbersWithData (rootBox, [])
    Just (extractedTargs, shallowestBox)

-- Checks if the list of expressions provided exist as hypothess in the tableau
-- in such a way that they can be used together. If not, returns Nothing.
-- If so, returns the deepest BoxNumber's in which the hypotheses lies (there could be many, depending on the route taken)
checkHypsExistCompatibly :: [Expr] -> Tableau -> [BoxNumber]
checkHypsExistCompatibly hypsToFind tab@(Tableau qZone rootBox@(Box rootHyps rootTargs)) = let
    exploreBranch :: ((BoxNumber, BoxZipper Expr), [Expr]) -> [((BoxNumber, BoxZipper Expr), [Expr])]
    exploreBranch ((boxNumber, boxZipper@(Box hyps targs, crumbs)), hypsToFind') = let
        newBranches = mapMaybe (\targInd -> case toBoxNumberFromZipper [targInd] boxZipper of
            Just newBoxZipper -> Just (boxNumber++[targInd], newBoxZipper)
            Nothing -> Nothing
            ) [0..length targs-1]
        in map (\a@(_, (Box hyps targs, _)) -> (a, filter (`notElem` hyps) hypsToFind')) newBranches
    
    exploreBranches :: ((BoxNumber, BoxZipper Expr), [Expr]) -> [BoxNumber]
    exploreBranches ((boxNumber, _), []) = [boxNumber]
    exploreBranches a@((boxNumber, boxZipper), _) = concatMap (exploreBranches) (exploreBranch a)

    remainingHyps = filter (`notElem` rootHyps) hypsToFind
    rootZipper = (rootBox, [])

    in exploreBranches (([], rootZipper), remainingHyps)


-- <<< NON-LIB MOVES >>>

-- PEELING

-- Peels universal target
-- targ i : forall x, P(x)
peelUniversalTarg :: BoxNumber -> Int -> Move
peelUniversalTarg boxNumber targInd tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Forall exNm sc) <- getPureTarg boxNumber targInd tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updatePureTarg boxNumber targInd (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- Peels existential target, creating a metavariable
-- targ i : exists x, P(x)
peelExistentialTarg :: BoxNumber -> Int -> Move
peelExistentialTarg boxNumber targInd tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Exists exNm sc) <- getPureTarg boxNumber targInd tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updatePureTarg boxNumber targInd (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- Peels existential hypothesis
-- hyp i : exists x, P(x)
-- IMPROVEMENT - currently find new external name to prevent confusing outputs after a single move, but maybe this should happen at the print stage? Think about this.
peelExistentialHyp :: BoxNumber -> Int -> Move
peelExistentialHyp boxNumber hypInd tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Exists exNm sc) <- getHyp boxNumber hypInd tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- updateHyp boxNumber hypInd (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox

-- Peels universal hypothesis, creating a metavariable
-- This move keeps the original hypothesis, because it's dangerous otherwise
-- hyp i : forall x, P(x)
peelUniversalHyp :: BoxNumber -> Int -> Move
peelUniversalHyp boxNumber hypInd tab@(Tableau qZone@(Poset set rel) rootBox) = do
    expr@(Forall exNm sc) <- getHyp boxNumber hypInd tab
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (Tableau _ newRootBox) <- addHyp boxNumber (instantiate (Free peeledName) sc) tab
    return $ Tableau newQZone newRootBox


-- TIDYING

-- Tidies implication in target
-- targ i : P \implies Q
tidyImplInTarg :: BoxNumber -> Int -> Move
tidyImplInTarg boxNumber targInd tab@(Tableau qZone rootBox) = do
    Box hyps targs <- getBox boxNumber rootBox
    PureTarg (Implies p q) <- getFromListMaybe targs targInd
    if length targs == 1 then
        addHyp boxNumber p tab >>= updatePureTarg boxNumber targInd q
    else
        removeTarg boxNumber targInd tab >>= addBoxTarg boxNumber (Box [p] [PureTarg q])

-- Splits and hypotheses up
-- hyp i : P ^ Q
tidyAndInHyp :: BoxNumber -> Int -> Move
tidyAndInHyp boxNumber hypInd tab@(Tableau qZone rootBox) = do
    And p q <- getHyp boxNumber hypInd tab
    updateHyp boxNumber hypInd p tab >>= addHyp boxNumber q

tidyAndInTarg :: BoxNumber -> Int -> Move
tidyAndInTarg boxNumber targInd tab@(Tableau qZone rootBox) = do
    And p q <- getPureTarg boxNumber targInd tab
    updatePureTarg boxNumber targInd p tab >>= addPureTarg boxNumber q


-- MODUS PONENS AND BACKWARDS REASONING

-- Performs modus ponens on hypotheses i and j
-- hyp i : forall x, P(x) \implies Q(x)
-- hyp j : P(y)
-- conclude : Q(y)
modusPonens :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
modusPonens (boxNumber1, hypInd1) (boxNumber2, hypInd2) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2 || isPrefix boxNumber2 boxNumber1
    let deepestBoxNumber = if isPrefix boxNumber1 boxNumber2 then boxNumber2 else boxNumber1

    expr@(Forall exNm (Sc (Implies px qx))) <- getHyp boxNumber1 hypInd1 tab
    let freeVars = getFreeVars expr
    py <- getHyp boxNumber2 hypInd2 tab
    let freeVars'@(freeVar':rest') = getFreeVars py
        toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
    guard $ not (null toInstantiate')
    guard $ (expr /= py)
    let successes = filter (\var -> instantiate (Free var) (Sc px) == py) toInstantiate'
    guard $ length successes == 1
    let newHyp = instantiate (Free . head $ successes) (Sc qx)
    
    addHyp deepestBoxNumber newHyp tab

rawModusPonens :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
rawModusPonens (boxNumber1, hypInd1) (boxNumber2, hypInd2) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2 || isPrefix boxNumber2 boxNumber1
    let deepestBoxNumber = if isPrefix boxNumber1 boxNumber2 then boxNumber2 else boxNumber1
    expr@(Implies p q) <- getHyp boxNumber1 hypInd1 tab
    p' <- getHyp boxNumber2 hypInd2 tab
    guard $ p' == p
    addHyp deepestBoxNumber q tab


-- Performs backwards reasoning on hypothesis i and target j
-- hyp i  : P \implies Q
-- targ j : Q
-- replace targ j with P
backwardsReasoningHyp :: (BoxNumber, Int) -> (BoxNumber, Int) -> Move
backwardsReasoningHyp (boxNumber1, hypInd) (boxNumber2, targInd) tab@(Tableau qZone rootBox) = do
    guard $ isPrefix boxNumber1 boxNumber2

    expr@(Implies p q) <- getHyp boxNumber1 hypInd tab
    q' <- getPureTarg boxNumber2 targInd tab
    guard $ q == q'
    updatePureTarg boxNumber2 targInd p tab


-- <<< OTHER >>>
-- Commits to the use of a particular hypothesis
-- hyp i : P \implies Q
-- add a new box with only target P and all hypotheses except i
-- replace hyp i in this box with Q
commitToHypothesis :: BoxNumber -> Int -> Move
commitToHypothesis boxNumber hypInd tab@(Tableau qZone rootBox) = do
    Implies p q <- getHyp boxNumber hypInd tab
    Box hyps targs <- getBox boxNumber rootBox
    let targsWithQ = Box [q] targs
    removeAllTargs boxNumber tab >>= addPureTarg boxNumber p >>= addBoxTarg boxNumber targsWithQ


{-
-- <<< QUALITY OF LIFE MOVES (IMPLEMENTED QUESTIONABLY) >>>

-- Repeat a hyp-index receiving move on a box as many times as possible
repeatAsMuchAsPossibleOnHyps :: (Int -> Move) -> Move
repeatAsMuchAsPossibleOnHyps move qBox@(qZone, box@(Box hyps targs)) =
    let applyOnce = mapMaybe (\i -> move i qBox) [0..(length hyps) - 1]
    in if null applyOnce then Just qBox else repeatAsMuchAsPossibleOnHyps move $ head applyOnce

repeatAsMuchAsPossibleOnTargs :: (Int -> Move) -> Move
repeatAsMuchAsPossibleOnTargs move qBox@(qZone, box@(Box hyps targs)) =
    let applyOnce = mapMaybe (\i -> move i qBox) [0..(length targs) - 1]
    in if null applyOnce then Just qBox else repeatAsMuchAsPossibleOnTargs move $ head applyOnce

-- Repeats a Move until the result is the same twice in a row or we can't perform the move again
repeatAsMuchAsPossible :: Move -> Move
repeatAsMuchAsPossible move qBox = repeatUntilFP move (Just (Poset [] [], Box [] [])) (Just qBox)
    where
        repeatUntilFP :: Move -> Maybe (Box Expr) -> Maybe (Box Expr) -> Maybe (Box Expr)
        repeatUntilFP move' last current =
            if last == current then current else case current of
                Just something -> repeatUntilFP move' current (move' something)
                _ -> last

tidySweep :: Move
tidySweep qBox = (repeatAsMuchAsPossibleOnTargs peelUniversalTargBox) qBox
    >>= (repeatAsMuchAsPossibleOnHyps peelExistentialHypBox)
    >>= (repeatAsMuchAsPossibleOnTargs tidyAndInTargBox)
    >>= (repeatAsMuchAsPossibleOnHyps tidyAndInHypBox)

tidyEverythingBox :: Move
tidyEverythingBox = repeatAsMuchAsPossible tidySweep

tidyTabImplOnce :: Move
tidyTabImplOnce tab@(Tableau qZone boxes) = let
    boxAndTargInds = concatMap (\boxInd -> let
        Box hyps targs = boxes!!boxInd
        in [(boxInd, targInd) | targInd <- [0..length targs-1]]
        ) [0..length boxes - 1]
    results = mapMaybe (\(boxInd, targInd) -> tidyImplInTarg targInd boxInd tab) boxAndTargInds
    in if null results then Just tab else Just $ head results

tidyTabOnBoxesOnce :: Move
tidyTabOnBoxesOnce tab@(Tableau qZone boxes) = let
    results = mapMaybe (\boxInd -> let
        result = tidyEverythingBox (qZone, boxes!!boxInd)
        in case result of
            Just something -> if something == (qZone, boxes!!boxInd) then Nothing else Just (boxInd, something)
            _ -> Nothing
        ) [0..length boxes-1]
    in if null results then Just tab else let
        (boxInd, (newQZone, newBox)) = head results
        (as, ourBox:bs) = splitAt boxInd boxes
        newBoxes = as ++ (newBox:bs)
        in Just (Tableau newQZone newBoxes)

tidyTabOnce :: Move
tidyTabOnce tab = tidyTabOnBoxesOnce tab >>= tidyTabImplOnce

tidyEverything :: Move
tidyEverything = repeatAsMuchAsPossibleTab tidyTabOnce

repeatAsMuchAsPossibleTab :: Move -> Move
repeatAsMuchAsPossibleTab tabMove tab = repeatUntilFP tabMove (Just $ Tableau (Poset [] []) []) (Just tab)
    where
        repeatUntilFP :: Move -> Maybe Tableau -> Maybe Tableau -> Maybe Tableau
        repeatUntilFP move' last current =
            if last == current then current else case current of
                Just something -> repeatUntilFP move' current (move' something)
                _ -> last



-}