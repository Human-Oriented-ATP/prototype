{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}

module BasicMoves where

import Lib
import TableauFoundation
import Poset
import Data.Maybe
import Data.List
import Control.Monad
import PPrinting
import HoleExpr
import Debug.Trace

-- <<< FOUNDATIONAL CODE >>>

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

addTarg :: Targ -> QBox -> Maybe QBox
addTarg targ (qZone, Box hyps targs) = Just (qZone, Box hyps (targs++[targ]))

addHyps :: [Hyp] -> QBox -> Maybe QBox
addHyps hypsToAdd (qZone, Box hyps targs) = Just (qZone, Box (hyps++hypsToAdd) targs)

addTargs :: [Hyp] -> QBox -> Maybe QBox
addTargs targsToAdd (qZone, Box hyps targs) = Just (qZone, Box hyps (targs++targsToAdd))

-- Removes hyps/targs. Should out-of-bounds index give unchanged or Nothing? Not sure yet.
-- IMPROVEMENT - think about whether out-of-bounds index should return unchanged or Nothing
removeHyp :: Int -> QBox -> Maybe QBox
removeHyp i (qZone, Box hyps targs)
    | i < 0 || i >= length hyps = Nothing
    | otherwise =
        let (as, (hyp:bs)) = splitAt i hyps
            updatedHyps = as++bs
        in Just (qZone, Box updatedHyps targs)

removeTarg :: Int -> QBox -> Maybe QBox
removeTarg i (qZone, Box hyps targs)
    | i < 0 || i >= length targs = Nothing
    | otherwise =
        let (as, (targ:bs)) = splitAt i targs
            updatedTargs = as++bs
        in Just (qZone, Box hyps updatedTargs)

-- Slightly more time-efficient solutions exist, but not sure the constant overhead is worth it?
removeHyps :: [Int] -> QBox -> Maybe QBox
removeHyps [] qBox = Just qBox
removeHyps inds qBox@(qZone, Box hyps targs)
    | any (\i -> i < 0 || i >= length hyps) inds = Nothing
    | otherwise = removeHypsNoSort 0 (sort inds) qBox where
        removeHypsNoSort :: Int -> [Int] -> QBox -> Maybe QBox
        removeHypsNoSort counter inds qBox = do
            let (ind:rest) = inds
            newBox <- removeHyp (ind-counter) qBox
            removeHypsNoSort (counter+1) rest newBox

removeTargs :: [Int] -> QBox -> Maybe QBox
removeTargs [] qBox = Just qBox
removeTargs inds qBox@(qZone, Box hyps targs)
    | any (\i -> i < 0 || i >= length targs) inds = Nothing
    | otherwise = removeTargsNoSort 0 (sort inds) qBox where
        removeTargsNoSort :: Int -> [Int] -> QBox -> Maybe QBox
        removeTargsNoSort counter [ind] qBox = removeTarg (ind-counter) qBox
        removeTargsNoSort counter inds qBox = do
            let (ind:rest) = inds
            newBox <- removeTarg (ind-counter) qBox
            removeTargsNoSort (counter+1) rest newBox

-- Updates the i-th hypothesis. Maybe because it might not exist.
updateHyp :: Int -> Hyp -> QBox -> Maybe QBox
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



-- <<< NON-LIB MOVES >>>

-- PEELING

-- Peels universal target
-- targ i : forall x, P(x)
peelUniversalTargBox :: Int -> BoxMove
peelUniversalTargBox i qBox@(qZone, Box hyps targs) = do
    expr@(Forall exNm sc) <- getTarg i targs
    let Poset set deps = qZone
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"] -- We only need to add dependencies relating to exists, because dependencies between forall's is given by this
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateTarg i (instantiate (Free peeledName) sc) qBox
    return $ (newQZone, newBox)

-- Peels existential target, creating a metavariable
-- targ i : exists x, P(x)
peelExistentialTargBox :: Int -> BoxMove
peelExistentialTargBox i qBox@(qZone, Box hyps targs) = do
    expr@(Exists exNm sc) <- getTarg i targs
    let Poset set deps = qZone
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateTarg i (instantiate (Free peeledName) sc) qBox
    return $ (newQZone, newBox)

-- Peels existential hypothesis
-- hyp i : exists x, P(x)
-- IMPROVEMENT - currently find new external name to prevent confusing outputs after a single move, but maybe this should happen at the print stage? Think about this.
peelExistentialHypBox :: Int -> BoxMove
peelExistentialHypBox i qBox@(qZone, Box hyps targs) = do
    expr@(Exists exNm sc) <- getHyp i hyps
    let Poset set deps = qZone
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Forall" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Exists"]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- updateHyp i (instantiate (Free peeledName) sc) qBox
    return $ (newQZone, newBox)

-- Peels universal hypothesis, creating a metavariable
-- This move keeps the original hypothesis, because it's dangerous otherwise
-- hyp i : forall x, P(x)
peelUniversalHypBox :: Int -> BoxMove
peelUniversalHypBox i qBox@(qZone, Box hyps targs) = do
    expr@(Forall exNm sc) <- getHyp i hyps
    let Poset set deps = qZone
    let freeVars = map (\inNm -> head $ filter (\q -> qVarGetInternalName q == inNm) set) $ getFreeVars expr
    let peeledName = getNewInternalName qZone
    let peeledExternalName = getNewExternalNamePeel exNm qZone
    let peeledVariable = QVar "Exists" peeledExternalName peeledName
    let newDeps = [(y, peeledVariable) | y <- freeVars, qVarGetQuantifier y == "Forall"]
    newQZone <- addRels (addSetMember qZone peeledVariable) newDeps
    (qZone, newBox) <- addHyp (instantiate (Free peeledName) sc) qBox
    return $ (newQZone, newBox)


-- TIDYING

-- Tidies implication in target
-- targ i : P \implies Q
tidyImplInTarg :: Int -> Int -> TableauMove
tidyImplInTarg i boxInd tab@(Tableau qZone boxes) = do
    qBox@(qZone, Box hyps targs) <- getBox boxInd tab
    Implies p q <- getTarg i targs
    let newHyps = hyps ++ [p]
    let newTargs = [q]
    let newBox = Box newHyps newTargs
    (_, remainingBox) <- removeTarg i qBox
    updateBox boxInd remainingBox tab >>= addBox newBox >>= clearEmptyBoxes

-- Splits and hypotheses up
-- hyp i : P ^ Q
tidyAndInHypBox :: Int -> BoxMove
tidyAndInHypBox i qBox@(qZone, Box hyps targ) = do
    And p q <- getHyp i hyps
    updateHyp i p qBox >>= addHyp q

tidyAndInTargBox :: Int -> BoxMove
tidyAndInTargBox i qBox@(qZone, Box hyps targs) = do
    And p q <- getTarg i targs
    updateTarg i p qBox >>= addTarg q


-- MODUS PONENS AND BACKWARDS REASONING

-- Performs modus ponens on hypotheses i and j
-- hyp i : forall x, P(x) \implies Q(x)
-- hyp j : P(y)
-- conclude : Q(y)
modusPonensBox :: Int -> Int -> BoxMove
modusPonensBox i j qBox@(qZone, Box hyps targs) = do
    expr@(Forall exNm (Sc (Implies px qx))) <- getHyp i hyps
    let freeVars = getFreeVars expr
    py <- getHyp j hyps
    let freeVars'@(freeVar':rest') = getFreeVars py
    let toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
    guard $ not (null toInstantiate')
    guard $ (expr /= py)
    let successes = filter (\var -> instantiate (Free var) (Sc px) == py) toInstantiate'
    guard $ length successes == 1
    let newHyp = instantiate (Free . head $ successes) (Sc qx)
    addHyp newHyp qBox

-- Performs backwards reasoning on hypothesis i and target j
-- hyp i  : P \implies Q
-- targ j : Q
-- replace targ j with P
backwardsReasoningHypBox :: Int -> Int -> BoxMove
backwardsReasoningHypBox i j qBox@(qZone, Box hyps targs) = do
    expr@(Implies p q) <- getHyp i hyps
    q' <- getTarg j targs
    guard $ q == q'
    updateTarg j p qBox


-- <<< OTHER >>>
-- Commits to the use of a particular hypothesis
-- hyp i : P \implies Q
-- add a new box with only target P and all hypotheses except i
-- replace hyp i in this box with Q
commitToHypothesis :: Int -> Int -> TableauMove
commitToHypothesis i boxInd tab@(Tableau qZone boxes) = do
    qBox@(_, Box hyps targs) <- getBox boxInd tab
    expr@(Implies p q) <- getHyp i hyps
    (qZone, Box deducePHyps _) <- removeHyp i qBox
    let deducePBox = (Box deducePHyps [p])
    (_, useQBox) <- updateHyp i q qBox
    newTab <- updateBox boxInd useQBox tab
    addBox deducePBox newTab


-- <<< QUALITY OF LIFE MOVES (IMPLEMENTED QUESTIONABLY) >>>

-- Repeat a hyp-index receiving move on a box as many times as possible
repeatAsMuchAsPossibleOnHyps :: (Int -> BoxMove) -> BoxMove
repeatAsMuchAsPossibleOnHyps move qBox@(qZone, box@(Box hyps targs)) =
    let applyOnce = mapMaybe (\i -> move i qBox) [0..(length hyps) - 1]
    in if null applyOnce then Just qBox else repeatAsMuchAsPossibleOnHyps move $ head applyOnce

repeatAsMuchAsPossibleOnTargs :: (Int -> BoxMove) -> BoxMove
repeatAsMuchAsPossibleOnTargs move qBox@(qZone, box@(Box hyps targs)) =
    let applyOnce = mapMaybe (\i -> move i qBox) [0..(length targs) - 1]
    in if null applyOnce then Just qBox else repeatAsMuchAsPossibleOnTargs move $ head applyOnce

-- Repeats a BoxMove until the result is the same twice in a row or we can't perform the move again
repeatAsMuchAsPossible :: BoxMove -> BoxMove
repeatAsMuchAsPossible move qBox = repeatUntilFP move (Just (Poset [] [], Box [] [])) (Just qBox)
    where
        repeatUntilFP :: BoxMove -> Maybe QBox -> Maybe QBox -> Maybe QBox
        repeatUntilFP move' last current =
            if last == current then current else case current of
                Just something -> repeatUntilFP move' current (move' something)
                _ -> last

tidySweep :: BoxMove
tidySweep qBox = (repeatAsMuchAsPossibleOnTargs peelUniversalTargBox) qBox
    >>= (repeatAsMuchAsPossibleOnHyps peelExistentialHypBox)
    >>= (repeatAsMuchAsPossibleOnTargs tidyAndInTargBox)
    >>= (repeatAsMuchAsPossibleOnHyps tidyAndInHypBox)

tidyEverythingBox :: BoxMove
tidyEverythingBox = repeatAsMuchAsPossible tidySweep

tidyTabImplOnce :: TableauMove
tidyTabImplOnce tab@(Tableau qZone boxes) = let
    boxAndTargInds = concatMap (\boxInd -> let
        Box hyps targs = boxes!!boxInd
        in [(boxInd, targInd) | targInd <- [0..length targs-1]]
        ) [0..length boxes - 1]
    results = mapMaybe (\(boxInd, targInd) -> tidyImplInTarg targInd boxInd tab) boxAndTargInds
    in if null results then Just tab else Just $ head results

tidyTabOnBoxesOnce :: TableauMove
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

tidyTabOnce :: TableauMove
tidyTabOnce tab = tidyTabOnBoxesOnce tab >>= tidyTabImplOnce

tidyEverything :: TableauMove
tidyEverything = repeatAsMuchAsPossibleTab tidyTabOnce

repeatAsMuchAsPossibleTab :: TableauMove -> TableauMove
repeatAsMuchAsPossibleTab tabMove tab = repeatUntilFP tabMove (Just $ Tableau (Poset [] []) []) (Just tab)
    where
        repeatUntilFP :: TableauMove -> Maybe Tableau -> Maybe Tableau -> Maybe Tableau
        repeatUntilFP move' last current =
            if last == current then current else case current of
                Just something -> repeatUntilFP move' current (move' something)
                _ -> last



