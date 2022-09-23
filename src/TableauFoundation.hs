module TableauFoundation where

import Poset
import Lib
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Data.List

-- <<<< TYPES DEFINING WHAT A TABLEAU IS >>>>

type Quantifier = String
data QuantifiedVariable = QVar { qVarGetQuantifier :: Quantifier
                               , qVarGetExternalName :: Maybe ExternalName
                               , qVarGetInternalName :: InternalName
                               }
  deriving (Eq, Read, Show)

type QZone = Poset QuantifiedVariable

data Box a = Box {getBoxHyps :: [a],
                getBoxTargs :: [Targ a]} deriving (Eq, Show, Read)
data Targ a = BoxTarg (Box a) | PureTarg a deriving (Eq, Show, Read)

data Tableau = Tableau {getQZone :: QZone,
                        getRootBox :: Box Expr}
                        deriving (Eq, Read, Show)

instance Functor Box where
  fmap f (Box hyps targs) = Box (map f hyps) (map targf targs) where
    targf (BoxTarg box) = BoxTarg $ fmap f box
    targf (PureTarg targ) = PureTarg $ f targ


data BoxCrumb a = Crumb [a] [Targ a] [Targ a]
type BoxZipper a = (Box a, [BoxCrumb a])

type BoxNumber = [Int]

toBoxNumberFromZipper :: BoxNumber -> BoxZipper a -> Maybe (BoxZipper a)
toBoxNumberFromZipper [] zipper = Just zipper
toBoxNumberFromZipper (nextBoxInd:rest) (Box hyps targs, crumbs)
  | nextBoxInd < 0 || nextBoxInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt nextBoxInd targs in case ourTarg of
      PureTarg something -> Nothing
      BoxTarg newBox -> let
        newCrumb = Crumb hyps as bs
        newZipper = Just (newBox, newCrumb:crumbs)
        in newZipper >>= toBoxNumberFromZipper rest

toBoxNumberFromRoot :: BoxNumber -> Box a -> Maybe (BoxZipper a)
toBoxNumberFromRoot boxNumber box = toBoxNumberFromZipper boxNumber (box, [])

goUp :: BoxZipper a -> Maybe (BoxZipper a)
goUp (_, []) = Nothing
goUp (box, crumb:rest) = let
  Crumb hyps aTargs bTargs = crumb
  newBox = Box hyps (aTargs ++ [BoxTarg box] ++ bTargs)
  in Just (newBox, rest)

unzipBox :: BoxZipper a -> Box a
unzipBox (box, []) = box
unzipBox zipper@(box, crumb:rest) = let Just newZipper = goUp zipper
  in unzipBox newZipper


getHypInZipper :: Int -> BoxZipper a -> Maybe a
getHypInZipper hypInd (Box hyps targs, crumbs)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = Just $ hyps !! hypInd

getPureTargInZipper :: Int -> BoxZipper a -> Maybe a
getPureTargInZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = case targs !! targInd of
    BoxTarg _ -> Nothing
    PureTarg targ -> Just targ

getBoxTargInZipper :: Int -> BoxZipper a -> Maybe (Box a)
getBoxTargInZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = case targs !! targInd of
    BoxTarg box -> Just box
    PureTarg _ -> Nothing

getBox :: BoxNumber -> Box a -> Maybe (Box a)
getBox boxNumber rootBox = case toBoxNumberFromRoot boxNumber rootBox of
  Just (box, crumbs) -> Just box
  Nothing -> Nothing

addHypToZipper :: a -> BoxZipper a -> BoxZipper a
addHypToZipper hyp (Box hyps targs, crumbs) = (Box (hyps++[hyp]) targs, crumbs)

addPureTargToZipper :: a -> BoxZipper a -> BoxZipper a
addPureTargToZipper targ (Box hyps targs, crumbs) = (Box hyps (targs++[PureTarg targ]), crumbs)

addBoxTargToZipper :: Box a -> BoxZipper a -> BoxZipper a
addBoxTargToZipper targ (Box hyps targs, crumbs) = (Box hyps (targs++[BoxTarg targ]), crumbs)

removeHypFromZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
removeHypFromZipper hypInd (Box hyps targs, crumbs)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = let (as, ourHyp:bs) = splitAt hypInd hyps
    in Just (Box (as++bs) targs, crumbs)

removeTargFromZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
removeTargFromZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in Just (Box hyps (as++bs), crumbs)

updateHypInZipper :: Int -> a -> BoxZipper a -> Maybe (BoxZipper a)
updateHypInZipper hypInd newHyp (Box hyps targs, crumbs)
  | hypInd < 0 || hypInd >= length hyps = Nothing
  | otherwise = let (as, ourHyp:bs) = splitAt hypInd hyps
    in Just (Box (as++newHyp:bs) targs, crumbs)

updatePureTargInZipper :: Int -> a -> BoxZipper a -> Maybe (BoxZipper a)
updatePureTargInZipper targInd newTarg (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in case ourTarg of
      PureTarg _ -> Just (Box hyps (as++PureTarg newTarg:bs), crumbs)
      BoxTarg _ -> Nothing

updateBoxTargInZipper :: Int -> Box a -> BoxZipper a -> Maybe (BoxZipper a)
updateBoxTargInZipper targInd newTarg (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs
    in case ourTarg of
      BoxTarg _ -> Just (Box hyps (as++BoxTarg newTarg:bs), crumbs)
      PureTarg _ -> Nothing


pureToBoxTargZipper :: Int -> BoxZipper a -> Maybe (BoxZipper a)
pureToBoxTargZipper targInd (Box hyps targs, crumbs)
  | targInd < 0 || targInd >= length targs = Nothing
  | otherwise = let (as, ourTarg:bs) = splitAt targInd targs in
    case ourTarg of
      BoxTarg _ -> Nothing
      PureTarg targ -> Just (Box hyps (as ++ BoxTarg (Box [] [PureTarg targ]):bs), crumbs)


getHypsUsableInBoxNumber :: BoxNumber -> Box Expr -> Maybe [Expr]
getHypsUsableInBoxNumber [] (Box rootHyps _) = Just rootHyps
getHypsUsableInBoxNumber (nextBoxInd:rest) (Box rootHyps rootTargs)
  | nextBoxInd < 0 || nextBoxInd >= length rootTargs = Nothing
  | otherwise = case rootTargs !! nextBoxInd of
      PureTarg _ -> Nothing
      BoxTarg box -> do
        lowerHyps <- getHypsUsableInBoxNumber rest box
        Just $ rootHyps ++ lowerHyps


isPrefix :: BoxNumber -> BoxNumber -> Bool
isPrefix [] _ = True
isPrefix (a:_) [] = False
isPrefix (a:as) (b:bs) = a == b && isPrefix as bs

-- Returns the order of box numbers required to traverse from top to bottom, hitting everything on the way
-- If this isn't possible (i.e. backtracking is necessary, returns nothing)
orderBoxNumbers :: [BoxNumber] -> Maybe [BoxNumber]
orderBoxNumbers boxNumbers = let
  sortedBoxNumbers = sortBy (\a b -> length a `compare` length b) boxNumbers
  in if verifyPrefix [] (nub sortedBoxNumbers) then Just sortedBoxNumbers else Nothing
  where
    verifyPrefix :: BoxNumber -> [BoxNumber] -> Bool
    verifyPrefix _ [] = True
    verifyPrefix currentNumber (nextNumber:rest) = isPrefix currentNumber nextNumber && verifyPrefix nextNumber rest

getPrefixDiff :: BoxNumber -> BoxNumber -> Maybe BoxNumber
getPrefixDiff longer [] = Just longer
getPrefixDiff [] (a:_) = Nothing
getPrefixDiff (a:as) (b:bs) = if a == b then getPrefixDiff as bs else Nothing

-- If an ordering like the one in orderBoxNumbers exists, this gives us a list of directions to take to pass by all of the desired boxes.
-- We carry along additional data (of type a) with us, so we can perform actions at each stage if wanted.
boxNumbersToDirections :: [(BoxNumber, a)] -> Maybe ([(BoxNumber, a)], BoxNumber)
boxNumbersToDirections boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> length (fst a) `compare` length (fst b)) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  deepestBox = case map fst reverseSortedBoxNumbersWithData of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, deepestBox)

boxNumbersToDirectionsFlipped :: [(BoxNumber, a)] -> Maybe ([(BoxNumber, a)], BoxNumber)
boxNumbersToDirectionsFlipped boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> length (fst a) `compare` length (fst b)) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  shallowestBox = case map fst (reverse reverseSortedBoxNumbersWithData) of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, shallowestBox)


-- Purely for removing targs and hyps. Idea is the second "Int" component should be decreasing when BoxNumber is same
boxNumbersToDirectionsWithInt :: [(BoxNumber, Int)] -> Maybe ([(BoxNumber, Int)], BoxNumber)
boxNumbersToDirectionsWithInt boxNumbersWithData = let
  reverseSortedBoxNumbersWithData = sortBy (\b a -> let
    firstCompare = length (fst a) `compare` length (fst b)
    in if firstCompare /= EQ then firstCompare else snd b `compare` snd a) boxNumbersWithData
  traverseBoxNumbers :: [(BoxNumber, a)] -> [(BoxNumber, a)] -> Maybe [(BoxNumber, a)]
  traverseBoxNumbers trailSoFar [] = Just trailSoFar
  traverseBoxNumbers trailSoFar [thisBox] = Just (thisBox:trailSoFar)
  traverseBoxNumbers trailSoFar (thisBox:(nextBox:rest)) = -- thisBox is further down than nextBox
    case getPrefixDiff (fst thisBox) (fst nextBox) of
      Nothing -> Nothing
      Just diff -> traverseBoxNumbers ((diff, snd thisBox):trailSoFar) (nextBox:rest)
  shallowestBox = case map fst (reverse reverseSortedBoxNumbersWithData) of
    [] -> []
    (a:_) -> a
  in do
    directions <- traverseBoxNumbers [] reverseSortedBoxNumbersWithData
    Just (directions, shallowestBox)
