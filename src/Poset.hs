module Poset where

import Data.List
import Debug.Trace
import Control.Applicative.Combinators (count)

-- | Poset type to store information about quantification order. Probably very inefficient for now, but this can be optimised I'm sure
-- In the relations list, a tuple (x_1, x_2) indicates that x_1 < x_2, i.e. x_1 must come before x_2
data Poset a = Poset {getSet :: [a], getRelations :: [(a, a)]} deriving (Eq, Show, Read)

-- | Adds member to set, leaving relation untouched
addSetMember :: (Eq a) => Poset a -> a -> Poset a
addSetMember (Poset set rel) x = Poset (set++[x]) rel

-- | Removes a member from the Poset, including from all dependencies
removeMember :: (Eq a) => Poset a -> a -> Poset a
removeMember (Poset set rel) x = let
  newSet = filter (/= x) set
  newRel = filter (\(a, b) -> a /= x && b /= x) rel
  in Poset newSet newRel

-- | Checks if a Poset is actually transitive
isTransitive :: (Eq a) => Poset a -> Bool
isTransitive (Poset set rel) = [] == [(x, y, z) | x <- set, y <- set, z <- set, (((x,y) `elem` rel) && ((y,z) `elem` rel)) && (not ((x, z) `elem` rel))]

-- | Checks if a Poset is actually irreflexive
isIrreflexive :: (Eq a) => Poset a -> Bool
isIrreflexive (Poset set rel) = and [not ((x,x) `elem` rel) | x <- set]

-- | Checks if a Poset is actually asymmetric
isAsymmetric :: (Eq a) => Poset a -> Bool
isAsymmetric (Poset set rel) = and [not (((x,y) `elem` rel) && ((y,x) `elem` rel)) | x <- set, y <- set]

-- | Checks if a Poset is a genuine mathematical poset. Note irreflexivity is covered by our implementation of asymmetry.
isRealPoset :: (Eq a) => Poset a -> Bool
isRealPoset poset = isTransitive poset && isAsymmetric poset

-- | Checks if a Poset is transitively closed. If it isn't then exhibits witnesses to this.
transitivelyCloseCounterExamples :: (Eq a) => Poset a -> [(a, a)]
transitivelyCloseCounterExamples (Poset set rel) =
  let counterExamples = [(x, y, z) | x <- set, y <- set, z <- set, (((x,y) `elem` rel) && ((y,z) `elem` rel)) && (not ((x, z) `elem` rel))]
  in map (\(x, y, z) -> (x, z)) (nub counterExamples)

-- | Takes a Poset and try to extend it to a genuine mathematical poset which is transitively closed
transitivelyClose :: (Eq a) => Poset a -> Maybe (Poset a)
transitivelyClose poset =
  let witnesses = transitivelyCloseCounterExamples poset
  in
    if witnesses == [] then (if isRealPoset poset then Just poset else Nothing)
    else
      let (Poset set rel) = poset
          newPoset = Poset set (witnesses ++ rel)
      in if isAsymmetric newPoset then transitivelyClose newPoset else Nothing

-- | Adds (a, b) to relation. If the result is not a Poset, returns Nothing.
addRel :: (Eq a) => Poset a -> (a,a) -> Maybe (Poset a)
addRel (Poset set rel) (x, y) = transitivelyClose (Poset set ((x,y):rel))

addRels :: (Eq a) => Poset a -> [(a, a)] -> Maybe (Poset a)
addRels (Poset set rel) toAdd = transitivelyClose (Poset set (toAdd ++ rel))

-- | isBefore poset a b = True only when a < b in the poset
isBefore :: (Eq a) => Poset a -> a -> a -> Bool
isBefore (Poset set rel) x y = (x, y) `elem` rel

-- | isAfter poset a b = True only when a > b in the poset
isAfter :: (Eq a) => Poset a -> a -> a -> Bool
isAfter (Poset set rel) x y = (y, x) `elem` rel

-- | Given a poset and an element, x, of the poset, checks if there are any y such that y < x
hasParent :: (Eq a) => Poset a -> a -> Bool
hasParent (Poset set rel) x = or [(y, x) `elem` rel | y <- set]

