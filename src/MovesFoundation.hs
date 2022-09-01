{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
module MovesFoundation where

import ExpressionFoundation
import TableauFoundation
import Poset
import Data.Maybe
import Data.List


-- TO-DO: Again, pretty sure there is a more abstract function which takes care of the various peeling/metavariable creation rules. Not going to mess around with this for now, but there may be some genuinely interesting theoretical points here, anyway.

-- <<<< THIS IS CURRENTLY THE MACHINERY WHICH CONTROLS HOW WE WRITE MOVES >>>>

-- | Returns a list of tableaus because the same move could have multiple results (e.g. for splitting, depending on which statement it's applied to)
type Move = Tableau -> [Tableau]

-- | This specifies a move on a single box (noting all boxes share a single TableauHead). This is usually more natural.
type BoxMove = HBox -> [HBox]

-- | The idea is much like the IO Monad - a HBox, (TableauHead, Box), forms a very natural object on which moves should act
-- (BoxMoveM a) is the type of moves, HBox -> [(a, HBox)], i.e. a (BoxMoveM a) takes a HBox, performs some move on it (possibly doing nothing), and fetches a value of type a.
-- In fact, the result is a list of (a, HBox)'s, because a single move could have multiple results (for example peeling moves, or basic logic moves)
newtype BoxMoveM a = BoxMoveM (HBox -> [(a, HBox)])

-- | Naturally a functor. Simply map a given function f :: a -> b over the fetch-result, ignoring the head
-- f :: a -> b
-- x :: HBox -> [(a, HBox)]
-- fmap f x :: HBox -> [(b, HBox)]
instance Functor BoxMoveM where
  fmap f (BoxMoveM x) = BoxMoveM $ \hBox -> map (\(a, head) -> (f a, head)) (x hBox)

-- | Less naturally an Applicative. Right now we ignore the HBoxes from the list of functions, and use the HBoxes of the values themselves.
-- This instance is a bit weird, and I'm not entirely sure this will work as we want in the long run. At least there's only one other natural choice.
-- pure :: a -> (HBox -> [(a, HBox)])
-- f :: (HBox -> [(a -> b), HBox])
-- x :: (HBox -> [(a, HBox)])
-- f <*> x :: (HBox -> [(b, HBox)])
instance Applicative BoxMoveM where
  pure x = BoxMoveM $ \hBox -> [(x, hBox)]
  BoxMoveM f <*> BoxMoveM x = BoxMoveM $ \hBox -> let
    listOfFuncHBoxes = f hBox
    listOfAHBoxes = x hBox
    in concatMap (\(f, _) -> map (\(aVal, head) -> (f aVal, head)) listOfAHBoxes) listOfFuncHBoxes

-- | (Mostly) naturally a Monad. Given a function, f, which takes values in a, and produces (BoxMoveM b)'s, and a (BoxMoveM a), we produce a (BoxMoveM b) as follows:
-- Given a HBox, apply the (BoxMoveM a) to it, to give a list of (a, HBox)'s. For each pair, we apply our function, f, to the first argument to get a (BoxMoveM b), which we subsequently apply to the hBox in the pair.
-- This gives a list of lists, which we flatten to produce a list of (b, HBox)'s, as wanted.
-- This is basically a combination of the State and List monads (so it's probable this is already built into Haskell, but oh well!)
-- !! WARNING !! - this may currently produce unwanted behaviour with using the same hypothesis twice for a single move (e.g. in Modus Ponens, about to test that now).
-- Should be possible to use guarding to prevent this in any case, but perhaps we can modify the Monad instance to deal with this.
-- f :: a -> (HBox -> [(b, HBox)])
-- x :: HBox -> [(a, HBox)]
-- x >>= f :: HBox -> [(b, HBox)]
instance Monad BoxMoveM where
  BoxMoveM x >>= f = BoxMoveM $ \hBox -> let
    listOfAHBoxes = x hBox
    listOfBBoxes = concatMap (\(aVal, head) -> let BoxMoveM m = f aVal in m head) listOfAHBoxes
    in listOfBBoxes

-- | We want to pattern match against particular types of expressions (e.g. if they start with a Forall), so we want to deal with failure well when these pattern matches fail.
-- Returning the empty list, [], on failure ensures that when a pattern match fails, the move doesn't go ahead.
-- Thus only relevantly pattern matched hypotheses will ever be used.
instance MonadFail BoxMoveM where
  fail _ = BoxMoveM (const [])

-- | Fails if the condition is false, preventing the move from progressing. Otherwise continues without doing anything.
checkCondition :: Bool -> BoxMoveM ()
checkCondition cond = if cond then do return ()
else BoxMoveM $ const []





-- | Gets a hypothesis, does nothing
getHyp :: BoxMoveM (Expr, [QuantifiedVariable])
getHyp = BoxMoveM $ \hBox@(head, Box hyps targs) -> [(hyp, hBox) | hyp <- hyps]

getTarg :: BoxMoveM (Expr, [QuantifiedVariable])
getTarg = BoxMoveM $ \hBox@(head, Box hyps targs) -> [(targ, hBox) | targ <- targs]

-- | Gets nothing, adds a hypothesis
addHyp :: (Expr, [QuantifiedVariable]) -> BoxMoveM ()
addHyp hyp = BoxMoveM $ \(head, Box hyps targs) ->
  [((), (head, Box (hyp:hyps) targs))]

addTarg :: (Expr, [QuantifiedVariable]) -> BoxMoveM ()
addTarg targ = BoxMoveM $ \(head, Box hyps targs) ->
  [((), (head, Box hyps (targ:targs)))]

-- | updateHyp (e, f) (e', f') deletes the first occurence of the hypothesis (e, f) and adds (e', f')
-- This may have unexpected behaviour if there are multiple occurences of the same hypothesis in a box (which hopefully shouldn't happen)
-- or if no hypothesis of a particular form when we expected one (also shouldn't happen if used in conjunction with getHypothesis)
updateHyp :: (Expr, [QuantifiedVariable]) -> (Expr, [QuantifiedVariable]) -> BoxMoveM ()
updateHyp oldHyp newHyp = BoxMoveM $ \(head, Box hyps targs) ->
  [((), (head, Box (newHyp:delete oldHyp hyps) targs))]

updateTarg :: (Expr, [QuantifiedVariable]) -> (Expr, [QuantifiedVariable]) -> BoxMoveM ()
updateTarg oldTarg newTarg = BoxMoveM $ \(head, Box hyps targs) ->
  [((), (head, Box hyps (newTarg:delete oldTarg targs)))]

-- | Takes a list of InternalNames that have already been used and finds a new one
getNewInternalName :: [InternalName] -> VariableType -> InternalName
getNewInternalName usedNames varType = (varType, (+1) $ maxWithEmpty . map snd $ filter (\(t, n) -> t == varType) usedNames)
  where
    maxWithEmpty :: [Int] -> Int
    maxWithEmpty [] = -1
    maxWithEmpty list = maximum list

-- | Given a VariableType, retreives a fresh InternalName for it
getNewInternalNameM :: VariableType -> BoxMoveM InternalName
getNewInternalNameM varType = BoxMoveM $ \hBox@(TableauHead grave qZone deps, box) ->
  let newName = getNewInternalName (map qVarGetInternalName $ getSet deps) varType
  in [(newName, hBox)]

-- | Retrieves the current TableauHead
getHeadM :: BoxMoveM TableauHead
getHeadM = BoxMoveM $ \(head, box) ->
  [(head, (head, box))]

-- | Retrieves the current Box
getBoxM :: BoxMoveM Box
getBoxM = BoxMoveM $ \(head, box) -> [(box, (head, box))]

-- | Retrieves the current HBox
getHBoxM :: BoxMoveM HBox
getHBoxM = BoxMoveM $ \(head, box) -> [((head, box), (head, box))]

-- | Adds variable to the QZone list with dependencies.
-- We do this as a single function, as this avoid the risk of adding a Qvar to the QZone, but the subsequent dependency-adding move failing. If the latter fails, so should the former.
addToQZoneWithDeps :: QuantifiedVariable -> [(QuantifiedVariable, QuantifiedVariable)] -> BoxMoveM ()
addToQZoneWithDeps qVar newRels = BoxMoveM $ \(head@(TableauHead grave qZone deps@(Poset set rel)), box) ->
  let newDeps = addRels (addSetMember deps qVar) newRels
  in case newDeps of
    Nothing -> [] -- If trying to add the newRelations doesn't form a poset, we just do nothing
    Just x -> [((), (TableauHead grave (qVar:qZone) x, box))]

addToGraveWithDeps :: QuantifiedVariable -> [(QuantifiedVariable, QuantifiedVariable)] -> BoxMoveM ()
addToGraveWithDeps qVar newRels = BoxMoveM $ \(head@(TableauHead grave qZone deps@(Poset set rel)), box) ->
  let newDeps = addRels (addSetMember deps qVar) newRels
  in case newDeps of
    Nothing -> [] -- If trying to add the newRelations doesn't form a poset, we just do nothing
    Just x -> [((), (TableauHead (qVar:grave) qZone x, box))]

-- | Simply adds dependencies to the poset structure
addDeps :: [(QuantifiedVariable, QuantifiedVariable)] -> BoxMoveM ()
addDeps newRels = BoxMoveM $ \(head@(TableauHead grave qZone deps@(Poset set rel)), box) ->
  let newDeps = addRels deps newRels
  in case newDeps of
    Nothing -> [] -- If trying to add the newRelations doesn't form a poset, we return the failing value, []
    Just x -> [((), (TableauHead grave qZone x, box))]

-- | Returns what would happen if we added dependencies without actually doing anything.
-- This is useful in peeling, when we need to know whether a variable can be peeled fully or not, and then perform the appropriate peel.
addDepsHypothetical :: [(QuantifiedVariable, QuantifiedVariable)] -> BoxMoveM (Poset QuantifiedVariable)
addDepsHypothetical newRels = BoxMoveM $ \(head@(TableauHead grave qZone deps), box) ->
  let newDeps = addRels deps newRels
  in case newDeps of
    Nothing -> [] -- If trying to add the newRelations doesn't form a poset, we just do nothing
    Just x -> [(x, (head, box))]






monadMoveToBoxMove :: BoxMoveM a -> BoxMove
monadMoveToBoxMove (BoxMoveM move) hBox = map snd $ move hBox

-- TO-DO: can probably do this in a nicer way using List monad (making Tableau a Monad which acts sort of like list)
-- | Takes a BoxMove, an index, i, and a Tableau then performs that move on a Tableau by changing the i-th box and leaving the others untouched.
-- Returns a list as there may be multiple possible results from the same move
boxMoveOnIndex :: BoxMove -> Tableau -> Int -> [Tableau]
boxMoveOnIndex boxMove (Tableau head boxes) i
    | i < 0 || i >= length boxes = []
    | otherwise = let
        (as, ourBox:bs) = splitAt i boxes
        moveResults = boxMove (head, ourBox)
        in map (uncurry Tableau . (\(newHead, newBox) -> (newHead, as ++ newBox:bs))) moveResults

-- | Takes a BoxMove, then turns it into a normal move on Tableau by performing on all boxes and concating all possible results
boxMoveToMove :: BoxMove -> Move
boxMoveToMove boxMove tab = concatMap (boxMoveOnIndex boxMove tab) [0..(length . getBoxes $ tab) - 1]









-- <<<< OLD NON-MONADIC MOVE STUFF >>

-- | This specifies a move on a single expression (with quantification context given by a TableauHead)
-- Returns Nothing if the move is not possible. This primarily exists for writing tidying moves or logical moves more easily
type ExprMove = (TableauHead, (Expr, [QuantifiedVariable])) -> Maybe (TableauHead, (Expr, [QuantifiedVariable]))

-- | Takes an ExprMove, an index i, and a TableauHead/Box.
-- Then performs the move on the i-th hypothesis, if possible
exprMoveOnHypIndex :: ExprMove -> (TableauHead, Box) -> Int -> Maybe (TableauHead, Box)
exprMoveOnHypIndex exprMove (head, Box hyps targs) i
  | i < 0 && i >= length hyps = Nothing
  | otherwise = do
    let (as, ourHyp:bs) = splitAt i hyps
    moveResult <- exprMove (head, ourHyp)
    let (newHead, newHyp) = moveResult
    return (newHead, Box (as ++ newHyp : bs) targs)

exprMoveOnTargIndex :: ExprMove -> (TableauHead, Box) -> Int -> Maybe (TableauHead, Box)
exprMoveOnTargIndex exprMove (head, Box hyps targs) i
  | i < 0 && i >= length targs = Nothing
  | otherwise = do
    let (as, ourTarg:bs) = splitAt i targs
    moveResult <- exprMove (head, ourTarg)
    let (newHead, newTarg) = moveResult
    return (newHead, Box hyps (as ++ newTarg : bs))

-- | Takes an ExprMove, then turns it into a BoxMove by performing the ExprMove on all possible hypotheses
exprMoveToBoxMoveHyp :: ExprMove -> BoxMove
exprMoveToBoxMoveHyp exprMove (head, box@(Box hyps targs)) = mapMaybe (exprMoveOnHypIndex exprMove (head, box)) [0..(length hyps-1)]

exprMoveToBoxMoveTarg :: ExprMove -> BoxMove
exprMoveToBoxMoveTarg exprMove (head, box@(Box hyps targs)) = mapMaybe (exprMoveOnTargIndex exprMove (head, box)) [0..(length targs-1)]

-- TO-DO: Pretty sure there is a more abstract function which takes care of all of these functions, but not sure it's worth writing given this is all we need for now.
