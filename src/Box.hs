{-
Tableau implementation of foundations building on Bhavik's implementation for FOL expressions from the Org Github
-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant if" #-}
module Lib where

import ExpressionFoundation
import TableauFoundation
import Poset
import MovesFoundation

import Data.List

-- | Peels a universal target (all the way to Grave if possible, otherwise to QZone)
peelUniversalTargBoxM :: BoxMoveM ()
peelUniversalTargBoxM = do
  (expr@(Forall exNm varType sc), freeVars) <- getTarg
  peeledName <- getNewInternalNameM varType
  let quantifiedVar = QVar "Forall" exNm peeledName varType

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  posetAfterAdding <- addDepsHypothetical newDeps -- Note if this fails, the value will be [], which will stop the move from doing anything
  (TableauHead grave qZone head) <- getHeadM
  let isFullPeel = and [not $ isBefore posetAfterAdding y quantifiedVar | y <- qZone]

  updateTarg (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  if isFullPeel then addToGraveWithDeps quantifiedVar newDeps
  else addToQZoneWithDeps quantifiedVar newDeps

  return ()

-- | Peels an existential target, creating a metavariable
peelExistentialTargBoxM :: BoxMoveM ()
peelExistentialTargBoxM = do
  (expr@(Exists exNm varType sc), freeVars) <- getTarg
  peeledName <- getNewInternalNameM varType
  let quantifiedVar = QVar "Exists" exNm peeledName varType

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  updateTarg (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  addToQZoneWithDeps quantifiedVar newDeps

  return ()



-- | Peels an existential hypothesis (all the way to Grave if possible, otherwise to QZone)
peelExistentialHypBoxM :: BoxMoveM ()
peelExistentialHypBoxM = do
  (expr@(Exists exNm varType sc), freeVars) <- getHyp
  peeledName <- getNewInternalNameM varType
  let quantifiedVar = QVar "Forall" exNm peeledName varType

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  posetAfterAdding <- addDepsHypothetical newDeps -- Note if this fails, the value will be [], which will stop the move from doing anything
  (TableauHead grave qZone head) <- getHeadM
  let isFullPeel = and [not $ isBefore posetAfterAdding y quantifiedVar | y <- qZone]

  updateHyp (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  if isFullPeel then addToGraveWithDeps quantifiedVar newDeps
  else addToQZoneWithDeps quantifiedVar newDeps

  return ()

-- | There's also peelUniversalHypBoxM, which would make a metavariable, but I'm personally against this  unless the original hypothesis is kept, because it could make a problem unsolveable if the hypothesis needs to be applied twice
-- I think there's also something to be said about this move being the same as committing to hypothesis, effectively.
-- Anyway, for now I'll implement it this way.
peelUniversalHypBoxM :: BoxMoveM ()
peelUniversalHypBoxM = do
  (expr@(Forall exNm varType sc), freeVars) <- getHyp
  peeledName <- getNewInternalNameM varType
  let quantifiedVar = QVar "Exists" exNm peeledName varType

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  addHyp (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  addToQZoneWithDeps quantifiedVar newDeps

  return ()


-- | This is when we have a hypothesis of the form (forall x, P(x) \implies Q(x)) and another of the form P(y), and deduce Q(y)
mpUniversalHypsM :: BoxMoveM ()
mpUniversalHypsM = do
  (expr@(Forall exNm varType (Sc (Implies p q))), freeVars) <- getHyp
  (p', freeVars'@(freeVar':rest')) <- getHyp -- Pattern match to ensure there is a free variable in the expression
  let toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
  let singleMissing = (length toInstantiate' == 1)
  
  if not singleMissing then do fail " "
  else
    if not $ (expr /= p') && (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc p) == p')
      then do fail " "
    else do
      addHyp (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc q), freeVars)



-- TO-DO: could there be issues of alpha equivalence here? I think it's fine for now, but if we somehow did end up with two alpha equivalent hypotheses this might need thinking about

-- | If there is a SINGLE target of the form 
-- Currently doesn't deal with multiple targets, as in this case we need to create a new box
-- Perhaps we will always take the approach of splitting any multiple-target box into multiple boxes

-- TO-DO: I'm starting to get slightly concerned about not having Heads for every Box (so we just work on BoxHeads everywhere, maybe this is silly though)
-- the reason being that we might get situations where we e.g. want to restore the quantifier in one box, but not the other, for a particular free variable
-- shouldn't be too hard to adjust to this if so. Indeed, it will probably feel more natural this way.

tidyImplInTargM :: BoxMoveM ()
tidyImplInTargM = do
  (Implies p q, freeVars) <- getTarg
  Box hyps targs <- getBoxM
  
  if length targs /= 1 then do fail ""
  else do
    updateTarg (Implies p q, freeVars) (q, freeVars)
    addHyp (p, freeVars)
    return ()


getFreeVars :: Expr -> [InternalName]
getFreeVars expr = []

-- | Instantiates a variable in the QZone (which is existentially quantified) with an Expr.
-- The instatiated expression will involve some free variables. To be valid, none of these variables can be preceded by the variable we're instantiating.
-- The poset structure must be updated when this occurs. Namely, all of the variables which had to come after the free variable now have to come after the extra ones.
instantiateExistential :: Expr -> QuantifiedVariable -> BoxMoveM ()
instantiateExistential expr qVar = do
  
  return ()




-- TO-DO: There's got to be a better way to do this without making a class like "MovePrecursor" or something
peelUniversalTargBox = monadMoveToBoxMove peelUniversalTargBoxM
peelUniversalTarg = boxMoveToMove peelUniversalTargBox

peelExistentialTargBox = monadMoveToBoxMove peelExistentialTargBoxM
peelExistentialTarg = boxMoveToMove peelExistentialTargBox

mpUniversalHypsBox = monadMoveToBoxMove mpUniversalHypsM
mpUniversalHyps = boxMoveToMove mpUniversalHypsBox

tidyImplInTargBox = monadMoveToBoxMove tidyImplInTargM
tidyImplInTarg = boxMoveToMove tidyImplInTargBox






















-- <<<< OLD NON-MONADIC MOVE STUFF >>>>


-- | Peels a universal quantifier from a target, as an ExprMove. This will peel to Graveyard if possible (i.e. no dependencies in QZone) and QZone otherwise.
-- | The peeled variable is added to the free variables in the resulting expression, and we insist that the peeled variable come after all free variables that were already in it pre-peel.
-- | In terms of getting "as much commutation as possible", this can be improved by searching for more subtle rules, like if variables appear in separate parts of a conjunction.
peelUniversalTargetExpr :: ExprMove
peelUniversalTargetExpr (TableauHead grave qZone deps, (Forall exNm varType sc, freeVars)) = do
    let peeledName = getNewInternalName (map qVarGetInternalName $ getSet deps) varType
    let quantifiedVar = QVar "Forall" exNm peeledName varType
    newDeps <- addRels (addSetMember deps quantifiedVar) [(y, quantifiedVar) | y <- freeVars]  -- Add deps y < quantifiedVar for every y in freeVars
    let fullPeel = and [not $ isBefore newDeps y quantifiedVar | y <- qZone] -- Check if any deps y < quantifiedVar for any y in qZone
    let newExpr = instantiate (Free peeledName) sc
    let newFreeVars = quantifiedVar:freeVars
    return (if fullPeel then (TableauHead (quantifiedVar:grave) qZone newDeps, (newExpr, newFreeVars))
          else (TableauHead grave (quantifiedVar:qZone) newDeps, (newExpr, newFreeVars)))

peelUniversalTargetExpr _ = Nothing


peelExistentialTargetExpr :: ExprMove
peelExistentialTargetExpr (TableauHead grave qZone deps, (Exists exNm varType sc, freeVars)) = do
    let peeledName = getNewInternalName (map qVarGetInternalName $ getSet deps) varType
    let quantifiedVar = QVar "Exists" exNm peeledName varType
    newDeps <- addRels (addSetMember deps quantifiedVar) [(y, quantifiedVar) | y <- freeVars]  -- Add deps y < quantifiedVar for every y in freeVars
    let newExpr = instantiate (Free peeledName) sc
    let newFreeVars = quantifiedVar:freeVars
    return (TableauHead grave (quantifiedVar:qZone) newDeps, (newExpr, newFreeVars))

peelExistentialTargetExpr _ = Nothing





someFunc :: IO ()
someFunc = putStrLn "someFunc"