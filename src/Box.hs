{-
Tableau implementation of foundations building on Bhavik's implementation for FOL expressions from the Org Github
-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant if" #-}
module Box where

import Lib
import TableauFoundation
import Poset
import MovesFoundation

import Data.List

-- <<<< PEELING >>>>
-- | Peels a universal target (all the way to Grave if possible, otherwise to QZone)
peelUniversalTargBoxM :: BoxMoveM ()
peelUniversalTargBoxM = do
  (expr@(Forall exNm sc), freeVars) <- getTarg
  peeledName <- getNewInternalNameM
  let quantifiedVar = QVar "Forall" exNm peeledName

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  posetAfterAdding <- addDepsHypothetical newDeps -- Note if this fails, the value will be [], which will stop the move from doing anything
  (TableauHead grave qZone head) <- getHeadM
  let isFullPeel = and [not $ isBefore posetAfterAdding y quantifiedVar | y <- qZone]

  updateTarg (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  if isFullPeel then addToGraveWithDeps quantifiedVar []
  else addToQZoneWithDeps quantifiedVar newDeps

-- | Peels an existential target, creating a metavariable
peelExistentialTargBoxM :: BoxMoveM ()
peelExistentialTargBoxM = do
  (expr@(Exists exNm sc), freeVars) <- getTarg
  peeledName <- getNewInternalNameM
  let quantifiedVar = QVar "Exists" exNm peeledName

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  updateTarg (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  addToQZoneWithDeps quantifiedVar newDeps

-- | Peels an existential hypothesis (all the way to Grave if possible, otherwise to QZone)
peelExistentialHypBoxM :: BoxMoveM ()
peelExistentialHypBoxM = do
  (expr@(Exists exNm sc), freeVars) <- getHyp
  peeledName <- getNewInternalNameM
  let quantifiedVar = QVar "Forall" exNm peeledName

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  posetAfterAdding <- addDepsHypothetical newDeps -- Note if this fails, the value will be [], which will stop the move from doing anything
  (TableauHead grave qZone head) <- getHeadM
  let isFullPeel = and [not $ isBefore posetAfterAdding y quantifiedVar | y <- qZone]

  updateHyp (expr, freeVars) (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  if isFullPeel then addToGraveWithDeps quantifiedVar newDeps
  else addToQZoneWithDeps quantifiedVar newDeps

-- | There's also peelUniversalHypBoxM, which would make a metavariable, but I'm personally against this  unless the original hypothesis is kept, because it could make a problem unsolveable if the hypothesis needs to be applied twice
-- I think there's also something to be said about this move being the same as committing to hypothesis, effectively.
-- Anyway, for now I'll implement it this way.
peelUniversalHypBoxM :: BoxMoveM ()
peelUniversalHypBoxM = do
  (expr@(Forall exNm sc), freeVars) <- getHyp
  peeledName <- getNewInternalNameM
  let quantifiedVar = QVar "Exists" exNm peeledName

  let newDeps = [(y, quantifiedVar) | y <- freeVars]
  addHyp (instantiate (Free peeledName) sc, quantifiedVar:freeVars)

  addToQZoneWithDeps quantifiedVar newDeps


-- <<<< TIDYING >>>>
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

-- | Splits hypothesis of form P^Q into two hypotheses P, Q
splitConjHypM :: BoxMoveM ()
splitConjHypM = do
  (And p q, freeVars) <- getHyp
  removeHyp (And p q, freeVars)
  addHyp (p, freeVars)
  addHyp (q, freeVars)

-- | TO-DO: There's a question here about whether we want to form a new box. It's safer and better facilitates quantification restoration.
-- But it will likely result in more computation and the same steps being done multiple times in two different boxes.
-- For this reason it may be worth keeping track of which moves cannot make a problem state unsolvable and allowing only those moves to be performed on such a HBox before splitting.
splitConjTargM :: BoxMoveM ()
splitConjTargM = do
  (And p q, freeVars) <- getTarg
  removeTarg (And p q, freeVars)
  addTarg (p, freeVars)
  addTarg (q, freeVars)


-- <<<< Modus ponens and modus tollens >>>>
-- TO-DO: could there be issues of alpha equivalence here? I think it's fine for now, but if we somehow did end up with two alpha equivalent hypotheses this might need thinking about
-- | This is when we have a hypothesis of the form (forall x, P(x) \implies Q(x)) and another of the form P(y), and deduce Q(y)
mpUniversalHypsM :: BoxMoveM ()
mpUniversalHypsM = do
  (expr@(Forall exNm (Sc (Implies px qx))), freeVars) <- getHyp
  (py, freeVars'@(freeVar':rest')) <- getHyp -- Pattern match to ensure there is a free variable in the expression
  let toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in p', but not expr
  let singleMissing = (length toInstantiate' == 1)
  
  if not singleMissing then do fail " "
  else
    if not $ (expr /= py) && (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc px) == py)
      then do fail " "
    else do
      addHyp (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc qx), freeVars)

-- | When we have a hypothesis of the form (forall x, P(x) \implies Q(x)) and a target Q(y), then replace this target by the target P(y)
mtUniversalHypM :: BoxMoveM ()
mtUniversalHypM = do
  (expr@(Forall exNm (Sc (Implies px qx))), freeVars) <- getHyp
  (qy, freeVars'@(freeVar':rest')) <- getTarg
  let toInstantiate' = filter (`notElem` freeVars) freeVars' -- Finds the freeVars in q', but not expr
  let singleMissing = (length toInstantiate' == 1)

  if not singleMissing then do fail " "
  else
    if not $ (expr /= qy) && (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc qx) == qy)
      then do fail " "
    else do
      updateTarg (qy, freeVars') (instantiate (Free . qVarGetInternalName . head $ toInstantiate') (Sc px), freeVars')

-- | Above but with library result, which we must input, and a hypothesis, which we must input also (should we mandate the need for this - not strictly necessary, but seems to justify the move we will always have to know the relevant hypothesis, anyway).
-- Issues of alpha equivalence here for sure, as an expression will often contain free variables which will be quantified in the library statement within the expression, rather than in a TableauHead.
-- TO-DO: think about this!
{-
mpUniversalLibM :: Expr -> Expr -> BoxMoveM ()
mpUniversalLibM hyp libImpl = do
  case libImpl of
    (expr@(Forall exNm varType (Sc (Implies px qx))), freeVars) -> do
      return ()
    _ -> fail ""
-}

-- <<<< BASIC LOGIC >>>>




-- <<<< OTHER MOVES >>>>
commitToHypM :: BoxMoveM ()
commitToHypM = do

  return ()

-- | Takes an expression and returns the free variables in it. For this kind of a function, a set of internal names would really be better than the current list structure.
getFreeVars :: Expr -> [InternalName]
getFreeVars (App e1 e2) = (getFreeVars e1) `union` (getFreeVars e2)
getFreeVars (Abs exNm (Sc sc)) = getFreeVars sc
getFreeVars (Free inNm) = [inNm]
getFreeVars _ = []

-- | expandTargetM t1 t2 will expand the target t1 into the form t2. The move here isn't doing any heavy lifting. The difficult part will come with choosing which expansions to use (i.e. the two inputs for this function)
expandTargM :: Expr -> Expr -> BoxMoveM ()
expandTargM t1 t2 = do
  let t1Free = getFreeVars t1
  let t2Free = getFreeVars t2
  (TableauHead grave qZone (Poset set rel)) <- getHeadM
  let t1FreeQVars = map (\inNm -> (head $ filter (\qVar -> qVarGetInternalName qVar == inNm) set)) t1Free -- very inefficient. Will probably change data structure later, there's probably no need to store free variables as QuantifiedVariable's (just use InternalName's). If so, we should probably be storing a HashMap mapping InternalName to QVar?
  let t2FreeQVars = map (\inNm -> (head $ filter (\qVar -> qVarGetInternalName qVar == inNm) set)) t2Free

  updateTarg (t1, t1FreeQVars) (t2, t2FreeQVars)






-- TO-DO: may need to think a bit about how we write moves which heavily involve the quantification structure. Right now it's a bit cumbersome.
-- It would be quite nice to be able to write something like getExistentiallyQuantifiedQZoneVar, or something like that.
-- Perhaps this will just work out the box with the current monad structure, actually. Only concern I have is whether the TableauHead's aren't dealt with appropriately in the monadic bind.


-- | Instantiates a variable in the QZone (which is existentially quantified) with an Expr.
-- The instatiated expression will involve some free variables. To be valid, none of these variables can be preceded by the variable we're instantiating.
-- The poset structure must be updated when this occurs. Namely, all of the variables which had to come after the free variable now have to come after the extra ones.

instantiateExistential :: Expr -> QuantifiedVariable -> BoxMoveM ()
instantiateExistential expr qVar = do
  
  return ()

-- | If we have \forall x, \exists y, P(x, y) then can rewrite as \exists f:function, \forall x, P(x, f(x)).
-- I sense there may be proper-class related issues here, but I'm not entirely sure what the limitations are. This needs thinking about.
-- We may need to check that x and y are quantified over some set to make the interchange, thus ensuring the function is indeed a set-theoretic function.
skolemize :: BoxMoveM ()
skolemize = do
  
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

splitConjHypBox = monadMoveToBoxMove splitConjHypM
splitConjHyp = boxMoveToMove splitConjHypBox

expandTargBox :: Expr -> Expr -> BoxMove
expandTargBox t1 t2 = monadMoveToBoxMove $ expandTargM t1 t2
expandTarg :: Expr -> Expr -> Move
expandTarg t1 t2 = boxMoveToMove $ expandTargBox t1 t2


















-- <<<< OLD NON-MONADIC MOVE STUFF >>>>


-- | Peels a universal quantifier from a target, as an ExprMove. This will peel to Graveyard if possible (i.e. no dependencies in QZone) and QZone otherwise.
-- | The peeled variable is added to the free variables in the resulting expression, and we insist that the peeled variable come after all free variables that were already in it pre-peel.
-- | In terms of getting "as much commutation as possible", this can be improved by searching for more subtle rules, like if variables appear in separate parts of a conjunction.
peelUniversalTargetExpr :: ExprMove
peelUniversalTargetExpr (TableauHead grave qZone deps, (Forall exNm sc, freeVars)) = do
    let peeledName = getNewInternalName (map qVarGetInternalName $ getSet deps)
    let quantifiedVar = QVar "Forall" exNm peeledName
    newDeps <- addRels (addSetMember deps quantifiedVar) [(y, quantifiedVar) | y <- freeVars]  -- Add deps y < quantifiedVar for every y in freeVars
    let fullPeel = and [not $ isBefore newDeps y quantifiedVar | y <- qZone] -- Check if any deps y < quantifiedVar for any y in qZone
    let newExpr = instantiate (Free peeledName) sc
    let newFreeVars = quantifiedVar:freeVars
    return (if fullPeel then (TableauHead (quantifiedVar:grave) qZone newDeps, (newExpr, newFreeVars))
          else (TableauHead grave (quantifiedVar:qZone) newDeps, (newExpr, newFreeVars)))

peelUniversalTargetExpr _ = Nothing


peelExistentialTargetExpr :: ExprMove
peelExistentialTargetExpr (TableauHead grave qZone deps, (Exists exNm sc, freeVars)) = do
    let peeledName = getNewInternalName (map qVarGetInternalName $ getSet deps)
    let quantifiedVar = QVar "Exists" exNm peeledName
    newDeps <- addRels (addSetMember deps quantifiedVar) [(y, quantifiedVar) | y <- freeVars]  -- Add deps y < quantifiedVar for every y in freeVars
    let newExpr = instantiate (Free peeledName) sc
    let newFreeVars = quantifiedVar:freeVars
    return (TableauHead grave (quantifiedVar:qZone) newDeps, (newExpr, newFreeVars))

peelExistentialTargetExpr _ = Nothing





someFunc :: IO ()
someFunc = putStrLn "someFunc"
