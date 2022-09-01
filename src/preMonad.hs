{-
Tableau implementation of foundations building on Bhavik's implementation from the Org Github
-}

module Lib where

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}

import Poset
import GHC.Base (VecElem(Int16ElemRep))
import Debug.Trace
import Control.Monad.State
import Data.Hashable
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.String (IsString(..))
import Data.List
import Data.Maybe (mapMaybe)

-- ??? Perhaps this isn't the best way to do it, but let's stick with it for now ???
data VariableType = TReal | TNatural | TPoint |TSet | TTopSpace | TFunction | TProperty
    deriving (Show, Eq)

instance Hashable VariableType where
  hashWithSalt n varType = hashWithSalt n $ show varType

instance Hashable ExternalName where
  hashWithSalt n (ExternalName str) = hashWithSalt n str


-- | Simply a suggestion for an external name when printed for viewing by the user.
newtype ExternalName = ExternalName {getExternalName :: String}
    deriving (Eq)

instance Show ExternalName where
  show (ExternalName string) = string

-- | Internal name used by program to keep track of different free variables.
type InternalName = (VariableType, Int)

-- Convenience
instance IsString ExternalName where
  fromString = ExternalName

data Expr
    = App Expr Expr
    -- Function application
    | Abs (Maybe ExternalName) VariableType Scoped
    -- ^ Abstraction. The (Maybe ExternalName) represents the suggested name for a given variable. VariableType determines what the type of the abstracted variable is.
    | Free InternalName
    -- ^ Free variable. In practice, a free variable will ONLY exist if it is quantified in the QZone / GYard, in which type information will be included, hence we do not include this information here.
    | Con String
    -- ^ Constant.
    | B Int
    -- ^ Bound variable (bound in an abstraction). Type not specified as this information is available in the abstraction.
    deriving (Show, Eq)

-- Scoped expression. Simply syntactic sugar to dilineate when an expression contains a bound variable which has not yet been assigned to an abstraction. A scoped expression should only contain a single such ("dangling") variable
newtype Scoped = Sc Expr
    deriving (Show, Eq)

-- | Check for equality of expressions up to alpha-equivalence.
class AlphaEq t where
  (~=) :: t -> t -> Bool

-- | Equality of scoped expressions, up to alpha equivalence.
instance AlphaEq Scoped where
  Sc x ~= Sc y = x ~= y

-- | Equality of expressions, up to alpha equivalence.
instance AlphaEq Expr where
  App f x ~= App g y = f ~= g && x ~= y
  Abs _ varType1 x ~= Abs _ varType2 y = (x ~= y) && (varType1 == varType2)
  Free n  ~= Free m  = n == m
  Con s   ~= Con t   = s == t
  B i     ~= B j     = i == j
  _       ~= _       = False


-- Applying function to several arguments
apps :: Expr -> [Expr] -> Expr
apps = foldl App

-- f                       -> (f, [])
-- App f x                 -> (f, [x])
-- App (App f x) y         -> (f, [y, x])
-- App (App (App g x) y) z -> (g, [z, y, x])
getAppChain :: Expr -> (Expr, [Expr])
getAppChain (App f x) = (g, x:t)
  where (g, t) = getAppChain f
getAppChain t = (t, [])

-- | Unary application of a constant function to an expression.
pattern UApp :: String -> Expr -> Expr
pattern UApp f x = App (Con f) x

-- | Binary application of a constant function to an expression.
pattern BApp :: String -> Expr -> Expr -> Expr
pattern BApp f x y = App (App (Con f) x) y

-- | The conjunction of two expressions.
pattern And :: Expr -> Expr -> Expr
pattern And x y = BApp "and" x y

-- | The disjunction of two expressions.
pattern Or :: Expr -> Expr -> Expr
pattern Or x y = BApp "or" x y

-- | The implication of two expressions.
pattern Implies :: Expr -> Expr -> Expr
pattern Implies x y = BApp "implies" x y

-- | The negation of an expression.
pattern Not :: Expr -> Expr
pattern Not x = UApp "not" x

-- | Equality of two expressions.
pattern Eq :: Expr -> Expr -> Expr
pattern Eq x y = BApp "eq" x y

-- | Forall x y z is the expression   -   \forall x : (type y), z.
-- Note that z has to be a Scoped expression
pattern Forall :: Maybe ExternalName -> VariableType -> Scoped -> Expr
pattern Forall exNm varType sc = UApp "forall" (Abs exNm varType sc)

pattern Exists :: Maybe ExternalName -> VariableType -> Scoped -> Expr
pattern Exists exNm varType sc = UApp "exists" (Abs exNm varType sc)

-- | Abstracts a free variable (specified by an InternalName) in an expression, returning a Scoped expression.
-- | The idea is that this will then be Abs-ed to create an abstraction.
abstract :: InternalName -> Expr -> Scoped
abstract inNm expr = Sc (nameTo 0 expr) where
  nameTo i (App f x)       = App (nameTo i f) (nameTo i x)
  nameTo i (Abs exNm varType (Sc scopedExpr)) = Abs exNm varType (Sc (nameTo (i+1) scopedExpr))
  nameTo i (Free m)
    | m == inNm            = B i
  nameTo _ t               = t -- otherwise, B and Con cases

-- | Instantiates the abstracted variable in a Scoped expression (not an Abs expression, but rather the Scoped inside of it) with the specified expression.
-- If the Expr is a (Free InternalName) then acts as an inverse to abstract.
instantiate :: Expr -> Scoped -> Expr
instantiate im (Sc b) = replace 0 b where
  replace i (Abs exNm varType (Sc scopedExpr)) = Abs exNm varType (Sc (replace (i+1) scopedExpr))
  replace i (App f x) = App (replace i f) (replace i x)
  replace i (B m)
    | i == m    = im
  replace _ t = t

-- | Takes an expression containing a free variable (specified by an InternalName) and abstracts the free variable (using the specified variableType), then Forall's it
forall :: Maybe ExternalName -> VariableType -> InternalName -> Expr -> Expr
forall x varType internalName expr = Forall x varType (abstract internalName expr)

exists :: Maybe ExternalName -> VariableType -> InternalName -> Expr -> Expr
exists x varType internalName expr = Exists x varType (abstract internalName expr)

-- | Instantiate an abstraction by entering the Scoped
instantiateAbs :: Expr -> Expr -> Maybe (Maybe ExternalName, Expr)
instantiateAbs (Abs exNm varType expr) x = Just (exNm, instantiate x expr)
instantiateAbs _         _ = Nothing

-- | Instantiates a forall by entering the Forall AND the Scoped
insantiateForall :: Expr -> Expr -> Maybe (Maybe ExternalName, Expr)
insantiateForall (Forall exNm varType scopedExpr) x = Just (exNm, instantiate x scopedExpr)
insantiateForall _ _ = Nothing



type Quantifier = String
data QuantifiedVariable = QVar {qVarGetQuantifier :: Quantifier, qVarGetExternalName :: Maybe ExternalName, qVarGetInternalName :: InternalName, getVarGetVarType :: VariableType}
  deriving (Eq)

instance Show QuantifiedVariable where
  show (QVar quantifier _ inNm _) = case quantifier of
    "Forall" -> "∀" ++ show inNm
    "Exists" -> "∃" ++ show inNm
    x -> "λ" ++ show inNm

-- All grave variables are quantified by a ForAll, so no need to specify quantifiers
type Grave = [QuantifiedVariable]
type QZone = [QuantifiedVariable]

-- The part of tableau storing peeled quantification inforamtion
data TableauHead = TableauHead {getGrave :: Grave,
                                getQZone :: QZone,
                                getDeps :: Poset QuantifiedVariable}

instance Show TableauHead where
  show (TableauHead grave qZone (Poset set rel)) = "Grave: " ++ show grave ++ "\n" ++ "QZone: " ++ show qZone ++ "\n" ++ "Deps: " ++ show rel ++ "\n"

instance Show Tableau where
  show (Tableau head boxes) = show head ++ intercalate "\n" (map show boxes)


-- We use pairs (Expr, [QuantifiedVariable]). The expression represents a hypothesis/target, and the list of quantified variables stores all the free variables in a given expression - necessary for peeling.
data Box = Box {getHyps :: [(Expr, [QuantifiedVariable])],
                getTargs :: [(Expr, [QuantifiedVariable])]} deriving (Show)

data Tableau = Tableau {getHead :: TableauHead,
                        getBoxes :: [Box]}



-- | Returns a list of tableaus because the same move could have multiple results (e.g. for splitting, depending on which statement it's applied to)
type Move = Tableau -> [Tableau]

-- | This specifies a move on a single box (noting all boxes share a single TableauHead). This is usually more natural.
type BoxMove = (TableauHead, Box) -> [(TableauHead, Box)]

-- | This specifies a move on a single expression (with quantification context given by a TableauHead)
-- Returns Nothing if the move is not possible. This primarily exists for writing tidying moves or logical moves more easily
type ExprMove = (TableauHead, (Expr, [QuantifiedVariable])) -> Maybe (TableauHead, (Expr, [QuantifiedVariable]))

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

-- | Takes a TableauHead and finds a legitimate ordering of the quantified variables in the head.
-- Grave variables are Forall quantified so can come in any order, provided they are before the qZone
orderQuantifiers :: TableauHead -> [QuantifiedVariable]
orderQuantifiers (TableauHead grave qZone deps) = grave ++ orderQZone qZone deps
  where
    orderQZone :: QZone -> Poset QuantifiedVariable -> [QuantifiedVariable]
    orderQZone [] poset = []
    orderQZone qZone poset@(Poset set rel) = let
      (nextUp:xs) = filter (not . hasParent poset) qZone -- WARNING - this might cause the program to crash if pattern match fails
      in nextUp : orderQZone (delete nextUp qZone) (Poset (delete nextUp set) rel)




isUniversallyQuantified :: Expr -> Bool
isUniversallyQuantified (Forall x y z) = True
isUniversallyQuantified _ = False

isExistentiallyQuantified :: Expr -> Bool
isExistentiallyQuantified (Exists x y z) = True
isExistentiallyQuantified _ = False


-- | Takes a list of InternalNames that have already been used and finds a new one
getNewInternalName :: [InternalName] -> VariableType -> InternalName
getNewInternalName usedNames varType = (varType, (+1) $ maxWithEmpty . map snd $ filter (\(t, n) -> t == varType) usedNames)
  where
    maxWithEmpty :: [Int] -> Int
    maxWithEmpty [] = -1
    maxWithEmpty list = maximum list

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


peelExistentialTargetBox = exprMoveToBoxMoveTarg peelExistentialTargetExpr
peelExistentialTarget = boxMoveToMove peelExistentialTargetBox
peelUniversalTargetBox = exprMoveToBoxMoveTarg peelUniversalTargetExpr
peelUniversalTarget = boxMoveToMove peelUniversalTargetBox


-- TO-DO: Again, pretty sure there is a more abstract function which takes care of the various peeling/metavariable creation rules. Not going to mess around with this for now, but there may be some genuinely interesting theoretical points here, anyway.
-- type BoxMove = (TableauHead, Box) -> [(TableauHead, Box)]

-- | If we have a hypothesis (\forall x, P(x) \implies Q(x)) and another hypothesis P(y), then we can deduce Q(y)
{-mpUniversalUsingHypBox :: BoxMove
mpUniversalUsingHypBox (head, box@(Box hyps targs)) = mapMaybe (uncurry (usingHyps (head, box))) [(h1, h2) | h1 <- hyps, h2 <- hyps, h1 /= h2]
  where
    usingHyps :: (TableauHead, Box) -> (Expr, [QuantifiedVariable]) -> (Expr, [QuantifiedVariable]) -> Maybe (TableauHead, Box)
    usingHyps (TableauHead grave qZone deps, Box hyps targs) (Forall exNm varType (Sc sc), freeVars) () = a
    usingHyps _ _ _ = a
-}

{-
How do we want to implement moves?
What's the minimum amount of information I need to specify?
Something like this would be perfect.

addHyp
addTarg
updateTarg
updateHyp

monadFail (monad state fail?) is something like the empty Tableau idk???

mP = do
  (Forall _ varType1 (Sc Implies p1 q1)) <- getHyp
  p1' <- getHyp

  guard p1' has freeVar of type varType1, and instantiating this in p1 gives p1'

  return (do
    addHyp q1 instantiated with correct variable
    )


peelUniversalTarg = do
  (Forall exNm varType (Sc sc)) <- getTarg
  update (Forall exNm varType (Sc sc)) (getNew)
  addQuantifier 

-}





























toProve = exists (Just $ ExternalName "x") TNatural (TNatural, 0) (forall (Just $ ExternalName "y") TNatural (TNatural, 1) (Eq (Free (TNatural, 0)) (Free (TNatural, 1))))
exprMoveTest = (TableauHead [] [] (Poset [] []), (toProve, []))

Just result = peelExistentialTargetExpr exprMoveTest
Just result2 = peelUniversalTargetExpr result

testGrave = [] :: [QuantifiedVariable]
testQZone = [] :: [QuantifiedVariable]
testDeps = Poset [] []
testHead = TableauHead testGrave testQZone testDeps
testBox = Box [] [(toProve, [])]
testBoxes = [testBox] :: [Box]
testTab = Tableau testHead testBoxes

toProve2 = exists (Just $ ExternalName "x") TNatural (TNatural, 0) (forall (Just $ ExternalName "y") TNatural (TNatural, 1) (Eq (Free (TNatural, 0)) (Free (TNatural, 1))))


someFunc :: IO ()
someFunc = putStrLn "someFunc"
