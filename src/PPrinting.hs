module PPrinting where

import Box
import Poset
import Lib
import TableauFoundation
import Data.Hashable
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.String (IsString(..))
import Data.List
import Control.Monad.State

import Debug.Trace


-- << Pretty printing expressions >>
-- If bound variable, will look for an external name and use that if it's not taken - if it doesn't exist, or is taken, it will use an internal name
-- If free variable, will do the same thing, but looks to TableauHead to do this

data PrintingState = PS
  { getShowMap :: HashMap InternalName ExternalName
  , getUsedNames :: HashSet ExternalName
  , getCounter :: Int
  }

-- Not 100% sure what's going on with this, need to check on it.
getSuggestion' :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion' x = do
  PS m s n <- get
  let r = (TPoint, n)
  put (PS (M.insert r x m) (S.insert x s) (n+1))
  return (r, x)

basicNames :: [ExternalName]
basicNames = [ExternalName (x : replicate n '\'') | n <- [0..], x <- alph]
  where alph = "abcdefghijklmnopqrstuvwxyz"

unusedName :: HashSet ExternalName -> ExternalName
unusedName s = head $ filter (not . (`S.member` s)) basicNames

getFresh :: State PrintingState (InternalName, ExternalName)
getFresh = do
  (PS _ u _) <- get
  getSuggestion' (unusedName u)

getSuggestion :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion x = do
  (PS _ y _) <- get
  if x `S.member` y
     then getFresh
     else getSuggestion' x

pprintBinderM :: String -> VariableType -> Maybe ExternalName -> Scoped -> State PrintingState String
pprintBinderM b varType sug sc = do
  (m, ExternalName sug') <- maybe getFresh getSuggestion sug
  s <- pprintExprM $ instantiate (Free m) sc
  return $ b ++ sug' ++ ":" ++ tail (show varType) ++ ", " ++ s

pprintExprM :: Expr -> State PrintingState String
-- special patterns (all these must come first!)
pprintExprM (Forall sug varType sc) = pprintBinderM "\8704" varType sug sc
pprintExprM (Exists sug varType sc) = pprintBinderM "\8707" varType sug sc
-- general patterns
pprintExprM t@(App _ _) = do
  let (f, x) = getAppChain t
  fs <- pprintExprM f
  xs <- traverse pprintExprM (reverse x)
  return $ fs ++ "(" ++ intercalate ", " xs ++ ")"
pprintExprM (Free x) = do
  (PS m _ _) <- get
  return $ getExternalName $ m M.! x
pprintExprM (Con s) = return s
pprintExprM (Abs sug varType sc) = pprintBinderM "λ" varType sug sc
pprintExprM (B _) = error "term not closed"


-- | Takes a TableauHead and finds a legitimate ordering of the quantified variables in the head.
-- Grave variables are Forall quantified so can come in any order, provided they are before the qZone
orderQZoneQuantifiers :: TableauHead -> [QuantifiedVariable]
orderQZoneQuantifiers (TableauHead grave qZone deps) = orderQZone qZone deps
  where
    orderQZone :: QZone -> Poset QuantifiedVariable -> [QuantifiedVariable]
    orderQZone [] poset = []
    orderQZone qZone poset@(Poset set rel) = let
      (nextUp:xs) = filter (not . hasParent poset) qZone -- WARNING - this might cause the program to crash if pattern match fails
      in nextUp : orderQZone (delete nextUp qZone) (Poset (delete nextUp set) rel)

orderQuantifiers :: TableauHead -> [QuantifiedVariable]
orderQuantifiers head@(TableauHead grave qZone deps) = grave ++ orderQZoneQuantifiers head

-- | Takes a TableauHead and returns the corresponding PrintingState, given one already
-- (e.g. if a variable is quantified over, it should appear in the usedNames, and have a showMap entry)
getStartingPrintState :: TableauHead -> PrintingState -> PrintingState
getStartingPrintState (TableauHead _ _ (Poset [] _)) state = state -- if there are no quantified variables in the head, we have nothing to do
getStartingPrintState (TableauHead _ _ deps) (PS showMap usedNames counter) = let
  (qVar@(QVar quantifier exNm inNm varType):xs) = getSet deps
  newHead = TableauHead [] [] (Poset xs [])
  useInNm = findExNameFromInName usedNames inNm
  name = case exNm of
    Just str -> if not $ str `S.member` usedNames then str else useInNm
    Nothing -> useInNm
  newMap = M.insert inNm name showMap
  newUsedNames = S.insert name usedNames
  newState = PS newMap newUsedNames 0
  in getStartingPrintState newHead newState

-- | Takes a HashSet of used ExternalName's, and an InternalName, and generates a unique ExternalName for this
findExNameFromInName :: HashSet ExternalName -> InternalName -> ExternalName
findExNameFromInName usedNames varType =
  let
    alph = case varType of
      (TReal, _) -> reals
      (TNatural, _) -> naturals
      (TPoint, _) -> points
      (TSet, _) -> sets
      (TTopSpace, _) -> topSpaces
      (TFunction, _) -> functions
      (TProperty, _) -> properties
      where
        reals = ["ε", "δ", "θ", "η", "ζ"]
        naturals = ["n", "m", "k", "l", "i", "j"]
        points = ["x", "y", "z", "u", "v", "w"]
        sets = ["A", "B", "C", "D", "E"]
        topSpaces = ["X", "Y", "Z"]
        functions = ["f", "g", "h"]
        properties = ["P", "Q", "R"]

  in unusedNameFromOptions usedNames (basicNamesFromAlphabet alph)

unusedNameFromOptions :: HashSet ExternalName -> [ExternalName] -> ExternalName
unusedNameFromOptions s options = head $ filter (not . (`S.member` s)) options

basicNamesFromAlphabet :: [String] -> [ExternalName]
basicNamesFromAlphabet alph = [ExternalName (x ++ replicate n '\'') | n <- [0..], x <- alph]

pprintExprWithHead :: TableauHead -> Expr -> String
pprintExprWithHead head e = evalState (pprintExprM e) (getStartingPrintState head (PS mempty mempty 0))

pprintExpr :: Expr -> String
pprintExpr e = evalState (pprintExprM e) (PS mempty mempty 0)



showHeadWithNames :: HashMap InternalName ExternalName -> TableauHead -> String
showHeadWithNames showMap head@(TableauHead grave qZone (Poset set rel)) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  qListToStr = dealWithEmpty . intercalate ", " . map (\qVar -> (if qVarGetQuantifier qVar == "Forall" then "\8704" else "\8707") ++ getExternalName (showMap M.! qVarGetInternalName qVar) ++ ":" ++ tail (show (qVarGetVarType qVar)))
  graveStr = qListToStr grave
  qZoneStr = qListToStr $ orderQZoneQuantifiers head
  depsStr = dealWithEmpty . intercalate ", " $ map (\(q1, q2) -> getExternalName (showMap M.! qVarGetInternalName q1) ++ "<" ++ getExternalName (showMap M.! qVarGetInternalName q2)) rel
  in "Grave: " ++ graveStr ++ "\n" ++ "QZone: " ++ qZoneStr ++ "\n" ++ "Deps: " ++ depsStr ++ "\n"


pprintHBox :: HBox -> String
pprintHBox (head, Box hyps targs) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  PS showMap usedNames counter = getStartingPrintState head (PS mempty mempty 0)
  in
    "---- Head ----\n" ++
    showHeadWithNames showMap head ++
    "---- Hyps ----\n" ++
    dealWithEmpty ( intercalate "\n" (map (pprintExprWithHead head . fst) hyps) ) ++ "\n" ++
    "---- Targs ----\n" ++
    dealWithEmpty ( intercalate "\n" (map (pprintExprWithHead head . fst) targs) )



-- TO-DO: come up with a comprenhensive list of test moves to make sure things are behaving as expected.
-- Of course, this should include weird edge cases, behaviour when multiple identical expressions are present, and interaction of expressions with themselves (which could happen without guarding because of how Monadic bind is implemented)

-- <<<< TESTING AREA FOR MOVES >>>>

-- Peeling targets
at1 = exists (Just $ ExternalName "x") TNatural (TNatural, 0) (forall (Just $ ExternalName "y") TNatural (TNatural, 0) (exists (Just $ ExternalName "z") TNatural (TNatural, 1) (Eq (Free (TNatural, 0)) (Free (TNatural, 1)))))
aBox = Box [] [(at1, [])]
aHead = TableauHead [] [] (Poset [] [])
aHBox = (aHead, aBox)
aResult = head $ peelExistentialTargBox aHBox >>= peelUniversalTargBox >>= peelExistentialTargBox
aStr = pprintHBox aResult


-- Universal modus ponens with hyp
bh1 = forall (Just $ ExternalName "x") TNatural (TNatural, 0) $
    Implies (Eq (UApp "succ" (Free (TNatural, 0))) (Con "1")) (Eq (Free (TNatural, 0)) (Con "0"))

bh2= Eq (UApp "succ" (Free (TNatural, 1))) (Con "1")

bTestHead = TableauHead [QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural] [] (Poset [QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural] [])
bTestBox = Box [(bh1, []), (bh2, [QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural])] []
bTestHBox = (bTestHead, bTestBox)
bResult = head $ mpUniversalHypsBox bTestHBox
bBeforeStr = pprintHBox bTestHBox
bStr = pprintHBox bResult


-- Implication in target tidy
ct1 = Implies (Eq (UApp "succ" (Free (TNatural, 0))) (UApp "succ" (Free (TNatural, 1)))) (Eq (Free (TNatural, 0)) (Free (TNatural, 1)))
cTestHead = TableauHead [QVar "Forall" (Just $ ExternalName "x") (TNatural, 0) TNatural, QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural] [] (Poset [QVar "Forall" (Just $ ExternalName "x") (TNatural, 0) TNatural, QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural] [])
cTestBox = Box [] [(ct1, [QVar "Forall" (Just $ ExternalName "x") (TNatural, 0) TNatural, QVar "Forall" (Just $ ExternalName "y") (TNatural, 1) TNatural])]
cTestHBox = (cTestHead, cTestBox)
cResult = head $ tidyImplInTargBox cTestHBox
cStr = pprintHBox cResult

