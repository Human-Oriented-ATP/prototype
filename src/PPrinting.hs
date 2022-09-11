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
-- If free variable, will do the same thing, but looks to QZone to do this

data PrintingState = PS
  { getShowMap :: HashMap InternalName ExternalName
  , getUsedNames :: HashSet ExternalName
  , getCounter :: Int
  }

-- Not 100% sure what's going on with this, need to check on it.
getSuggestion' :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion' x = do
  PS m s n <- get
  let r = n
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

pprintBinderM :: String -> Maybe ExternalName -> Scoped -> State PrintingState String
pprintBinderM b sug sc = do
  (m, ExternalName sug') <- maybe getFresh getSuggestion sug
  s <- pprintExprM $ instantiate (Free m) sc
  return $ b ++ sug' ++ ", " ++ s

pprintExprM :: Expr -> State PrintingState String
-- special patterns (all these must come first!)
pprintExprM (Forall sug sc) = pprintBinderM "\8704" sug sc
pprintExprM (Exists sug sc) = pprintBinderM "\8707" sug sc
-- general patterns
pprintExprM t@(App _ _) = do
  let (f, x) = getAppChain t
  fs <- pprintExprM f
  xs <- traverse pprintExprM (reverse x)
  return $ fs ++ "(" ++ intercalate ", " xs ++ ")"
pprintExprM (Free x) = do
  (PS m _ _) <- get
  return $ getExternalName $ m M.! x
pprintExprM (Con s) = return $ strFromConStr s
pprintExprM (Abs sug sc) = pprintBinderM "λ" sug sc
pprintExprM (B _) = error "term not closed"


-- | Takes a QZone and finds a legitimate ordering of the quantified variables in the QZone.
orderQZone :: QZone -> [QuantifiedVariable]
orderQZone (Poset [] _) = []
orderQZone qZone@(Poset set rel) = let
  (nextUp:xs) = filter (not . hasParent qZone) set -- WARNING - this might cause the program to crash if pattern match fails, but shouldn't happen otherwise there isn't an ordering?
  in nextUp : orderQZone (Poset (delete nextUp set) rel)


-- | Takes a QZone and returns the corresponding PrintingState, given one already
-- (e.g. if a variable is quantified over, it should appear in the usedNames, and have a showMap entry)
getStartingPrintState :: QZone -> PrintingState -> PrintingState
getStartingPrintState (Poset [] _) state = state -- if there are no quantified variables in the QZone, we have nothing to do
getStartingPrintState qZone@(Poset set rel) (PS showMap usedNames counter) = let
  (qVar@(QVar quantifier exNm inNm):xs) = set
  newQZone = Poset xs []
  useInNm = findExNameFromInName usedNames inNm
  name = case exNm of
    Just str -> if not $ str `S.member` usedNames then str else useInNm
    Nothing -> useInNm
  newMap = M.insert inNm name showMap
  newUsedNames = S.insert name usedNames
  newState = PS newMap newUsedNames (max (counter + 1) (maximum (map qVarGetInternalName set)))
  in getStartingPrintState newQZone newState

-- | Takes a HashSet of used ExternalName's, and an InternalName, and generates a unique ExternalName for this
findExNameFromInName :: HashSet ExternalName -> InternalName -> ExternalName
findExNameFromInName usedNames inNm = let alph = map (\c -> [c]) ['a'..'z']
  in unusedNameFromOptions usedNames (basicNamesFromAlphabet alph)

unusedNameFromOptions :: HashSet ExternalName -> [ExternalName] -> ExternalName
unusedNameFromOptions s options = head $ filter (not . (`S.member` s)) options

basicNamesFromAlphabet :: [String] -> [ExternalName]
basicNamesFromAlphabet alph = [ExternalName (x ++ replicate n '\'') | n <- [0..], x <- alph]

pprintExprWithQZone :: QZone -> Expr -> String
pprintExprWithQZone qZone e = evalState (pprintExprM e) (getStartingPrintState qZone (PS mempty mempty 0))

pprintExpr :: Expr -> String
pprintExpr e = evalState (pprintExprM e) (PS mempty mempty 0)


showQZoneWithNamesNoDeps :: HashMap InternalName ExternalName -> QZone -> String
showQZoneWithNamesNoDeps showMap qZone@(Poset set rel) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  qListToStr = dealWithEmpty . intercalate ", " . map (\qVar -> (if qVarGetQuantifier qVar == "Forall" then "\8704" else "\8707") ++ getExternalName (showMap M.! qVarGetInternalName qVar))
  qZoneStr = qListToStr $ orderQZone qZone
  in "QZone: " ++ qZoneStr ++ "\n"

showQZoneWithNames :: HashMap InternalName ExternalName -> QZone -> String
showQZoneWithNames showMap qZone@(Poset set rel) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  qListToStr = dealWithEmpty . intercalate ", " . map (\qVar -> (if qVarGetQuantifier qVar == "Forall" then "\8704" else "\8707") ++ getExternalName (showMap M.! qVarGetInternalName qVar))
  qZoneStr = qListToStr $ orderQZone qZone
  depsStr = dealWithEmpty . intercalate ", " $ map (\(q1, q2) -> getExternalName (showMap M.! qVarGetInternalName q1) ++ "<" ++ getExternalName (showMap M.! qVarGetInternalName q2)) rel
  in "QZone: " ++ qZoneStr ++ "\n" ++ "Deps: " ++ depsStr ++ "\n"

showQZoneWithNamesRaw ::QZone -> String
showQZoneWithNamesRaw qZone@(Poset set rel) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  qListToStr = dealWithEmpty . intercalate ", " . map (\qVar -> (if qVarGetQuantifier qVar == "Forall" then "\8704" else "\8707") ++ show (qVarGetInternalName qVar))
  qZoneStr = qListToStr $ orderQZone qZone
  depsStr = dealWithEmpty . intercalate ", " $ map (\(q1, q2) ->  show (qVarGetInternalName q1) ++ "<" ++ show (qVarGetInternalName q2)) rel
  in "QZone: " ++ qZoneStr ++ "\n" ++ "Deps: " ++ depsStr ++ "\n"


pprintQBox :: QBox -> String
pprintQBox (qZone, Box hyps targs) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
  in
    "---- QZone ----\n" ++
    showQZoneWithNamesNoDeps showMap qZone ++
    "---- Hyps ----\n" ++
    dealWithEmpty ( intercalate "\n" (zipWith (\a b -> a ++ ": " ++ b) (map show [0..]) $ map (pprintExprWithQZone qZone . fst) hyps) ) ++ "\n" ++
    "---- Targs ----\n" ++
    dealWithEmpty ( intercalate "\n" (zipWith (\a b -> a ++ ": " ++ b) (map show [0..]) $ map (pprintExprWithQZone qZone . fst) targs) )


rawPrintQBox :: QBox -> String
rawPrintQBox (qZone, Box hyps targs) = let
  dealWithEmpty str = if str /= "" then str else "(empty)"
  PS showMap usedNames counter = getStartingPrintState qZone (PS mempty mempty 0)
  in
    "---- QZone ----\n" ++
    showQZoneWithNamesRaw qZone ++
    "---- Hyps ----\n" ++
    dealWithEmpty ( intercalate "\n" (zipWith (\a b -> a ++ ": " ++ b) (map show [0..]) $ map show hyps) ) ++ "\n" ++
    "---- Targs ----\n" ++
    dealWithEmpty ( intercalate "\n" (zipWith (\a b -> a ++ ": " ++ b) (map show [0..]) $ map show targs) )


pprintTab :: Tableau -> String
pprintTab (Tableau qZone boxes) = intercalate "\n\n" (map (\box -> pprintQBox (qZone, box)) boxes)

rawPrintTab :: Tableau -> String
rawPrintTab (Tableau qZone boxes) = intercalate "\n\n" (map (\box -> rawPrintQBox (qZone, box)) boxes)
