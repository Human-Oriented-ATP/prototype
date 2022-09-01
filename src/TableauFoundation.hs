module TableauFoundation where

import Poset
import Lib

import Data.List

-- <<<< TYPES DEFINING WHAT A TABLEAU IS >>>>

type Quantifier = String
data QuantifiedVariable = QVar { qVarGetQuantifier :: Quantifier
                               , qVarGetExternalName :: Maybe ExternalName
                               , qVarGetInternalName :: InternalName
                               }
  deriving (Eq)

instance Show QuantifiedVariable where
  show (QVar quantifier _ inNm) = case quantifier of
    "Forall" -> "\8704" ++ show inNm
    "Exists" -> "\8707" ++ show inNm
    x -> "." ++ show inNm

-- | Graveyard and quantification zone.
type Grave = [QuantifiedVariable]
type QZone = [QuantifiedVariable]

-- | The part of tableau storing peeled quantification inforamtion (including Poset info on order of quantification).
data TableauHead = TableauHead {getGrave :: Grave,
                                getQZone :: QZone,
                                getDeps :: Poset QuantifiedVariable}

instance Show TableauHead where
  show (TableauHead grave qZone (Poset set rel)) = "Grave: " ++ show grave ++ "\n" ++ "QZone: " ++ show qZone ++ "\n" ++ "Deps: " ++ show rel ++ "\n"

instance Show Tableau where
  show (Tableau head boxes) = show head ++ intercalate "\n" (map show boxes)


-- | Type synonyms to make type declarations clearer. The expression part of the pair is by far the most important.
-- The only reason we need a list of QuantifiedVariables is to keep track of which free variables (InternalName's) appear in the expression
-- This could be deduced from the expression, but it'll be more computationally expensive
type Hyp = (Expr, [QuantifiedVariable])
type Targ = (Expr, [QuantifiedVariable])

-- | This stores hypothesis and targets. The only missing piece to form a full FOL statement is a TableauHead to contextualise the quantification.
data Box = Box {getHyps :: [Hyp],
                getTargs :: [Targ]} deriving (Show)

-- | Other than closed expressions, this is the minimum natural object on which moves can act
type HBox = (TableauHead, Box)

-- | The final product - Tableau's. The only difference with HBox's is that there may be multiple Box's.
-- At the moment, I'm thinking of different Box's as being more or less independent, but it seems useful to build in the capacity to have many.
data Tableau = Tableau {getHead :: TableauHead,
                        getBoxes :: [Box]}
