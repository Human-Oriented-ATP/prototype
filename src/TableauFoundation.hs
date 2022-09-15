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

-- | The part of tableau storing peeled quantification inforamtion.
type QZone = Poset QuantifiedVariable

-- | Type synonyms to make type declarations clearer. The expression part of the pair is by far the most important.
-- The only reason we need a list of QuantifiedVariables is to keep track of which free variables (InternalName's) appear in the expression
-- This could be deduced from the expression, but it'll be more computationally expensive
type Hyp = Expr
type Targ = Expr

-- | This stores hypothesis and targets. The only missing piece to form a full FOL statement is a TableauHead to contextualise the quantification.
data Box = Box {getHyps :: [Hyp],
                getTargs :: [Targ]} deriving (Eq, Show, Read)

-- | Other than closed expressions, this is the minimum natural object on which moves can act
type QBox = (QZone, Box)

-- | The final product - Tableau's. The only difference with HBox's is that there may be multiple Box's.
-- At the moment, I'm thinking of different Box's as being more or less independent, but it seems useful to build in the capacity to have many.
data Tableau = Tableau {getQZone :: QZone,
                        getBoxes :: [Box]}
                        deriving (Eq, Read, Show)







-- <<< FOR INTERFACE ? >>>

-- Another version of show for passing Tableau's to external interface and back
tableauToString :: Tableau -> String
tableauToString (Tableau qZone boxes) = "a"

-- A version of read for passing Tableau's to external interface and back
stringToTableau :: String -> Maybe Tableau
stringToTableau string = Nothing