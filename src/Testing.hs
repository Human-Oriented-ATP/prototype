module Testing where

import Lib
import TableauFoundation
import Poset
import BasicMoves
import LibraryMoves
import Data.Maybe
import Data.List
import Control.Monad
import PPrinting
import HoleExpr
import Debug.Trace


-- <<< MOVE TESTING >>>

-- IMPROVEMENT - have fixed the hacky need for negative InternalName's here using HoleExpr's, but this seemed to hit performance a bit
-- How can we improve this, and why does it affect performance?

openSetDefQZone = Poset [QVar "Forall" (Just $ ExternalName "M") (-1)
    , QVar "Forall" (Just $ ExternalName "d") (-2)
    , QVar "Forall" (Just $ ExternalName "A") (-3)] []
openSetDefH1 = holeFreeVars $ BApp (Pred "metric_on") (Free (-2)) (Free (-1))
openSetDefe = holeFreeVars $ TApp (Pred "open_in_metric") (Free (-3)) (Free (-2)) (Free (-1))
openSetDefe' = holeFreeVars $ forall (Just $ ExternalName "x") (0) $
    Implies (BApp (Pred "element_of") (Free (0)) (Free (-3))) $
    exists (Just $ ExternalName "delta") (1) $
    And (BApp (Pred "real_greater_than") (Free (1)) (Con $ Obj "0")) $
    forall (Just $ ExternalName "y") (2) $
    Implies (BApp (Pred "element_of") (Free (2)) (Free (-1))) $
    Implies (BApp (Pred "real_lesser_than") (App (App (Free (-2)) (Free (0))) (Free (2))) (Free (1))) $
    BApp (Pred "element_of") (Free (2)) (Free (-3))
openSetDefinition = LibraryEquivalence openSetDefQZone [openSetDefH1] [openSetDefe, openSetDefe']

intersectionDefQZone = Poset [ QVar "forall" (Just $ ExternalName "x") (-1)
    , QVar "forall" (Just $ ExternalName "A") (-2)
    , QVar "forall" (Just $ ExternalName "B") (-3)] []
intersectionDefe = holeFreeVars $ BApp (Pred "element_of") (Free (-1)) (BApp (Operator "set_intersection") (Free (-2)) (Free (-3)))
intersectionDefe' = holeFreeVars $ And (BApp (Pred "element_of") (Free (-1)) (Free (-2))) (BApp (Pred "element_of") (Free (-1)) (Free (-3)))
intersectionDef = LibraryEquivalence intersectionDefQZone [] [intersectionDefe, intersectionDefe']

-- IMPROVEMENT - for now we're storing this as an equivalence because the above code would be identical for an implication, but
-- need to clarify how we want either to work and implement separately.
-- Probably the most sensible way is to store equivalences as suggested, except with a set rather than a pair. Then appropriate function should take two indices giving which two expressions we want to exchange, and the appropriate substitution
-- then checks this is correct and performs equivalence on the desired expression. I guess we also want to specify the condition/hypothesis-mapping, but have the option for it to compute this manually?
-- we could trust that the substitution works if provided, but this would allow the function to create non-sound moves, so probably best not to do this.
-- Similarly, one way implications can just be stored as Tableau's, and we can implement library forward-reasoning and backward-reasoning separately in a similar way?
lesserThanTransQZone = Poset [QVar "Forall" (Just $ ExternalName "a") (-1)
    , QVar "Forall" (Just $ ExternalName "b") (-2)
    , QVar "Forall" (Just $ ExternalName "c") (-3)] []
lesserThanTransH1 = holeFreeVars $ BApp (Pred "real_lesser_than") (Free (-1)) (Free (-2))
lesserThanTranse = holeFreeVars $ BApp (Pred "real_lesser_than") (Free (-1)) (Free (-3))
lesserThanTranse' = holeFreeVars $  BApp (Pred "real_leq") (Free (-2)) (Free (-3))
lesserThanTrans = LibraryEquivalence lesserThanTransQZone [lesserThanTransH1] [lesserThanTranse, lesserThanTranse']

-- Intersection of open sets is open
f1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "d") (1) $
    forall (Just $ ExternalName "U") (2) $
    forall (Just $ ExternalName "V") (3) $
    Implies (TAnd
        (BApp (Pred "metric_on") (Free 1) (Free 0))
        (TApp (Pred "open_in_metric") (Free 2) (Free 1) (Free 0))
        (TApp (Pred "open_in_metric") (Free 3) (Free 1) (Free 0))) $
    TApp (Pred "open_in_metric") (BApp (Operator "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
fQZone = Poset [] []
fBox = Box [] [f1]
fQBox = (fQZone, fBox)
fTab = Tableau fQZone [fBox]

Just fResult' =
    tidyEverything fTab

Just fResult =
    tidyEverything fTab
    >>= boxToTabMove (libEquivTarg openSetDefinition (0, 1) 0) 0 >>= boxToTabMove (libEquivHyp openSetDefinition (0, 1) 1) 0 >>= boxToTabMove (libEquivHyp openSetDefinition (0, 1) 2) 0
    >>= tidyEverything >>= boxToTabMove (peelExistentialTargBox 0) 0 >>= tidyEverything
    >>= boxToTabMove (libEquivTarg intersectionDef (0, 1) 0) 1 >>= boxToTabMove (libEquivHyp intersectionDef (0, 1) 3) 1
    >>= tidyEverything
    >>= boxToTabMove (modusPonensBox 1 6) 1 >>= boxToTabMove (modusPonensBox 2 3) 1
    >>= tidyEverything
    >>= boxToTabMove (modusPonensBox 9 4) 1 >>= boxToTabMove (backwardsReasoningHypBox 11 1) 1
    >>= boxToTabMove (modusPonensBox 10 4) 1 >>= boxToTabMove (backwardsReasoningHypBox 12 0) 1
    >>= boxToTabMove (libEquivTarg lesserThanTrans (0, 1) 0) 1 >>= boxToTabMove (libEquivTarg lesserThanTrans (0, 1) 1) 1



-- Continuous in metric space
continuousDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f") (-1)
    , QVar "Forall" (Just $ ExternalName "d_X") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
continuousDefH1 = holeFreeVars $ BApp (Pred "metric_on") (Free (-2)) (Free (-3))
continuousDefH2 = holeFreeVars $ BApp (Pred "metric_on") (Free (-4)) (Free (-5))
continuousDefH3 = holeFreeVars $ TApp (Pred "function") (Free (-1)) (Free (-3)) (Free (-5))
continuousDefe = holeFreeVars $ PApp (Pred "continuous_in_metric_space") (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
continuousDefe' = holeFreeVars $
    forall (Just $ ExternalName "x") 0 $ Implies (BApp (Pred "element_of") (Free 0) (Free (-3))) $
    forall (Just $ ExternalName "epsilon") 1 $ Implies (BApp (Pred "real_greater_than") (Free 1) (Con $ Obj "0")) $
    exists (Just $ ExternalName "delta") 2 $ And (BApp (Pred "real_greater_than") (Free 2) (Con $ Obj "0")) $
    forall (Just $ ExternalName "y") 3 $ Implies (BApp (Pred "element_of") (Free 3) (Free (-3))) $
    Implies (BApp (Pred "real_lesser_than") (App (App (Free (-2)) (Free 0)) (Free 3)) (Free 2)) $
    BApp (Pred "real_lesser_than") (App (App (Free (-4)) (App (Free (-1)) (Free 0))) (App (Free (-1)) (Free 3))) (Free 1)
continuousDef = LibraryEquivalence continuousDefQZone [continuousDefH1, continuousDefH2, continuousDefH3] [continuousDefe, continuousDefe']



-- IMPROVEMENT - think about exactly how much information we include. For example, do we really need things like "metric_on" as conditions, given that this is implicit from the uniform_limit_of_functions_metric_space? I don't know.
-- gonna exclude it for now
uniformLimDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f_") (-1)
    , QVar "Forall" (Just $ ExternalName "f") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
uniformLimDefe = holeFreeVars $ PApp (Pred "uniform_limit_of_functions_metric_space") (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
uniformLimDefe' = holeFreeVars $ forall (Just $ ExternalName "theta") (0) $ Implies (BApp (Pred "real_greater_than") (Free 0) (Con $ Obj "0")) $
    exists (Just $ ExternalName "N") (1) $ And (BApp (Pred "element_of") (Free 1) (Con $ Obj "naturals")) $
    forall (Just $ ExternalName "n") (2) $ Implies (And (BApp (Pred "element_of") (Free 2) (Con $ Obj "naturals")) (BApp (Pred "real_greater_than") (Free 2) (Free 1))) $
    forall (Just $ ExternalName "x") (3) $ Implies (BApp (Pred "element_of") (Free 3) (Free (-3))) $
    BApp (Pred "real_lesser_than") (App (App (Free (-4)) (App (App (Free (-1)) (Free 2)) (Free 3))) (App (Free (-2)) (Free 3))) (Free 0)
uniformLimDef = LibraryEquivalence uniformLimDefQZone [] [uniformLimDefe, uniformLimDefe']

-- Uniform limit of cts functions is cts
g1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "Y") (1) $
    forall (Just $ ExternalName "d_X") (2) $
    forall (Just $ ExternalName "d_Y") (3) $
    forall (Just $ ExternalName "f") (4) $
    forall (Just $ ExternalName "f_") (5) $
    Implies (HAnd
        (BApp (Pred "metric_on") (Free 2) (Free 0))
        (BApp (Pred "metric_on") (Free 3) (Free 1))
        (TApp (Pred "function") (Free 4) (Free 0) (Free 1))
        (TApp (Pred "sequence_of_functions") (Free 5) (Free 0) (Free 1))
        (PApp (Pred "uniform_limit_of_functions_metric_space") (Free 5) (Free 4) (Free 0) (Free 3) (Free 1))
        (forall (Just $ ExternalName "n") (6) $ Implies (BApp (Pred "element_of") (Free 6) (Con $ Obj "naturals")) (PApp (Pred "continuous_in_metric_space") (App (Free 5) (Free 6)) (Free 2) (Free 0) (Free 3) (Free 1))))$
    PApp (Pred "continuous_in_metric_space") (Free 4) (Free 2) (Free 0) (Free 3) (Free 1)


gQZone = Poset [] []
gBox = Box [] [g1]
gQBox = (gQZone, gBox)
gTab = Tableau gQZone [gBox]

Just gResult = tidyEverything gTab >>= boxToTabMove (libEquivTargCondMap continuousDef (0, 1) [(0, 0), (1, 5), (2, 4)] 0) 0 >>= tidyEverything
     >>= boxToTabMove (peelExistentialTargBox 0) 0 >>= tidyEverything
     >>= boxToTabMove (libEquivHyp uniformLimDef (0, 1) 2) 1
     >>= boxToTabMove (peelUniversalHypBox 2) 1 >>= commitToHypothesis 10 1 >>= tidyEverything
     >>= boxToTabMove (peelUniversalHypBox 11) 1 >>= commitToHypothesis 12 1 >>= tidyEverything
     >>= boxToTabMove (modusPonensBox 12 6) 1 >>= boxToTabMove (modusPonensBox 12 8) 1 >>= tidyEverything
     >>= boxToTabMove (peelUniversalHypBox 1) 1 >>= commitToHypothesis 15 1
    -- >>= boxToTabMove (libEquivHyp continuousDef (0, 1) 15) 1 >>= tidyEverything
    -- >>= boxToTabMove (modusPonensBox 15 6) 1 >>= boxToTabMove (modusPonensBox 16 7) 1 >>= tidyEverything
    -- >>= boxToTabMove (modusPonensBox 18 8) 1



gResult' = tidyEverything gTab

at1 = exists (Just $ ExternalName "x") 0 (forall (Just $ ExternalName "y") 0 (exists (Just $ ExternalName "z") 1 (Eq (Free 0) (Free 1))))
aBox = Box [] [at1]
aHead = Poset [] []
aQBox = (aHead, aBox)
Just aResult = (peelExistentialTargBox 0) aQBox >>= (peelUniversalTargBox 0) >>= (peelExistentialTargBox 0)
aStr = pprintQBox aResult


-- Universal modus ponens with hyp
bh1 = forall (Just $ ExternalName "x") 0 $
    Implies (Eq (UApp (Operator "succ") (Free 0)) (Con (Obj "1"))) (Eq (Free 0) (Con (Obj "0")))

bh2= Eq (UApp (Operator "succ") (Free 1)) (Con (Obj "1"))

bTestHead = Poset [QVar "Forall" (Just $ ExternalName "y") 1] []
bTestBox = Box [bh1, bh2] []
bTestQBox = (bTestHead, bTestBox)
Just bResult = modusPonensBox 0 1 bTestQBox
bBeforeStr = pprintQBox bTestQBox
bStr = pprintQBox bResult


-- Implication in target tidy
ct1 = Implies (Eq (UApp (Operator "succ") (Free 0)) (UApp (Operator "succ") (Free 1))) (Eq (Free 0) (Free 1))
cTestHead = Poset [QVar "Forall" (Just $ ExternalName "x") 0, QVar "Forall" (Just $ ExternalName "y") 1] []
cTestBox = Box [] [ct1]
cTestQBox = (cTestHead, cTestBox)
cTestTab = Tableau cTestHead [cTestBox]
Just cResult = tidyImplInTarg 0 0 cTestTab
cStr = pprintTab cResult



-- Forwards and backwards reasoning
xh1 = holeFreeVars $ BApp (Pred "metric_on") (Free 1) (Free 0)
xh2 = holeFreeVars $ TApp (Pred "open_in_metric") (Free 2) (Free 1) (Free 0)
xh3 = holeFreeVars $ TApp (Pred "open_in_metric") (Free 3) (Free 1) (Free 0)
xt1 = holeFreeVars $ TApp (Pred "open_in_metric") (BApp (Operator "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
forwardReasoningTestLib = LibraryImplication (Poset [] []) [xh1, xh2, xh3] [xt1]

xQZone = Poset [QVar "Forall" (Just $ ExternalName "M") 0
    , QVar "Forall" (Just $ ExternalName "d") 1
    , QVar "Forall" (Just $ ExternalName "U") 2
    , QVar "Forall" (Just $ ExternalName "V") 3] []
xhh1 = BApp (Pred "metric_on") (Free 1) (Free 0)
xhh2 = TApp (Pred "open_in_metric") (Free 2) (Free 1) (Free 0)
xhh3 = TApp (Pred "open_in_metric") (Free 3) (Free 1) (Free 0)
xtt1 = TApp (Pred "open_in_metric") (BApp (Operator "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
xTab = Tableau xQZone [Box [xhh1, xhh3] [xtt1]]

Just a = boxToTabMove (libForwardReasoning forwardReasoningTestLib) 0 xTab
Just b = boxToTabMove (libBackwardReasoning forwardReasoningTestLib) 0 xTab

