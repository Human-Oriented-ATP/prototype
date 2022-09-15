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
import Parser
import Debug.Trace
import ExistentialMoves


-- <<< MOVE TESTING >>>

-- IMPROVEMENT - have fixed the hacky need for negative InternalName's here using HoleExpr's, but this seemed to hit performance a bit
-- How can we improve this, and why does it affect performance?

openSetDefQZone = Poset [QVar "Forall" (Just $ ExternalName "M") (-1)
    , QVar "Forall" (Just $ ExternalName "d") (-2)
    , QVar "Forall" (Just $ ExternalName "A") (-3)] []
openSetDefH1 = holeFreeVars $ BApp "metric_on" (Free (-2)) (Free (-1))
openSetDefe = holeFreeVars $ TApp "open_in_metric" (Free (-3)) (Free (-2)) (Free (-1))
openSetDefe' = holeFreeVars $ forall (Just $ ExternalName "x") 0 $
    Implies (BApp "element_of" (Free 0) (Free (-3))) $
    exists (Just $ ExternalName "delta") 1 $
    And (BApp "real_greater_than" (Free 1) (Con "0")) $
    forall (Just $ ExternalName "y") 2 $
    Implies (BApp "element_of" (Free 2) (Free (-1))) $
    Implies (BApp "real_lesser_than" (App (App (Free (-2)) (Free 0)) (Free 2)) (Free 1)) $
    BApp "element_of" (Free 2) (Free (-3))
openSetDefinition = LibraryEquivalence openSetDefQZone [openSetDefH1] [openSetDefe, openSetDefe']

intersectionDefQZone = Poset [ QVar "forall" (Just $ ExternalName "x") (-1)
    , QVar "forall" (Just $ ExternalName "A") (-2)
    , QVar "forall" (Just $ ExternalName "B") (-3)] []
intersectionDefe = holeFreeVars $ BApp ( "element_of") (Free (-1)) (BApp ( "set_intersection") (Free (-2)) (Free (-3)))
intersectionDefe' = holeFreeVars $ And (BApp ( "element_of") (Free (-1)) (Free (-2))) (BApp ( "element_of") (Free (-1)) (Free (-3)))
intersectionDef = LibraryEquivalence intersectionDefQZone [] [intersectionDefe, intersectionDefe']

-- IMPROVEMENT - for now we're storing this as an equivalence because the above code would be identical for an implication, but
-- need to clarify how we want either to work and implement separately.
-- Probably the most sensible way is to store equivalences as suggested, except with a set rather than a pair. Then appropriate function should take two indices giving which two expressions we want to exchange, and the appropriate substitution
-- then checks this is correct and performs equivalence on the desired expression. I guess we also want to specify the condition/hypothesis-mapping, but have the option for it to compute this manually?
-- we could trust that the substitution works if provided, but this would allow the function to create non-sound moves, so probably best not to do this.
-- Similarly, one way implications can just be stored as Tableau's, and we can implement library forward-reasoning and backward-reasoning separately in a similar way?
Just lesserThanTransQZone = parseQZone "forall a, forall b, forall c"
Just lesserThanTransH1 = parseWithQZone lesserThanTransQZone "real_lesser_than(a, b)"
Just lesserThanTransH2 = parseWithQZone lesserThanTransQZone "real_leq(b, c)"
Just lesserThanTransT1 = parseWithQZone lesserThanTransQZone "real_lesser_than(a, c)"
lesserThanTrans = LibraryImplication lesserThanTransQZone
    (map holeFreeVars [lesserThanTransH1, lesserThanTransH2])
    (map holeFreeVars [lesserThanTransT1])

-- Intersection of open sets is open
f1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "d") (1) $
    forall (Just $ ExternalName "U") (2) $
    forall (Just $ ExternalName "V") (3) $
    Implies (TAnd
        (BApp ( "metric_on") (Free 1) (Free 0))
        (TApp ( "open_in_metric") (Free 2) (Free 1) (Free 0))
        (TApp ( "open_in_metric") (Free 3) (Free 1) (Free 0))) $
    TApp ( "open_in_metric") (BApp ( "set_intersection") (Free 2) (Free 3)) (Free 1) (Free 0)
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
    >>= boxToTabMove (libBackwardReasoning lesserThanTrans) 1 >>= boxToTabMove (libBackwardReasoning lesserThanTrans) 1


-- Sequence of functions
Just sequenceOfFunctionsQZone = parseQZone "forall X, forall Y, forall f_"
Just sequenceOfFunctionsT1 = parseWithQZone sequenceOfFunctionsQZone "sequence_of_functions(f_, X, Y)"
Just sequenceOfFunctionsT2 = parseWithQZone sequenceOfFunctionsQZone "forall n, implies(element_of(n, naturals), function(f_(n), X, Y))"
sequenceOfFunctions = LibraryEquivalence sequenceOfFunctionsQZone
    (map holeFreeVars [])
    (map holeFreeVars [sequenceOfFunctionsT1, sequenceOfFunctionsT2])

-- Continuous in metric space
continuousDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f") (-1)
    , QVar "Forall" (Just $ ExternalName "d_X") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
continuousDefH1 = holeFreeVars $ BApp "metric_on" (Free (-2)) (Free (-3))
continuousDefH2 = holeFreeVars $ BApp "metric_on" (Free (-4)) (Free (-5))
continuousDefH3 = holeFreeVars $ TApp "function" (Free (-1)) (Free (-3)) (Free (-5))
continuousDefe = holeFreeVars $ PApp "continuous_in_metric_space" (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
continuousDefe' = holeFreeVars $
    forall (Just $ ExternalName "x") 0 $ Implies (BApp "element_of" (Free 0) (Free (-3))) $
    forall (Just $ ExternalName "epsilon") 1 $ Implies (BApp "real_greater_than" (Free 1) (Con "0")) $
    exists (Just $ ExternalName "delta") 2 $ And (BApp "real_greater_than" (Free 2) (Con "0")) $
    forall (Just $ ExternalName "y") 3 $ Implies (BApp "element_of" (Free 3) (Free (-3))) $
    Implies (BApp "real_lesser_than" (App (App (Free (-2)) (Free 0)) (Free 3)) (Free 2)) $
    BApp "real_lesser_than" (App (App (Free (-4)) (App (Free (-1)) (Free 0))) (App (Free (-1)) (Free 3))) (Free 1)
continuousDef = LibraryEquivalence continuousDefQZone [continuousDefH1, continuousDefH2, continuousDefH3] [continuousDefe, continuousDefe']



-- IMPROVEMENT - think about exactly how much information we include. For example, do we really need things like "metric_on" as conditions, given that this is implicit from the uniform_limit_of_functions_metric_space? I don't know.
-- gonna exclude it for now
uniformLimDefQZone = Poset [QVar "Forall" (Just $ ExternalName "f_") (-1)
    , QVar "Forall" (Just $ ExternalName "f") (-2)
    , QVar "Forall" (Just $ ExternalName "X") (-3)
    , QVar "Forall" (Just $ ExternalName "d_Y") (-4)
    , QVar "Forall" (Just $ ExternalName "Y") (-5)] []
uniformLimDefe = holeFreeVars $ PApp ( "uniform_limit_of_functions_metric_space") (Free (-1)) (Free (-2)) (Free (-3)) (Free (-4)) (Free (-5))
uniformLimDefe' = holeFreeVars $ forall (Just $ ExternalName "theta") (0) $ Implies (BApp ( "real_greater_than") (Free 0) (Con $  "0")) $
    exists (Just $ ExternalName "N") (1) $ And (BApp ( "element_of") (Free 1) (Con $  "naturals")) $
    forall (Just $ ExternalName "n") (2) $ Implies (And (BApp ( "element_of") (Free 2) (Con $  "naturals")) (BApp ( "real_greater_than") (Free 2) (Free 1))) $
    forall (Just $ ExternalName "x") (3) $ Implies (BApp ( "element_of") (Free 3) (Free (-3))) $
    BApp ( "real_lesser_than") (App (App (Free (-4)) (App (App (Free (-1)) (Free 2)) (Free 3))) (App (Free (-2)) (Free 3))) (Free 0)
uniformLimDef = LibraryEquivalence uniformLimDefQZone [] [uniformLimDefe, uniformLimDefe']


-- Triangle inequality version
Just triIneqQZone = parseQZone "forall X, forall d, forall w, forall x, forall y, forall z, forall a, forall b, forall c"
Just triIneqH1 = parseWithQZone triIneqQZone "metric_on(d, X)"
Just triIneqH2 = parseWithQZone triIneqQZone "real_lesser_than(d(w, x), a)"
Just triIneqH3 = parseWithQZone triIneqQZone "real_lesser_than(d(z, y), b)"
Just triIneqH4 = parseWithQZone triIneqQZone "real_lesser_than(d(w, z), c)"
Just triIneqT1 = parseWithQZone triIneqQZone "real_lesser_than(d(x, y), real_plus(a, real_plus(b, c)))"
triIneq = LibraryImplication triIneqQZone
    (map holeFreeVars [triIneqH1, triIneqH2, triIneqH3, triIneqH4])
    (map holeFreeVars [triIneqT1])


-- Uniform limit of cts functions is cts
g1 = forall (Just $ ExternalName "X") (0) $
    forall (Just $ ExternalName "Y") (1) $
    forall (Just $ ExternalName "d_X") (2) $
    forall (Just $ ExternalName "d_Y") (3) $
    forall (Just $ ExternalName "f") (4) $
    forall (Just $ ExternalName "f_") (5) $
    Implies (HAnd
        (BApp ( "metric_on") (Free 2) (Free 0))
        (BApp ( "metric_on") (Free 3) (Free 1))
        (TApp ( "function") (Free 4) (Free 0) (Free 1))
        (TApp ( "sequence_of_functions") (Free 5) (Free 0) (Free 1))
        (PApp ( "uniform_limit_of_functions_metric_space") (Free 5) (Free 4) (Free 0) (Free 3) (Free 1))
        (forall (Just $ ExternalName "n") (6) $ Implies (BApp ( "element_of") (Free 6) (Con $  "naturals")) (PApp ( "continuous_in_metric_space") (App (Free 5) (Free 6)) (Free 2) (Free 0) (Free 3) (Free 1))))$
    PApp ( "continuous_in_metric_space") (Free 4) (Free 2) (Free 0) (Free 3) (Free 1)

gQZone = Poset [] []
gBox = Box [] [g1]
gQBox = (gQZone, gBox)
gTab = Tableau gQZone [gBox]

Just gResult = tidyEverything gTab >>= boxToTabMove (libEquivTargCondMap continuousDef (0, 1) [(0, 0), (1, 5), (2, 4)] 0) 0 >>= tidyEverything
     >>= boxToTabMove (peelExistentialTargBox 0) 0 >>= tidyEverything
     >>= boxToTabMove (libEquivHyp uniformLimDef (0, 1) 2) 0
     >>= boxToTabMove (peelUniversalHypBox 2) 0 >>= commitToHypothesis 10 0 >>= tidyEverything
     >>= boxToTabMove (peelUniversalHypBox 11) 0 >>= commitToHypothesis 12 0 >>= tidyEverything
     >>= boxToTabMove (modusPonensBox 12 6) 0 >>= boxToTabMove (modusPonensBox 12 8) 0 >>= tidyEverything
     >>= boxToTabMove (peelUniversalHypBox 1) 0 >>= commitToHypothesis 15 0
     >>= boxToTabMove (libEquivHyp sequenceOfFunctions (0, 1) 3) 0 >>= boxToTabMove (peelUniversalHypBox 3) 0 >>= commitToHypothesis 16 0 >>= instantiateExistential "b" "a"
     >>= boxToTabMove (libEquivHyp continuousDef (0, 1) 15) 0 >>= tidyEverything
     >>= boxToTabMove (modusPonensBox 15 6) 0 >>= boxToTabMove (peelUniversalHypBox 15) 0 >>= commitToHypothesis 18 0 >>= instantiateExistential "b" "x"
     >>= boxToTabMove (peelUniversalHypBox 18) 0 >>= commitToHypothesis 19 0 >>= instantiateExistential "b" "theta"
     >>= boxToTabMove (peelExistentialHypBox 19) 0 >>= tidyEverything
     >>= boxToTabMove (modusPonensBox 20 8) 0
    -- >>= instantiateExistential "delta" "b" >>= boxToTabMove (rawModusPonensBox 21 9) 0
    -- >>= instantiateExistential "a" "n" >>= boxToTabMove (libForwardReasoning triIneq) 0
    -- >>= boxToTabMove (libBackwardReasoning lesserThanTrans) 0
    -- >>= boxToTabMove (modusPonensBox 15 6) 0 >>= boxToTabMove (modusPonensBox 16 7) 0 >>= tidyEverything
    -- >>= boxToTabMove (modusPonensBox 18 8) 0



gResult' = tidyEverything gTab

at1 = exists (Just $ ExternalName "x") 0 (forall (Just $ ExternalName "y") 0 (exists (Just $ ExternalName "z") 1 (Eq (Free 0) (Free 1))))
aBox = Box [] [at1]
aHead = Poset [] []
aQBox = (aHead, aBox)
Just aResult = (peelExistentialTargBox 0) aQBox >>= (peelUniversalTargBox 0) >>= (peelExistentialTargBox 0)
aStr = pprintQBox aResult


-- Universal modus ponens with hyp
bh1 = forall (Just $ ExternalName "x") 0 $
    Implies (Eq (UApp ( "succ") (Free 0)) (Con ( "1"))) (Eq (Free 0) (Con ( "0")))

bh2= Eq (UApp ( "succ") (Free 1)) (Con ( "1"))

bTestHead = Poset [QVar "Forall" (Just $ ExternalName "y") 1] []
bTestBox = Box [bh1, bh2] []
bTestQBox = (bTestHead, bTestBox)
Just bResult = modusPonensBox 0 1 bTestQBox
bBeforeStr = pprintQBox bTestQBox
bStr = pprintQBox bResult


-- Implication in target tidy
ct1 = Implies (Eq (UApp ( "succ") (Free 0)) (UApp ( "succ") (Free 1))) (Eq (Free 0) (Free 1))
cTestHead = Poset [QVar "Forall" (Just $ ExternalName "x") 0, QVar "Forall" (Just $ ExternalName "y") 1] []
cTestBox = Box [] [ct1]
cTestQBox = (cTestHead, cTestBox)
cTestTab = Tableau cTestHead [cTestBox]
Just cResult = tidyImplInTarg 0 0 cTestTab
cStr = pprintTab cResult



-- Forwards and backwards reasoning
Just xQZone' = parseQZone "forall M, forall d, forall U, forall V"
Just xh1 = parseWithQZone xQZone' "metric_on(d, M)"
Just xh2 = parseWithQZone xQZone' "open_in_metric(U, d, M)"
Just xh3 = parseWithQZone xQZone' "open_in_metric(V, d, M)"
Just xt1 = parseWithQZone xQZone' "open_in_metric(set_intersection(U, V), d, M)"
forwardReasoningTestLib = LibraryImplication xQZone'
    (map holeFreeVars [xh1, xh2, xh3])
    (map holeFreeVars [xt1])

Just xQZone = parseQZone "forall M, forall d, forall U, forall V"
Just xhh1 = parseWithQZone xQZone "metric_on(d, M)"
Just xhh2 = parseWithQZone xQZone "open_in_metric(U, d, M)"
Just xhh3 = parseWithQZone xQZone "open_in_metric(V, d, M)"
Just xtt1 = parseWithQZone xQZone "open_in_metric(set_intersection(U, V), d, M)"
xTab = Tableau xQZone [Box [xhh1, xhh2, xhh3] [xtt1]]

Just a' = boxToTabMove (libForwardReasoning forwardReasoningTestLib) 0 xTab
Just b' = boxToTabMove (libBackwardReasoning forwardReasoningTestLib) 0 xTab

