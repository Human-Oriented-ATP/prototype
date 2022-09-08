module Library where

import Box
import Poset
import Lib
import TableauFoundation
import PPrinting



contDef :: Tableau
contHead = Poset [] []
-- 0 : f
-- 1 : X
-- 2 : \tau_X
-- 3 : Y
-- 4 : \tau_Y
-- 5 : A
f0 = QVar "Forall" (Just $ ExternalName "f") 0
f1 = QVar "Forall" (Just $ ExternalName "X") 1
f2 = QVar "Forall" (Just $ ExternalName "tau_X") 2
f3 = QVar "Forall" (Just $ ExternalName "Y") 3
f4 = QVar "Forall" (Just $ ExternalName "tau_Y") 4
f5 = QVar "Forall" (Just $ ExternalName "A") 5

h1 = (TApp (Pred "function") (Free 0) (Free 1) (Free 3), [f0, f1, f3])
h2 = (PApp (Pred "continuous_in") (Free 0) (Free 1) (Free 2) (Free 3) (Free 4), [f0, f1, f2, f3, f4])
h3 = (TApp (Pred "open_in") (Free 5) (Free 3) (Free 4), [f3, f4, f5])
t1 = (TApp (Pred "open_in") (App (UApp (Operator "inv") (Free 0)) (Free 5)) (Free 1) (Free 2), [f0, f1, f2, f5])

contBox = Box [h1, h2, h3] [t1]
contDef = Tableau contHead [contBox]

library :: [Tableau]
library = [contDef]

