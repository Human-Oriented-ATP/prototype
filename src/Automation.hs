{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use first" #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Use bimap" #-}
module Automation where

import Lib
import TableauFoundation
import Poset
import Data.Maybe
import Data.List
import Control.Monad
import PPrinting
import Unification
import Debug.Trace
import NewMoves

