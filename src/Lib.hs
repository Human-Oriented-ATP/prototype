{-|
Adapted from
<http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.66.6645&rep=rep1&type=pdf>
/[MM] I am not a number: I am a free variable - Conor McBride and James McKinna/.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Lib where

import Data.Hashable
import Control.Monad.State
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import Data.String (IsString(..))
import Data.List

-- | A type to represent external variable names.
newtype ExternalName = ExternalName { getExternalName :: String }
  deriving (Eq, Ord, Show, Hashable, Read)

type InternalName = Int

-- For convenience
instance IsString ExternalName where
  fromString = ExternalName


-- | The type of terms with free variables of type v.
data Expr
  = App Expr Expr
    -- ^ A function application. Note that the function itself can be an expression.
  | Abs (Maybe ExternalName) Scoped
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | Free InternalName
    -- ^ A free variable.
  | Con String
    -- ^ A constant (eg the naturals, or the sin function).
  | B Int
    -- ^ A bound variable
  deriving (Eq, Show, Read) 

-- \forall x, \forall y, x + y = y + x
-- \forall a, \forall b, a + b = b + a

newtype Scoped = Sc Expr
  deriving (Eq, Show, Read)

-- | Check for equality of expressions up to alpha-equivalence.
class AlphaEq t where
  (~=) :: t -> t -> Bool

-- | Equality of scoped expressions, up to alpha equivalence.
instance AlphaEq Scoped where
  Sc x ~= Sc y = x ~= y

-- | Equality of expressions, up to alpha equivalence.
instance AlphaEq Expr where
  App f x ~= App g y = f ~= g && x ~= y
  Abs _ x ~= Abs _ y = x ~= y
  Free n  ~= Free m  = n == m
  Con s   ~= Con t   = s == t
  B i     ~= B j     = i == j
  _       ~= _       = False

-- | Example: Peano's first axiom as an expression
peanoOne :: Expr
peanoOne = App (Con "forall") $ Abs (Just "x") $ Sc $ App (Con "forall") $ Abs (Just "y") $ Sc $ App (Con "not") $
  App (App (Con "eq") $ App (Con "succ") (B 0)) $ App (Con "succ") (B 1)

apps :: Expr -> [Expr] -> Expr
apps e [] = e
apps e (x : xs) = apps (App e x) xs

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
pattern BApp f x y = App (App (Con  f) x) y

pattern TApp :: String -> Expr -> Expr -> Expr -> Expr
pattern TApp f x y z = App (App (App (Con f) x) y) z

pattern QApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr
pattern QApp f a b c d = App (App (App (App (Con f) a) b) c) d

pattern PApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern PApp f a b c d e = App (App (App (App (App (Con f) a) b) c) d) e

pattern HApp :: String -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern HApp f a b c d e g = App (App (App (App (App (App (Con f) a) b) c) d) e) g

pattern TAnd :: Expr -> Expr -> Expr -> Expr
pattern TAnd x y z = And (And x y) z

pattern QAnd :: Expr -> Expr -> Expr -> Expr -> Expr
pattern QAnd a b c d = And (And (And a b) c) d

pattern PAnd :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern PAnd a b c d e = And (And (And (And a b) c) d) e

pattern HAnd :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern HAnd a b c d e f = And (And (And (And (And a b) c) d) e) f

-- | The conjunction of two expressions.
pattern And :: Expr -> Expr -> Expr
pattern And x y = App (App (Con "and") x) y

-- | The disjunction of two expressions.
pattern Or :: Expr -> Expr -> Expr
pattern Or x y = App (App (Con "or") x) y

-- | The implication of two expressions.
pattern Implies :: Expr -> Expr -> Expr
pattern Implies x y = App (App (Con "implies") x) y

-- | The negation of an expression.
pattern Not :: Expr -> Expr
pattern Not x = App (Con "not") x

-- | Equality of two expressions.
pattern Eq :: Expr -> Expr -> Expr
pattern Eq x y = App (App (Con "eq") x) y

pattern Forall :: Maybe ExternalName -> Scoped -> Expr
pattern Forall x y = App (Con "forall") (Abs x y)

pattern Exists :: Maybe ExternalName -> Scoped -> Expr
pattern Exists x y = App (Con "exists") (Abs x y)

abstract :: InternalName -> Expr -> Scoped
abstract n e = Sc (nameTo 0 e) where
  nameTo i (App f x)       = App (nameTo i f) (nameTo i x)
  nameTo i (Abs nm (Sc b)) = Abs nm (Sc (nameTo (i+1) b))
  nameTo i (Free m)
    | m == n               = B i
  nameTo _ t               = t -- otherwise, B and Con cases

instantiate :: Expr -> Scoped -> Expr
instantiate im (Sc b) = replace 0 b where
  replace i (Abs nm (Sc m)) = Abs nm (Sc (replace (i+1) m))
  replace i (App f x) = App (replace i f) (replace i x)
  replace i (B m)
    | i == m    = im
  replace _ t = t

forall :: Maybe ExternalName -> InternalName -> Expr -> Expr
forall m x exp = Forall m (abstract x exp)

exists :: Maybe ExternalName -> InternalName -> Expr -> Expr
exists m x p = Exists m (abstract x p)

instantiateAbs :: Expr -> Expr -> Maybe Expr
instantiateAbs (Abs _ p) x = Just (instantiate x p)
instantiateAbs _         _ = Nothing

instantiateForall :: Expr -> Expr -> Maybe (Maybe ExternalName, Expr)
instantiateForall (Forall nm p) x = Just (nm, instantiate x p)
instantiateForall _            _  = Nothing


-- | Forget all name suggestions.
forgetSuggestions :: Expr -> Expr
forgetSuggestions (App f x)      = App (forgetSuggestions f) (forgetSuggestions x)
forgetSuggestions (Abs _ (Sc e)) = Abs Nothing (Sc (forgetSuggestions e))
forgetSuggestions (Free m)       = Free m
forgetSuggestions (Con s)        = Con s
forgetSuggestions (B i)          = B i


getFreeVars :: Expr -> [InternalName]
getFreeVars (App e e') = getFreeVars e `union` getFreeVars e'
getFreeVars (Abs exNm (Sc sc)) = getFreeVars sc
getFreeVars (Free n) = [n]
getFreeVars (Con con) = []
getFreeVars (B i) = []

-- | Nothing right now.
someFunc :: IO ()
someFunc = return ()
