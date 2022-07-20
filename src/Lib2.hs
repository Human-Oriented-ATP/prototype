{-|
Adapted from
<http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.66.6645&rep=rep1&type=pdf>
/[MM] I am not a number: I am a free variable - Conor McBride and James McKinna/.
-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lib2 where

import Data.String (IsString(..))

-- | A type to represent external variable names.
newtype ExternalName = ExternalName { getExternalName :: String }
  deriving (Eq, Ord, Show)

newtype InternalName = InternalName { getInternalName :: [(String, Int)] }
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Show)

newtype Scoped = Sc Expr
  deriving (Eq, Show)

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
peanoOne = App (Con "forall") $ Abs (Just "x") $ Sc $ App (Con "not") $
  App (App (Con "eq") $ App (Con "succ") (B 0)) $ Con "zero"

apps :: Expr -> [Expr] -> Expr
apps e [] = e
apps e (x : xs) = apps (App e x) xs

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

pattern Forall :: Maybe ExternalName -> Scoped -> Expr
pattern Forall x y = UApp "forall" (Abs x y)

pattern Exists :: Maybe ExternalName -> Scoped -> Expr
pattern Exists x y = UApp "exists" (Abs x y)

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

instantiateAbs :: Expr -> Expr -> Maybe Expr
instantiateAbs (Abs _ p) x = Just (instantiate x p)
instantiateAbs _         _ = Nothing

-- | Forget all name suggestions.
forgetSuggestions :: Expr -> Expr
forgetSuggestions (App f x)      = App (forgetSuggestions f) (forgetSuggestions x)
forgetSuggestions (Abs _ (Sc e)) = Abs Nothing (Sc (forgetSuggestions e))
forgetSuggestions (Free m)       = Free m
forgetSuggestions (Con s)        = Con s
forgetSuggestions (B i)          = B i

-- goIntoForall :: Expr -> Maybe Expr
-- goIntoForall (Forall x p) = Just (instantiate _ p)
-- goIntoForall _            = Nothing
--
-- commuteForalls :: Expr -> Maybe Expr
-- commuteForalls (Forall x p) = Just _
-- commuteForalls _            = Nothing

-- | Nothing right now.
someFunc :: IO ()
someFunc = return ()
