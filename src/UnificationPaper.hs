{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module UnificationPaper where

import Box
import Poset
import Lib
import TableauFoundation
import PPrinting

-- PROBABLY ALL QUITE INEFFICIENT, BUT WE CAN OPTIMISE LATER

-- By default the permutation will be identity
-- The left case is where we have a free variable, the right case is where we have a bound variable
type Atom = Either InternalName Int
type Permutation = [(InternalName , InternalName)]
type VariableName = InternalName
type SuspendedVariable = (Permutation, VariableName)

-- | The type of expressions with the addition of variables in the sense of unification.
data HExpr
  = HApp HExpr HExpr
    -- ^ A function application. Note that the function itself can be an expression.
  | HAbs (Maybe ExternalName) HScoped
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | HFree InternalName
    -- ^ A free variable.
  | HCon ConstantString
    -- ^ A constant (eg the naturals, or the sin function).
  | HB Int
    -- ^ A bound variable
  | V SuspendedVariable
    -- ^ A variable in the sense of unification
  deriving (Eq, Show) 

-- Takes an expression and makes it a holed-expression (though this will have no holes, of course)
exprToHExpr :: Expr -> HExpr
exprToHExpr (App e1 e2) = HApp (exprToHExpr e1) (exprToHExpr e2)
exprToHExpr (Abs exNm (Sc e)) = HAbs exNm (HSc (exprToHExpr e))
exprToHExpr (Free inNm) = HFree inNm
exprToHExpr (Con con) = HCon con
exprToHExpr (B i) = HB i

-- Takes a holed expression and attempts to turn it into an expression. Fails if there are holes.
-- Mainly useful to convert back after substitution.
hExprToExpr :: HExpr -> Maybe Expr
hExprToExpr (HApp e1 e2) = case (hExprToExpr e1, hExprToExpr e2) of
    (Just e1', Just e2') -> Just $ App e1' e2'
    _ -> Nothing
hExprToExpr (HAbs exNm (HSc e)) = case hExprToExpr e of
    Just e' -> Just $ Abs exNm (Sc e')
    _ -> Nothing
hExprToExpr (HFree inNm) = Just $ Free inNm
hExprToExpr (HCon con) = Just $ Con con
hExprToExpr (HB i) = Just $ B i
hExprToExpr (V i) = Nothing

-- A list of correspondences from VariableName to Expression
type Substitution = [(VariableName, Expr)]

-- Performs a substitution
substituteHExpr :: Substitution -> HExpr -> HExpr
substituteHExpr [] e = e
substituteHExpr [f] (HApp e1 e2) = HApp (substituteHExpr [f] e1) (substituteHExpr [f] e2)
substituteHExpr [f] (HAbs exNm (HSc e)) = HAbs exNm (HSc (substituteHExpr [f] e))
substituteHExpr [f] (HFree i) = HFree i
substituteHExpr [f] (HCon con) = HCon con
substituteHExpr [f] (HB i) = HB i
substituteHExpr [(i, expr)] (V (pi, i')) = if i == i' then exprToHExpr $ applyPermToExpr pi expr else V (pi, i')
substituteHExpr (f:sub) expr = substituteHExpr sub (substituteHExpr [f] expr)


applyPermToInternalName :: Permutation -> InternalName -> InternalName
applyPermToInternalName _ _ = 0

-- Applies a permutation to an expression
applyPermToExpr :: Permutation -> Expr -> Expr
applyPermToExpr _ _ = B 0


-- Applies a permutation to a holed expression
applyPermToHExpr :: Permutation -> HExpr -> HExpr
applyPermToHExpr _ _ = HB 0















-- << IDENTICAL TO NORMAL EXPRESSION STUFF >>

newtype HScoped = HSc HExpr
  deriving (Eq, Show)

-- | Equality of scoped expressions, up to alpha equivalence.
instance AlphaEq HScoped where
  HSc x ~= HSc y = x ~= y

-- | Equality of expressions, up to alpha equivalence.
instance AlphaEq HExpr where
  HApp f x ~= HApp g y = f ~= g && x ~= y
  HAbs _ x ~= HAbs _ y = x ~= y
  HFree n  ~= HFree m  = n == m
  HCon s   ~= HCon t   = s == t
  HB i     ~= HB j     = i == j
  V i     ~= V j     = i == j
  _       ~= _       = False

-- | Example: Peano's first axiom as an expression
peanoOne :: Expr
peanoOne = App (Con (Quant "forall")) $ Abs (Just "x") $ Sc $ App (Con (Log "not")) $
  App (App (Con (Pred "eq")) $ App (Con (Operator "succ")) (B 0)) $ Con (Obj "zero")

hApps :: HExpr -> [HExpr] -> HExpr
hApps e [] = e
hApps e (x : xs) = hApps (HApp e x) xs

-- f                       -> (f, [])
-- App f x                 -> (f, [x])
-- App (App f x) y         -> (f, [y, x])
-- App (App (App g x) y) z -> (g, [z, y, x])
hGetAppChain :: HExpr -> (HExpr, [HExpr])
hGetAppChain (HApp f x) = (g, x:t)
  where (g, t) = hGetAppChain f
hGetAppChain t = (t, [])

-- | Unary application of a constant function to an expression.
pattern HUApp :: String -> HExpr -> HExpr
pattern HUApp f x = HApp (HCon (Operator f)) x

-- | Binary application of a constant function to an expression.
pattern HBApp :: String -> HExpr -> HExpr -> HExpr
pattern HBApp f x y = HApp (HApp (HCon (Operator f)) x) y

pattern HTApp :: String -> HExpr -> HExpr -> HExpr -> HExpr
pattern HTApp f x y z = HApp (HApp (HApp (HCon (Operator f)) x) y) z

pattern HQApp :: String -> HExpr -> HExpr -> HExpr -> HExpr -> HExpr
pattern HQApp f a b c d = HApp (HApp (HApp (HApp (HCon (Operator f)) a) b) c) d

pattern HPApp :: String -> HExpr -> HExpr -> HExpr -> HExpr -> HExpr -> HExpr
pattern HPApp f a b c d e = HApp (HApp (HApp (HApp (HApp (HCon (Operator f)) a) b) c) d) e

-- | The conjunction of two expressions.
pattern HAnd :: HExpr -> HExpr -> HExpr
pattern HAnd x y = HBApp "and" x y

-- | The disjunction of two expressions.
pattern HOr :: HExpr -> HExpr -> HExpr
pattern HOr x y = HBApp "or" x y

-- | The implication of two expressions.
pattern HImplies :: HExpr -> HExpr -> HExpr
pattern HImplies x y = HBApp "implies" x y

-- | The negation of an expression.
pattern HNot :: HExpr -> HExpr
pattern HNot x = HUApp "not" x

-- | Equality of two expressions.
pattern HEq :: HExpr -> HExpr -> HExpr
pattern HEq x y = HBApp "eq" x y

pattern HForall :: Maybe ExternalName -> HScoped -> HExpr
pattern HForall x y = HUApp "forall" (HAbs x y)

pattern HExists :: Maybe ExternalName -> HScoped -> HExpr
pattern HExists x y = HUApp "exists" (HAbs x y)

hAbstract :: InternalName -> HExpr -> HScoped
hAbstract n e = HSc (nameTo 0 e) where
  nameTo i (HApp f x)       = HApp (nameTo i f) (nameTo i x)
  nameTo i (HAbs nm (HSc b)) = HAbs nm (HSc (nameTo (i+1) b))
  nameTo i (HFree m)
    | m == n               = HB i
  nameTo _ t               = t -- otherwise, B and Con cases

hInstantiate :: HExpr -> HScoped -> HExpr
hInstantiate im (HSc b) = replace 0 b where
  replace i (HAbs nm (HSc m)) = HAbs nm (HSc (replace (i+1) m))
  replace i (HApp f x) = HApp (replace i f) (replace i x)
  replace i (HB m)
    | i == m    = im
  replace _ t = t

hForall :: Maybe ExternalName -> InternalName -> HExpr -> HExpr
hForall m x p = HForall m (hAbstract x p)

hExists :: Maybe ExternalName -> InternalName -> HExpr -> HExpr
hExists m x p = HExists m (hAbstract x p)

hInstantiateAbs :: HExpr -> HExpr -> Maybe HExpr
hInstantiateAbs (HAbs _ p) x = Just (hInstantiate x p)
hInstantiateAbs _         _ = Nothing

hInstantiateForall :: HExpr -> HExpr -> Maybe (Maybe ExternalName, HExpr)
hInstantiateForall (HForall nm p) x = Just (nm, hInstantiate x p)
hInstantiateForall _            _  = Nothing

-- | Forget all name suggestions.
hForgetSuggestions :: HExpr -> HExpr
hForgetSuggestions (HApp f x)      = HApp (hForgetSuggestions f) (hForgetSuggestions x)
hForgetSuggestions (HAbs _ (HSc e)) = HAbs Nothing (HSc (hForgetSuggestions e))
hForgetSuggestions (HFree m)       = HFree m
hForgetSuggestions (HCon s)        = HCon s
hForgetSuggestions (HB i)          = HB i
hForgetSuggestions (V i)           = V i


