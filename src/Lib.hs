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
  deriving (Eq, Ord, Show, Hashable)

type InternalName = [(String, Int)]

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

forall :: Maybe ExternalName -> InternalName -> Expr -> Expr
forall m x p = Forall m (abstract x p)

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

type Agency t = InternalName -> t

enterForall :: Agency (Expr -> Maybe (Maybe ExternalName, Expr))
enterForall root e = instantiateForall e (Free root)

swapForalls :: Agency (Expr -> Maybe Expr)
swapForalls root e = do
  (x0, first)  <- enterForall (("x", 0) : root) e
  (x1, second) <- enterForall (("x", 1) : root) first
  return $ forall x1 (("x", 1) : root) (forall x0 (("x", 0) : root) second)

unsafeRunAgency :: Agency t -> t
unsafeRunAgency x = x []

data PrintingState = PS
  { showMap :: HashMap InternalName ExternalName
  , usedNames :: HashSet ExternalName
  , counter :: Int
  }

getSuggestion' :: ExternalName -> State PrintingState (InternalName, ExternalName)
getSuggestion' x = do
  PS m s n <- get
  let r = [("printing", n)]
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
pprintExprM (Forall sug sc) = pprintBinderM "∀" sug sc
-- general patterns
pprintExprM t@(App _ _) = do
  let (f, x) = getAppChain t
  fs <- pprintExprM f
  xs <- traverse pprintExprM (reverse x)
  return $ fs ++ "(" ++ intercalate ", " xs ++ ")"
pprintExprM (Free x) = do
  (PS m _ _) <- get
  return $ getExternalName $ m M.! x
pprintExprM (Con s) = return s
pprintExprM (Abs sug sc) = pprintBinderM "λ" sug sc
pprintExprM (B _) = error "term not closed"

pprintExpr :: Expr -> String
pprintExpr e = evalState (pprintExprM e) (PS mempty mempty 0)

-- | Nothing right now.
someFunc :: IO ()
someFunc = return ()
