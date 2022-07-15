{-|
Adapted from
/[BP] de Bruijn notation as a nested datatype - Bird, Paterson/ but with a
two sorted theory, mutual recursion and suggested names.

Might be nicer to adapt to
<http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.66.6645&rep=rep1&type=pdf>
/[MM] I am not a number: I am a free variable - Conor McBride and James McKinna/.
-}
-- {-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
-- {-# OPTIONS_GHC -fdefer-typed-holes #-}
module Lib where

import Data.Set (Set)
import qualified Data.Set as S
import Data.String (IsString(..))
import Data.List
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Classes
import Data.Coerce
import Control.Monad.State
import Control.Monad.Reader

-- | A type to represent variable names. Ultimately I think this might want a more
--   sophisticated type, perhaps like the one in [MM], but for now it's just a `String`.
newtype Name = Name { getName :: String }
  deriving (Eq, Ord, Show)

instance IsString Name where
  fromString = Name

-- | The type of terms with free variables of type v.
data Expr v
  = App (Expr v) [Expr v]
    -- ^ A function application. Note that the function itself can be a term.
  | Abs (Maybe Name) (Expr (Maybe v))
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | Var v
    -- ^ A variable, either bound higher in the expression or free.
  | Con String
    -- ^ A constant (eg the naturals, or the sin function).
  deriving ( Show          -- ^ stock derivation of 'Show', not for user consumption.
           , Functor       -- ^ stock derivation of 'Functor'
           , Foldable      -- ^ stock derivation of 'Foldable'
           , Traversable   -- ^ stock derivation of 'Traversable'
           )

-- | For convenience of writing expressions directly.
instance IsString v => IsString (Expr v) where
  fromString = Var . fromString

-- | This can be derived using TemplateHaskell but it's not worth it. Note
-- this considers expressions with different name suggestions to be different.
instance Eq1 Expr where
  liftEq f (App g xs) (App h ys) = liftEq f g h && and (zipWith (liftEq f) xs ys)
  liftEq f (Abs n1 x1) (Abs n2 x2) = n1 == n2 && liftEq (liftEq f) x1 x2
  liftEq f (Var x) (Var y) = f x y
  liftEq f (Con x) (Con y) = x == y
  liftEq _ _ _ = False

-- | Note this considers expressions with different name suggestions to be
-- different. See `AlphaEq`.
instance Eq v => Eq (Expr v) where
  (==) = liftEq (==)

-- | Check for equality of expressions up to alpha-equivalence.
class AlphaEq t where
  (~=) :: t -> t -> Bool

class AlphaEq1 f where
  liftAlphaEq :: (a -> b -> Bool) -> f a -> f b -> Bool

instance AlphaEq1 Expr where
  liftAlphaEq f (App g xs) (App h ys) = liftAlphaEq f g h && and (zipWith (liftAlphaEq f) xs ys)
  liftAlphaEq f (Abs n1 x1) (Abs n2 x2) = liftAlphaEq (liftEq f) x1 x2
  liftAlphaEq f (Var x) (Var y) = f x y
  liftAlphaEq f (Con x) (Con y) = x == y
  liftAlphaEq _ _ _ = False

instance Eq v => AlphaEq (Expr v) where
  (~=) = liftAlphaEq (==)

-- | Fold up an expression, allowing a type constructor on the inside.
gfold :: forall m e.
         (forall v. e v -> [e v] -> e v) -- ^ app
      -> (forall v. Maybe Name -> e (Maybe v) -> e v) -- ^ abs
      -> (forall v. Maybe (m v) -> m (Maybe v)) -- ^ lift abs
      -> (forall v. m v -> e v) -- ^ variable
      -> (forall v. String -> e v) -- ^ constant
      -> forall a. Expr (m a) -> e a
gfold f a l v k = run where
  run :: forall a. Expr (m a) -> e a
  run (App g xs) = f (run g) (run <$> xs)
  run (Abs n p) = a n (run (l <$> p))
  run (Var x) = v x
  run (Con s) = k s

-- | Fold up an expression.
fold :: forall e.
        (forall v. e v -> [e v] -> e v) -- ^ app
     -> (forall v. Maybe Name -> e (Maybe v) -> e v) -- ^ abs
     -> (forall v. v -> e v) -- ^ variable
     -> (forall v. String -> e v) -- ^ constant
     -> forall a. Expr a -> e a
fold f a v k = run where
  run :: forall a. Expr a -> e a
  run (App g xs) = f (run g) (run <$> xs)
  run (Abs n p) = a n (run p)
  run (Var x) = v x
  run (Con s) = k s

-- | The distribution of `Maybe` over `Expr`.
distE :: Maybe (Expr v) -> Expr (Maybe v)
distE Nothing = Var Nothing
distE (Just x) = Just <$> x

-- | Expressions form a monad, essentially via substitution.
instance Monad Expr where
  App g xs >>= f = App (g >>= f) (map (>>= f) xs)
  Abs n p  >>= f = Abs n (p >>= distE . fmap f)
  Var x    >>= f = f x
  Con s    >>= f = Con s

instance Applicative Expr where
  pure = Var
  (<*>) = ap

-- | Example: Peano's first axiom as an expression
peanoOne :: Expr v
peanoOne = App (Con "forall")
  [Abs (Just (Name "x"))
    (App (Con "not")
      [App (Con "eq")
        [App (Con "succ") [Var Nothing],
         App (Con "zero") []]])]

-- | Unary application of a constant function to an expression.
pattern UApp :: String -> Expr v -> Expr v
pattern UApp f x = App (Con f) [x]

-- | Binary application of a constant function to an expression.
pattern BApp :: String -> Expr v -> Expr v -> Expr v
pattern BApp f x y = App (Con f) [x, y]

-- | The conjunction of two expressions.
pattern And :: Expr v -> Expr v -> Expr v
pattern And x y = BApp "and" x y

-- | The disjunction of two expressions.
pattern Or :: Expr v -> Expr v -> Expr v
pattern Or x y = BApp "or" x y

-- | The implication of two expressions.
pattern Implies :: Expr v -> Expr v -> Expr v
pattern Implies x y = BApp "implies" x y

-- | The negation of an expression.
pattern Not :: Expr v -> Expr v
pattern Not x = UApp "not" x

-- | Equality of two expressions.
pattern Eq :: Expr v -> Expr v -> Expr v
pattern Eq x y = BApp "eq" x y

pattern Forall :: Maybe Name -> Expr (Maybe v) -> Expr v
pattern Forall x y = UApp "forall" (Abs x y)

pattern Exists :: Maybe Name -> Expr (Maybe v) -> Expr v
pattern Exists x y = UApp "exists" (Abs x y)

abstract :: Eq v => v -> Expr v -> Expr (Maybe v)
abstract x = fmap (\y -> if x == y then Nothing else Just y)

instantiate :: Expr v -> Expr (Maybe v) -> Expr v
instantiate x = (>>= maybe x Var)

forall :: Name -> Expr Name -> Expr Name
forall x p = Forall (Just x) (abstract x p)

exists :: Name -> Expr Name -> Expr Name
exists x p = Exists (Just x) (abstract x p)

instantiateAbs :: Expr v -> Expr v -> Maybe (Expr v)
instantiateAbs (Abs _ p) x = Just (instantiate x p)
instantiateAbs _         _ = Nothing

-- | Example: Peano's second axiom as an expression
peanoTwo :: Expr Name
peanoTwo =
  forall "x" $
    forall "y" $
      Implies
        (Eq (UApp "succ" "x") (UApp "succ" "y"))
        (Eq "x" "y")

-- | If possible, convert an expression to one with no free variables.
toClosed :: Expr v -> Maybe (Expr a)
toClosed = traverse $ const Nothing

-- | The set of names available to use.
availableNames :: Set Name
availableNames = S.fromAscList $ map (Name . (:[])) "abcdefghijklmnopqrstuvwxyz"

-- | Given an optional name and a set of unavailable names, pick a fresh name.
spareName :: Maybe Name -> Set Name -> Name
spareName (Just n) s = if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
spareName Nothing  s = S.findMin (availableNames S.\\ s)

-- | Pretty-print an expression as a string, provided a set of names which are not available.
pprintExprAux :: Set Name -> Expr Name -> String
pprintExprAux s (And p1 p2) = "(" ++ pprintExprAux s p1 ++ " ∧ " ++ pprintExprAux s p2 ++ ")"
pprintExprAux s (Or p1 p2) = "(" ++ pprintExprAux s p1 ++ " ∨ " ++ pprintExprAux s p2 ++ ")"
pprintExprAux s (Implies p1 p2) = "(" ++ pprintExprAux s p1 ++ " ⇒ " ++ pprintExprAux s p2 ++ ")"
pprintExprAux s (Not p) = "(¬" ++ pprintExprAux s p ++ ")"
pprintExprAux s (Eq p1 p2) = "(" ++ pprintExprAux s p1 ++ " = " ++ pprintExprAux s p2 ++ ")"
pprintExprAux s (Forall m v) =
  let new = spareName m s
   in "∀" ++ getName new ++ ", " ++ pprintExprAux (S.insert new s) (instantiate (Var new) v)
pprintExprAux s (Exists m v) =
  let new = spareName m s
   in "∃" ++ getName new ++ ", " ++ pprintExprAux (S.insert new s) (instantiate (Var new) v)
pprintExprAux s (App g []) = pprintExprAux s g
pprintExprAux s (App g x) = pprintExprAux s g ++ "(" ++ intercalate ", " (map (pprintExprAux s) x) ++ ")"
pprintExprAux s (Abs m v) =
  let new = spareName m s
   in "λ" ++ getName new ++ ", " ++ pprintExprAux (S.insert new s) (instantiate (Var new) v)
pprintExprAux s (Var x) = getName x
pprintExprAux s (Con c) = c

-- | Pretty-print an expression as a string.
pprintExpr :: Expr Name -> String
pprintExpr = pprintExprAux S.empty

-- | Forget all name suggestions.
forgetSuggestions :: Expr v -> Expr v
forgetSuggestions = fold App (const (Abs Nothing)) Var Con

-- | Example: the original state of the open sets problem.
openSetsProblem :: Expr Name
openSetsProblem =
  forall "X" $
    Implies (UApp "is_metric_space" "X") $
      forall "Y" $
        Implies (UApp "is_metric_space" "Y") $
          forall "f" $
            Implies (App "is_function_on" ["f", "X", "Y"]) $
              forall "U" $
                Implies (BApp "subset" "U" "Y") $
                  Implies (UApp "continuous" "f") $
                    Implies (UApp "open" "U") $
                      UApp "open" (App (UApp "inv_image" "f") ["U"])

-- | Nothing right now.
someFunc :: IO ()
someFunc = return ()
