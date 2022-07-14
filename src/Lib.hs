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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
-- {-# OPTIONS_GHC -fdefer-typed-holes #-}
module Lib where

import Data.Set (Set)
import qualified Data.Set as S
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

-- | @`WithFreeVar` x v@ represents `x`-expressions with one extra free variable (not
-- from `v`), optionally together with a name suggestion for that variable.
data WithFreeVar x v =
  FV { getSuggestion :: Maybe Name -- ^ The optional name suggestion for the bound variable.
     , getScoped :: x (Maybe v) -- ^ The scoped expression containing one new variable.
     }
  deriving ( Functor      -- ^ stock derivation of 'Functor'
           , Foldable     -- ^ stock derivation of 'Foldable'
           , Traversable  -- ^ stock derivation of 'Traversable'
           )

-- | Prints the internal structure (not for user consumption). Note we could use
-- @`Show1` t => `Show` (`WithFreeVar` t v)@ here like for `Eq` but it seems much
-- more painful to write like that
deriving instance Show v => Show (WithFreeVar Expr v)

-- | The type of terms with free variables of type v.
data Expr v
  = App (Expr v) [Expr v]
    -- ^ A function application. Note that the function itself can be a term.
  | Abs (WithFreeVar Expr v)
    -- ^ An abstraction (eg \(x \mapsto x^2\)).
  | Var v
    -- ^ A variable, either bound higher in the expression or free.
  | Constant String
    -- ^ A constant (eg the naturals, or the sin function).
  deriving ( Show          -- ^ stock derivation of 'Show', not for user consumption.
           , Functor       -- ^ stock derivation of 'Functor'
           , Foldable      -- ^ stock derivation of 'Foldable'
           , Traversable   -- ^ stock derivation of 'Traversable'
           )

-- | Note this considers expressions with different name suggestions to be
-- different. See `AlphaEq1`.
instance Eq1 t => Eq1 (WithFreeVar t) where
  liftEq f (FV n1 p1) (FV n2 p2) = n1 == n2 && liftEq (liftEq f) p1 p2

-- | Note this considers expressions with different name suggestions to be
-- different. See `AlphaEq`.
instance (Eq1 t, Eq v) => Eq (WithFreeVar t v) where
  (==) = liftEq (==)

-- | This can be derived using TemplateHaskell but it's not worth it. Note
-- this considers expressions with different name suggestions to be different.
instance Eq1 Expr where
  liftEq f (App g xs) (App h ys) = liftEq f g h && and (zipWith (liftEq f) xs ys)
  liftEq f (Abs x) (Abs y) = liftEq f x y
  liftEq f (Var x) (Var y) = f x y
  liftEq f (Constant x) (Constant y) = x == y
  liftEq _ _ _ = False

-- | Note this considers expressions with different name suggestions to be
-- different. See `AlphaEq`.
instance Eq v => Eq (Expr v) where
  (==) = liftEq (==)

class AlphaEq t where
  (~=) :: t -> t -> Bool

class AlphaEq1 f where
  liftAlphaEq :: (a -> b -> Bool) -> f a -> f b -> Bool

instance AlphaEq1 t => AlphaEq1 (WithFreeVar t) where
  liftAlphaEq f (FV n1 p1) (FV n2 p2) = liftAlphaEq (liftEq f) p1 p2

instance AlphaEq1 Expr where
  liftAlphaEq f (App g xs) (App h ys) = liftAlphaEq f g h && and (zipWith (liftAlphaEq f) xs ys)
  liftAlphaEq f (Abs x) (Abs y) = liftAlphaEq f x y
  liftAlphaEq f (Var x) (Var y) = f x y
  liftAlphaEq f (Constant x) (Constant y) = x == y
  liftAlphaEq _ _ _ = False

instance Eq v => AlphaEq (Expr v) where
  (~=) = liftAlphaEq (==)
instance (AlphaEq1 t, Eq v) => AlphaEq (WithFreeVar t v) where
  (~=) = liftAlphaEq (==)

-- data Expr v
--   = App (Expr v) [Expr v]
--     -- ^ A function application. Note that the function itself can be a term.
--   | Abs (WithFreeVar Expr v)
--     -- ^ An abstraction (eg \(x \mapsto x^2\)).
--   | Var v
--     -- ^ A variable, either bound higher in the expression or free.
--   | Constant String
--     -- ^ A constant (eg the naturals, or the sin function).

gfoldE :: forall m e.
          (forall v. e v -> [e v] -> e v) -- ^ app
       -> (forall v. Maybe Name -> e (Maybe v) -> e v) -- ^ abs
       -> (forall v. Maybe (m v) -> m (Maybe v)) -- ^ lift abs
       -> (forall v. m v -> e v) -- ^ variable
       -> (forall v. String -> e v) -- ^ constant
       -> forall a. Expr (m a) -> e a
gfoldE f a l v k = run where
  run :: forall a. Expr (m a) -> e a
  run (App g xs) = f (run g) (run <$> xs)
  run (Abs (FV n p)) = a n (run (l <$> p))
  run (Var x) = v x
  run (Constant s) = k s

--          forall a. Expr a -> t a
-- foldT fapp fite fabs flabs fvar fconst
--   fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists x =
--     gfoldT @Identity fapp fite fabs coerce (fvar . runIdentity) fconst
--       fand for fimp fnot ffalse ftrue feq frel fforall coerce fexists coerce (coerce <$> x)
--
distT :: Maybe (Expr v) -> Expr (Maybe v)
distT Nothing = Var Nothing
distT (Just x) = Just <$> x

joinE :: Expr (Expr v) -> Expr v
joinE = gfoldE App (\x y -> Abs (FV x y)) distT id Constant

-- bindE :: forall a b. Expr a -> (a -> Expr b) -> Expr b
-- bindE e f = gfoldE App (\x y -> Abs (FV x y)) undefined undefined Constant (coerce (_ :: Expr a) :: Expr (Const a b))

-- instance Applicative Expr where
--   pure = Var
--   (<*>) = ap
--
-- instance Monad Expr where
--   x >>= f = joinT (f <$> x)
--   -- TODO (BM): there should be a more efficient way of implementing this
--   --            right now it can do two full traversals
--
-- peanoOne :: Prop v
-- peanoOne =
--     Forall $ FV (Just (Name "x")) $ Not $
--       Eq
--        (App (Constant "succ") [Var Nothing])
--        (App (Constant "zero") [])
--
-- unaryApply :: String -> Expr v -> Expr v
-- unaryApply f x = App (Constant f) [x]
--
-- -- Remembers the name suggestion
-- abstractP :: Name -> Prop Name -> WithFreeVar Prop Name
-- abstractP x = FV (Just x) . fmap (\y -> if x == y then Nothing else Just y)
--
-- -- Remembers the name suggestion
-- abstractT :: Name -> Expr Name -> WithFreeVar Expr Name
-- abstractT x = FV (Just x) . fmap (\y -> if x == y then Nothing else Just y)
--
-- -- Has no name suggestion
-- abstractP' :: Eq v => v -> Prop v -> WithFreeVar Prop v
-- abstractP' x = FV Nothing . fmap (\y -> if x == y then Nothing else Just y)
--
-- -- Has no name suggestion
-- abstractT' :: Eq v => v -> Expr v -> WithFreeVar Expr v
-- abstractT' x = FV Nothing . fmap (\y -> if x == y then Nothing else Just y)
--
-- instantiateT :: Expr v -> WithFreeVar Expr v -> Expr v
-- instantiateT x = (>>= maybe x Var) . getScoped
--
-- instantiateP :: Expr v -> WithFreeVar Prop v -> Prop v
-- instantiateP x = (`bindP` maybe x Var) . getScoped
--
-- forall :: Name -> Prop Name -> Prop Name
-- forall x p = Forall (abstractP x p)
--
-- exists :: Name -> Prop Name -> Prop Name
-- exists x p = Exists (abstractP x p)
--
-- instantiateForall :: Prop v -> Expr v -> Maybe (Prop v)
-- instantiateForall (Forall p) x = Just (instantiateP x p)
-- instantiateForall _ _ = Nothing
--
-- instantiateExists :: Prop v -> Expr v -> Maybe (Prop v)
-- instantiateExists (Exists p) x = Just (instantiateP x p)
-- instantiateExists _ _ = Nothing
--
-- peanoTwo :: Prop Name
-- peanoTwo =
--   forall (Name "x") $
--     forall (Name "y") $
--       Implies
--         (Eq (unaryApply "succ" (Var (Name "x")))
--             (unaryApply "succ" (Var (Name "y"))))
--         (Eq (Var (Name "x")) (Var (Name "y")))
--
-- toClosedT :: Expr v -> Maybe (Expr a)
-- toClosedT = traverse $ const Nothing
--
-- toClosedP :: Prop v -> Maybe (Prop a)
-- toClosedP = traverse $ const Nothing
--
-- -- change to hashset
-- availableNames :: Set Name
-- availableNames = S.fromAscList $ map (Name . (:[])) "abcdefghijklmnopqrstuvwxyz"
--
-- -- the set should have the names which are *not* available to use
-- pprintProp :: Set Name -> Prop Name -> String
-- pprintProp s (And p1 p2) = "(" ++ pprintProp s p1 ++ " ∧ " ++ pprintProp s p2 ++ ")"
-- pprintProp s (Or p1 p2) = "(" ++ pprintProp s p1 ++ " ∨ " ++ pprintProp s p2 ++ ")"
-- pprintProp s (Implies p1 p2) = "(" ++ pprintProp s p1 ++ " ⇒ " ++ pprintProp s p2 ++ ")"
-- pprintProp s (Not p) = "(¬" ++ pprintProp s p ++ ")"
-- pprintProp s PFalse = "⊥"
-- pprintProp s PTrue = "⊤"
-- pprintProp s (Eq t u) = "(" ++ pprintExpr s t ++ " = " ++ pprintExpr s u ++ ")"
-- pprintProp s (RApp g x) =  pprintExpr s g ++ "(" ++ intercalate ", " (map (pprintExpr s) x) ++ ")"
-- pprintProp s (Forall v) =
--   let new = case getSuggestion v of
--               Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
--               Nothing -> S.findMin (availableNames S.\\ s)
--   in "∀" ++ getName new ++ ", " ++ pprintProp (S.insert new s) (instantiateP (Var new) v)
-- pprintProp s (Exists v) =
--   let new = case getSuggestion v of
--               Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
--               Nothing -> S.findMin (availableNames S.\\ s)
--   in "∃" ++ getName new ++ ", " ++ pprintProp (S.insert new s) (instantiateP (Var new) v)
--
-- pprintExpr :: Set Name -> Expr Name -> String
-- pprintExpr s (App g x) = pprintExpr s g ++ "(" ++ intercalate ", " (map (pprintExpr s) x) ++ ")"
-- pprintExpr s (Ite p t1 t2) = "if " ++ pprintProp s p ++ " then " ++ pprintExpr s t1 ++ " else " ++ pprintExpr s t2
-- pprintExpr s (Abs v) =
--   let new = case getSuggestion v of
--               Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
--               Nothing -> S.findMin (availableNames S.\\ s)
--    in "λ" ++ getName new ++ ", " ++ pprintExpr (S.insert new s) (instantiateT (Var new) v)
-- pprintExpr s (Var x) = getName x
-- pprintExpr s (Constant c) = c
--
-- forgetSuggestionsP :: Prop v -> Prop v
-- forgetSuggestionsP = foldP App Ite (\_ y -> Abs (FV Nothing y)) id Var Constant
--   And Or Implies Not PFalse PTrue Eq RApp (\_ y -> Forall (FV Nothing y)) id (\_ y -> Exists (FV Nothing y)) id
--
-- forgetSuggestionsT :: Expr v -> Expr v
-- forgetSuggestionsT = foldT App Ite (\_ y -> Abs (FV Nothing y)) id Var Constant
--   And Or Implies Not PFalse PTrue Eq RApp (\_ y -> Forall (FV Nothing y)) id (\_ y -> Exists (FV Nothing y)) id
--
-- pprintProp' :: (Ord v, Show v) => Prop v -> String
-- pprintProp' = pprintProp show availableLetters
-- pprintExpr' :: (Ord v, Show v) => Expr v -> String
-- pprintExpr' = pprintExpr show availableLetters

someFunc :: IO ()
someFunc = return ()
