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
deriving instance Show v => Show (WithFreeVar Term v)
-- | Prints the internal structure (not for user consumption). Note we could use
-- @`Show1` t => `Show` (`WithFreeVar` t v)@ here like for `Eq` but it seems much
-- more painful to write like that
deriving instance Show v => Show (WithFreeVar Prop v)

-- | The type of terms with free variables of type v.
data Term v
  = App (Term v) [Term v]
    -- ^ A function application. Note that the function itself can be a term.
  | Ite (Prop v) (Term v) (Term v)
    -- ^ An if\/then\/else expression. Useful for specifying functions by cases, for example.
  | Abs (WithFreeVar Term v)
    -- ^ A function abstraction (eg \(x \mapsto x^2\)).
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
instance Eq1 Term where
  liftEq f (App g xs) (App h ys) = liftEq f g h && and (zipWith (liftEq f) xs ys)
  liftEq f (Ite i1 t1 e1) (Ite i2 t2 e2) = liftEq f i1 i2 && liftEq f t1 t2 && liftEq f e1 e2
  liftEq f (Abs x) (Abs y) = liftEq f x y
  liftEq f (Var x) (Var y) = f x y
  liftEq f (Constant x) (Constant y) = x == y
  liftEq _ _ _ = False

-- | Note this considers expressions with different name suggestions to be
-- different. See `AlphaEq`.
instance Eq v => Eq (Term v) where
  (==) = liftEq (==)

-- | The type of propositions with free variables of type `v`.
data Prop v
  = And (Prop v) (Prop v)
  | Or (Prop v) (Prop v)
  | Implies (Prop v) (Prop v)
  | Not (Prop v)
  | PFalse
  | PTrue
  | Eq (Term v) (Term v)
  | RApp (Term v) [Term v]
  | Forall (WithFreeVar Prop v)
  | Exists (WithFreeVar Prop v)
  deriving ( Show          -- ^ stock derivation of 'Show', not for user consumption.
           , Functor       -- ^ stock derivation of 'Functor'
           , Foldable      -- ^ stock derivation of 'Foldable'
           , Traversable   -- ^ stock derivation of 'Traversable'
           )

instance Eq1 Prop where
  liftEq f (And p1 q1) (And p2 q2) = liftEq f p1 p2 && liftEq f q1 q2
  liftEq f (Or p1 q1) (Or p2 q2) = liftEq f p1 p2 && liftEq f q1 q2
  liftEq f (Implies p1 q1) (Implies p2 q2) = liftEq f p1 p2 && liftEq f q1 q2
  liftEq f (Not p1) (Not p2) = liftEq f p1 p2
  liftEq f PFalse PFalse = True
  liftEq f PTrue PTrue = True
  liftEq f (Eq t1 u1) (Eq t2 u2) = liftEq f t1 t2 && liftEq f u1 u2
  liftEq f (RApp t1 u1) (RApp t2 u2) = liftEq f t1 t2 && and (zipWith (liftEq f) u1 u2)
  liftEq f (Forall p1) (Forall p2) = liftEq f p1 p2
  liftEq f (Exists p1) (Exists p2) = liftEq f p1 p2
  liftEq _ _ _ = False

class AlphaEq t where
  (~=) :: t -> t -> Bool

class AlphaEq1 f where
  liftAlphaEq :: (a -> b -> Bool) -> f a -> f b -> Bool

instance AlphaEq1 t => AlphaEq1 (WithFreeVar t) where
  liftAlphaEq f (FV n1 p1) (FV n2 p2) = liftAlphaEq (liftEq f) p1 p2

instance AlphaEq1 Term where
  liftAlphaEq f (App g xs) (App h ys) = liftAlphaEq f g h && and (zipWith (liftAlphaEq f) xs ys)
  liftAlphaEq f (Ite i1 t1 e1) (Ite i2 t2 e2) = liftAlphaEq f i1 i2 && liftAlphaEq f t1 t2 && liftAlphaEq f e1 e2
  liftAlphaEq f (Abs x) (Abs y) = liftAlphaEq f x y
  liftAlphaEq f (Var x) (Var y) = f x y
  liftAlphaEq f (Constant x) (Constant y) = x == y
  liftAlphaEq _ _ _ = False

instance AlphaEq1 Prop where
  liftAlphaEq f (And p1 q1) (And p2 q2) = liftAlphaEq f p1 p2 && liftAlphaEq f q1 q2
  liftAlphaEq f (Or p1 q1) (Or p2 q2) = liftAlphaEq f p1 p2 && liftAlphaEq f q1 q2
  liftAlphaEq f (Implies p1 q1) (Implies p2 q2) = liftAlphaEq f p1 p2 && liftAlphaEq f q1 q2
  liftAlphaEq f (Not p1) (Not p2) = liftAlphaEq f p1 p2
  liftAlphaEq f PFalse PFalse = True
  liftAlphaEq f PTrue PTrue = True
  liftAlphaEq f (Eq t1 u1) (Eq t2 u2) = liftAlphaEq f t1 t2 && liftAlphaEq f u1 u2
  liftAlphaEq f (RApp t1 u1) (RApp t2 u2) = liftAlphaEq f t1 t2 && and (zipWith (liftAlphaEq f) u1 u2)
  liftAlphaEq f (Forall p1) (Forall p2) = liftAlphaEq f p1 p2
  liftAlphaEq f (Exists p1) (Exists p2) = liftAlphaEq f p1 p2
  liftAlphaEq _ _ _ = False

instance Eq v => AlphaEq (Prop v) where
  (~=) = liftAlphaEq (==)
instance Eq v => AlphaEq (Term v) where
  (~=) = liftAlphaEq (==)
instance (AlphaEq1 t, Eq v) => AlphaEq (WithFreeVar t v) where
  (~=) = liftAlphaEq (==)

gfoldT :: forall m t p.
          (forall v. t v -> [t v] -> t v) ->                     -- app
          (forall v. p v -> t v -> t v -> t v) ->                -- ite
          (forall v. Maybe Name -> t (Maybe v) -> t v) ->        -- abs
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift abs
          (forall v. m v -> t v) ->                              -- variable
          (forall v. String -> t v) ->                           -- constant
          (forall v. p v -> p v -> p v) ->                       -- and
          (forall v. p v -> p v -> p v) ->                       -- or
          (forall v. p v -> p v -> p v) ->                       -- implies
          (forall v. p v -> p v) ->                              -- not
          (forall v. p v) ->                                     -- pfalse
          (forall v. p v) ->                                     -- ptrue
          (forall v. t v -> t v -> p v) ->                       -- eq
          (forall v. t v -> [t v] -> p v) ->                     -- rel
          (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- forall
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift forall
          (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- exists
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift exists
          forall a. Term (m a) -> t a
gfoldT fapp fite fabs flabs fvar fconst
  fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists = runT
  where runT :: forall a. Term (m a) -> t a
        runT (App f xs) = fapp (runT f) (runT <$> xs)
        runT (Ite p t1 t2) = fite (runP p) (runT t1) (runT t2)
        runT (Abs (FV n p)) = fabs n (runT (flabs <$> p))
        runT (Var v) = fvar v
        runT (Constant s) = fconst s
        runP = gfoldP fapp fite fabs flabs fvar fconst
                fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists

gfoldP :: forall m t p.
          (forall v. t v -> [t v] -> t v) ->                     -- app
          (forall v. p v -> t v -> t v -> t v) ->                -- ite
          (forall v. Maybe Name -> t (Maybe v) -> t v) ->        -- abs
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift abs
          (forall v. m v -> t v) ->                              -- variable
          (forall v. String -> t v) ->                           -- constant
          (forall v. p v -> p v -> p v) ->                       -- and
          (forall v. p v -> p v -> p v) ->                       -- or
          (forall v. p v -> p v -> p v) ->                       -- implies
          (forall v. p v -> p v) ->                              -- not
          (forall v. p v) ->                                     -- pfalse
          (forall v. p v) ->                                     -- ptrue
          (forall v. t v -> t v -> p v) ->                       -- eq
          (forall v. t v -> [t v] -> p v) ->                     -- rel
          (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- forall
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift forall
          (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- exists
          (forall v. Maybe (m v) -> m (Maybe v)) ->              -- lift exists
          forall a. Prop (m a) -> p a
gfoldP fapp fite fabs flabs fvar fconst
  fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists = runP
  where runP :: forall a. Prop (m a) -> p a
        runP (And p1 p2) = fand (runP p1) (runP p2)
        runP (Or p1 p2) = for (runP p1) (runP p2)
        runP (Implies p1 p2) = fimp (runP p1) (runP p2)
        runP (Not p1) = fnot (runP p1)
        runP PFalse = ffalse
        runP PTrue = ftrue
        runP (Eq t1 t2) = feq (runT t1) (runT t2)
        runP (RApp r ts) = frel (runT r) (runT <$> ts)
        runP (Forall (FV n p)) = fforall n (runP (flforall <$> p))
        runP (Exists (FV n p)) = fexists n (runP (flexists <$> p))
        runT = gfoldT fapp fite fabs flabs fvar fconst
                fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists

foldT :: forall t p.
         (forall v. t v -> [t v] -> t v) ->                     -- app
         (forall v. p v -> t v -> t v -> t v) ->                -- ite
         (forall v. Maybe Name -> t (Maybe v) -> t v) ->        -- abs
         (forall v. Maybe v -> Maybe v) ->              -- lift abs
         (forall v. v -> t v) ->                              -- variable
         (forall v. String -> t v) ->                           -- constant
         (forall v. p v -> p v -> p v) ->                       -- and
         (forall v. p v -> p v -> p v) ->                       -- or
         (forall v. p v -> p v -> p v) ->                       -- implies
         (forall v. p v -> p v) ->                              -- not
         (forall v. p v) ->                                     -- pfalse
         (forall v. p v) ->                                     -- ptrue
         (forall v. t v -> t v -> p v) ->                       -- eq
         (forall v. t v -> [t v] -> p v) ->                     -- rel
         (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- forall
         (forall v. Maybe v -> Maybe v) ->              -- lift forall
         (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- exists
         (forall v. Maybe v -> Maybe v) ->              -- lift exists
         forall a. Term a -> t a
foldT fapp fite fabs flabs fvar fconst
  fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists x =
    gfoldT @Identity fapp fite fabs coerce (fvar . runIdentity) fconst
      fand for fimp fnot ffalse ftrue feq frel fforall coerce fexists coerce (coerce <$> x)

foldP :: forall t p.
         (forall v. t v -> [t v] -> t v) ->                     -- app
         (forall v. p v -> t v -> t v -> t v) ->                -- ite
         (forall v. Maybe Name -> t (Maybe v) -> t v) ->        -- abs
         (forall v. Maybe v -> Maybe v) ->              -- lift abs
         (forall v. v -> t v) ->                              -- variable
         (forall v. String -> t v) ->                           -- constant
         (forall v. p v -> p v -> p v) ->                       -- and
         (forall v. p v -> p v -> p v) ->                       -- or
         (forall v. p v -> p v -> p v) ->                       -- implies
         (forall v. p v -> p v) ->                              -- not
         (forall v. p v) ->                                     -- pfalse
         (forall v. p v) ->                                     -- ptrue
         (forall v. t v -> t v -> p v) ->                       -- eq
         (forall v. t v -> [t v] -> p v) ->                     -- rel
         (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- forall
         (forall v. Maybe v -> Maybe v) ->              -- lift forall
         (forall v. Maybe Name -> p (Maybe v) -> p v) ->        -- exists
         (forall v. Maybe v -> Maybe v) ->              -- lift exists
         forall a. Prop a -> p a
foldP fapp fite fabs flabs fvar fconst
  fand for fimp fnot ffalse ftrue feq frel fforall flforall fexists flexists x =
    gfoldP @Identity fapp fite fabs coerce (fvar . runIdentity) fconst
      fand for fimp fnot ffalse ftrue feq frel fforall coerce fexists coerce (coerce <$> x)

distT :: Maybe (Term v) -> Term (Maybe v)
distT Nothing = Var Nothing
distT (Just x) = Just <$> x

joinT :: Term (Term v) -> Term v
joinT = gfoldT App Ite (\x y -> Abs (FV x y)) distT id Constant
  And Or Implies Not PFalse PTrue Eq RApp (\x y -> Forall (FV x y)) distT (\x y -> Exists (FV x y)) distT

joinP :: Prop (Term v) -> Prop v
joinP = gfoldP App Ite (\x y -> Abs (FV x y)) distT id Constant
  And Or Implies Not PFalse PTrue Eq RApp (\x y -> Forall (FV x y)) distT (\x y -> Exists (FV x y)) distT

bindP :: Prop a -> (a -> Term b) -> Prop b
bindP p f = joinP (f <$> p)

instance Applicative Term where
  pure = Var
  (<*>) = ap

instance Monad Term where
  x >>= f = joinT (f <$> x)
  -- TODO (BM): there should be a more efficient way of implementing this
  --            right now it can do two full traversals

peanoOne :: Prop v
peanoOne =
    Forall $ FV (Just (Name "x")) $ Not $
      Eq
       (App (Constant "succ") [Var Nothing])
       (App (Constant "zero") [])

unaryApply :: String -> Term v -> Term v
unaryApply f x = App (Constant f) [x]

-- Remembers the name suggestion
abstractP :: Name -> Prop Name -> WithFreeVar Prop Name
abstractP x = FV (Just x) . fmap (\y -> if x == y then Nothing else Just y)

-- Remembers the name suggestion
abstractT :: Name -> Term Name -> WithFreeVar Term Name
abstractT x = FV (Just x) . fmap (\y -> if x == y then Nothing else Just y)

-- Has no name suggestion
abstractP' :: Eq v => v -> Prop v -> WithFreeVar Prop v
abstractP' x = FV Nothing . fmap (\y -> if x == y then Nothing else Just y)

-- Has no name suggestion
abstractT' :: Eq v => v -> Term v -> WithFreeVar Term v
abstractT' x = FV Nothing . fmap (\y -> if x == y then Nothing else Just y)

instantiateT :: Term v -> WithFreeVar Term v -> Term v
instantiateT x = (>>= maybe x Var) . getScoped

instantiateP :: Term v -> WithFreeVar Prop v -> Prop v
instantiateP x = (`bindP` maybe x Var) . getScoped

forall :: Name -> Prop Name -> Prop Name
forall x p = Forall (abstractP x p)

exists :: Name -> Prop Name -> Prop Name
exists x p = Exists (abstractP x p)

instantiateForall :: Prop v -> Term v -> Maybe (Prop v)
instantiateForall (Forall p) x = Just (instantiateP x p)
instantiateForall _ _ = Nothing

instantiateExists :: Prop v -> Term v -> Maybe (Prop v)
instantiateExists (Exists p) x = Just (instantiateP x p)
instantiateExists _ _ = Nothing

peanoTwo :: Prop Name
peanoTwo =
  forall (Name "x") $
    forall (Name "y") $
      Implies
        (Eq (unaryApply "succ" (Var (Name "x")))
            (unaryApply "succ" (Var (Name "y"))))
        (Eq (Var (Name "x")) (Var (Name "y")))

toClosedT :: Term v -> Maybe (Term a)
toClosedT = traverse $ const Nothing

toClosedP :: Prop v -> Maybe (Prop a)
toClosedP = traverse $ const Nothing

-- change to hashset
availableNames :: Set Name
availableNames = S.fromAscList $ map (Name . (:[])) "abcdefghijklmnopqrstuvwxyz"

-- the set should have the names which are *not* available to use
pprintProp :: Set Name -> Prop Name -> String
pprintProp s (And p1 p2) = "(" ++ pprintProp s p1 ++ " ∧ " ++ pprintProp s p2 ++ ")"
pprintProp s (Or p1 p2) = "(" ++ pprintProp s p1 ++ " ∨ " ++ pprintProp s p2 ++ ")"
pprintProp s (Implies p1 p2) = "(" ++ pprintProp s p1 ++ " ⇒ " ++ pprintProp s p2 ++ ")"
pprintProp s (Not p) = "(¬" ++ pprintProp s p ++ ")"
pprintProp s PFalse = "⊥"
pprintProp s PTrue = "⊤"
pprintProp s (Eq t u) = "(" ++ pprintTerm s t ++ " = " ++ pprintTerm s u ++ ")"
pprintProp s (RApp g x) =  pprintTerm s g ++ "(" ++ intercalate ", " (map (pprintTerm s) x) ++ ")"
pprintProp s (Forall v) =
  let new = case getSuggestion v of
              Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
              Nothing -> S.findMin (availableNames S.\\ s)
  in "∀" ++ getName new ++ ", " ++ pprintProp (S.insert new s) (instantiateP (Var new) v)
pprintProp s (Exists v) =
  let new = case getSuggestion v of
              Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
              Nothing -> S.findMin (availableNames S.\\ s)
  in "∃" ++ getName new ++ ", " ++ pprintProp (S.insert new s) (instantiateP (Var new) v)

pprintTerm :: Set Name -> Term Name -> String
pprintTerm s (App g x) = pprintTerm s g ++ "(" ++ intercalate ", " (map (pprintTerm s) x) ++ ")"
pprintTerm s (Ite p t1 t2) = "if " ++ pprintProp s p ++ " then " ++ pprintTerm s t1 ++ " else " ++ pprintTerm s t2
pprintTerm s (Abs v) =
  let new = case getSuggestion v of
              Just n -> if n `S.notMember` s then n else S.findMin (availableNames S.\\ s)
              Nothing -> S.findMin (availableNames S.\\ s)
   in "λ" ++ getName new ++ ", " ++ pprintTerm (S.insert new s) (instantiateT (Var new) v)
pprintTerm s (Var x) = getName x
pprintTerm s (Constant c) = c

forgetSuggestionsP :: Prop v -> Prop v
forgetSuggestionsP = foldP App Ite (\_ y -> Abs (FV Nothing y)) id Var Constant
  And Or Implies Not PFalse PTrue Eq RApp (\_ y -> Forall (FV Nothing y)) id (\_ y -> Exists (FV Nothing y)) id

forgetSuggestionsT :: Term v -> Term v
forgetSuggestionsT = foldT App Ite (\_ y -> Abs (FV Nothing y)) id Var Constant
  And Or Implies Not PFalse PTrue Eq RApp (\_ y -> Forall (FV Nothing y)) id (\_ y -> Exists (FV Nothing y)) id

-- pprintProp' :: (Ord v, Show v) => Prop v -> String
-- pprintProp' = pprintProp show availableLetters
-- pprintTerm' :: (Ord v, Show v) => Term v -> String
-- pprintTerm' = pprintTerm show availableLetters

someFunc :: IO ()
someFunc = return ()
