{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

{-|
An implementation of "I am not a number: I am a free variable" by Conor
McBride and James McKinna, for the sake of understanding it better.
-}

module Prisoner where

import Control.Applicative
import Control.Monad

infixl 4 :<
data Stack x = Empty | Stack x :< x
  deriving (Eq, Show, Functor)

infixl 4 +<
(+<) :: Stack x -> Stack x -> Stack x
xs +< Empty = xs
xs +< (ys :< y) = xs +< ys :< y

instance Applicative Stack where
  pure = (Empty :<)
  (<*>) = ap

instance Monad Stack where
  Empty >>= f = Empty
  (xs :< x) >>= f = (xs >>= f) +< f x

instance Alternative Stack where
  empty = Empty
  (<|>) = (+<)

instance MonadPlus Stack where

type Name = Stack (String, Int)

infixl 6 //
(//) :: Name -> String -> Name
me // s = me :< (s, 0)

nm :: String -> Name
nm s = Empty // s

type Agency agent = Name -> agent

infixl 9 :$
infixl 6 :->

data Expr = F Name
          | B Int
          | Expr :$ Expr
          | Expr :-> Scope
          deriving (Eq, Show)

newtype Scope = Scope Expr
  deriving (Eq, Show)

abstract :: Name -> Expr -> Scope
abstract me expr = Scope (letMeB 0 expr) where
  letMeB this (F you)
    | you == me                       = B this
    | otherwise                       = F you
  letMeB this (B that)                = B that
  letMeB this (fun :$ arg)            = letMeB this fun :$ letMeB this arg
  letMeB this (domain :-> Scope body) = letMeB this domain :-> Scope (letMeB (this + 1) body)

instantiate :: Expr -> Scope -> Expr
instantiate what (Scope body) = whatsB 0 body where
  whatsB this (B that)
    | this == that = what
    | otherwise = B that
  whatsB this (F you) = F you
  whatsB this (fun :$ arg) = whatsB this fun :$ whatsB this arg
  whatsB this (domain :-> Scope bod) = whatsB this domain :-> Scope (whatsB (this + 1) bod)

substitute :: Expr -> Name -> Expr -> Expr
substitute image me = instantiate image . abstract me

unapply :: MonadPlus m => Expr -> m (Expr, Expr)
unapply (fun :$ arg) = return (fun, arg)
unapply _ = mzero

infix 5 :∈
data Binding = Name :∈ Expr
  deriving (Eq, Show)

name :: Binding -> Name
name (me :∈ _) = me

var :: Binding -> Expr
var = F . name

type Zipper = Stack Step

data Step = Fun () Expr
          | Arg Expr ()
          | Domain () Scope
          | Range Binding ()

infixr 6 -->
(-->) :: Binding -> Expr -> Expr
(me :∈ domain) --> range = domain :-> abstract me range

infix <--
(<--) :: MonadPlus m => Agency (Expr -> m (Binding, Expr))
me <-- (domain :-> scope) = return (me :∈ domain, instantiate (F me) scope)
me <-- _                  = mzero

type Prefix = Stack Binding
infixr 6 ->>
(->>) :: Prefix -> Expr -> Expr
Empty ->> expr = expr
(bindings :< binding) ->> range = bindings ->> binding --> range

unprefix :: Agency (String -> Expr -> (Prefix, Expr))
unprefix me x things = introduce 1 (Empty, things) where
  introduce :: Int -> (Prefix, Expr) -> (Prefix, Expr)
  introduce i (bindings, thing) =
    case (me :< (x, i)) <-- thing of
      Just (binding, range) -> introduce (i + 1) (bindings :< binding, range)
      Nothing -> (bindings, thing)

weaken :: Agency (Expr -> Expr -> Expr)
weaken me dom expr = doms ->> (me // "y" :∈ dom) --> range where
  (doms, range) = unprefix me "x" expr

infixl 9 $$
($$) :: Expr -> [Expr] -> Expr
expr $$ [] = expr
fun $$ (arg : args) = fun :$ arg $$ args

unapplies :: Expr -> (Expr, [Expr])
unapplies expr = peel (expr, []) where
  peel (fun :$ arg, args) = peel (fun, arg : args)
  peel funargs = funargs

data Analysis = ForAll Prefix Name [Expr]
  deriving Show

analysis :: Agency (String -> Expr -> Analysis)
analysis me x expr = ForAll prefix f args where
  (prefix, range) = unprefix me x expr
  (F f, args) = unapplies range

infixl 9 -$$
(-$$) :: Name -> Prefix -> Expr
f -$$ parameters = apply (F f) parameters where
  apply expr Empty = expr
  apply fun (bindings :< a :∈ _) = apply fun bindings :$ F a

generalize :: Prefix -> Binding -> (Binding, Expr -> Expr)
generalize bindings (me :∈ expr) =
  (me :∈ bindings ->> expr, substitute (me -$$ bindings) me)

makeInductiveElim :: Agency (Binding -> Prefix -> Binding)
makeInductiveElim me (family :∈ famtype) constructors =
  me :∈ targets ->>
        motive -->
        fmap method constructors ->>
        name motive -$$ targets
          where
            ForAll indices set [] = analysis me "i" famtype
            targets = indices :< me // "x" :∈ family -$$ indices
            motive = me // "P" :∈ targets ->> F (nm "Set")
            method :: Binding -> Binding
            method (con :∈ contype) =
              meth :∈ conargs ->>
                (conargs >>= indhyp) ->>
                  var motive $$ conindices :$ (con -$$ conargs)
                    where
                      meth = me // "m" +< con
                      ForAll conargs fam conindices = analysis meth "a" contype
                      indhyp :: Binding -> Prefix
                      indhyp (arg :∈ argtype) = do
                        guard (argfam == family) -- yield Empty if arg is non-recursive
                        return (arg // "h" :∈ argargs ->>
                                              var motive $$ argindices :$ (arg -$$ argargs))
                          where ForAll argargs argfam argindices = analysis meth "y" argtype

vec :: Binding
vec = nm "vec" :∈ (nm "X" :∈ F (nm "Set")) --> (nm "n" :∈ F (nm "nat")) --> F (nm "Set")

vnil :: Binding
vnil = nm "vnil" :∈ (nm "X" :∈ F (nm "Set")) --> (F (nm "vec") :$ F (nm "X") :$ F (nm "zero"))

vcons :: Binding
vcons = nm "vcons" :∈
  (Empty :< (nm "X" :∈ F (nm "Set")) :< (nm "n" :∈ F (nm "Nat")) :< (nm "x" :∈ F (nm "X")) :< (nm "xs" :∈ (F (nm "vec") :$ F (nm "X") :$ F (nm "n"))))
  ->> (F (nm "vec") :$ F (nm "X") :$ (F (nm "suc") :$ F (nm "n")))

example :: Binding
example = makeInductiveElim (nm "C") vec (Empty :< vnil :< vcons)

pprintN' :: Int -> Name -> String
pprintN' n Empty = ""
pprintN' n (Empty :< y) = fst y ++ show (snd y)
pprintN' n (ys :< y) = pprintN' n ys ++ "-" ++ fst y ++ show (snd y)

pprintB' :: Int -> Binding -> String
pprintB' n (dom :∈ e) = pprintN' n dom ++ " ∈ " ++ pprintE' n e

pprintE' :: Int -> Expr -> String
pprintE' n (F nme) = pprintN' n nme
pprintE' n (e1 :$ e2) = pprintE' n e1 ++ "(" ++ pprintE' n e2 ++ ")"
pprintE' n e = case (Empty :< ("x", n)) <-- e of
  Just (bd, e2) -> "∀ (" ++ pprintB' (n+1) bd ++ "), " ++ pprintE' (n+1) e2
  Nothing -> "failed"

pprintP' :: Prefix -> String
pprintP' Empty = ""
pprintP' (ys :< y) = pprintP' ys ++ pprintB' 0 y
