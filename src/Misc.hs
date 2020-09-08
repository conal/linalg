-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Miscellany

module Misc where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip, product)
import GHC.Types (Constraint)
import GHC.Generics ((:*:)(..),(:+:)(..), Generic, Generic1)
import Control.Newtype.Generics
import Data.Coerce (coerce)

import Data.Functor.Rep

-------------------------------------------------------------------------------
-- | More convenient type notation
-------------------------------------------------------------------------------

infixl 7 :*
type (:*)  = (,)

infixl 6 :+
type (:+)  = Either


-------------------------------------------------------------------------------
-- | Constraint helpers
-------------------------------------------------------------------------------

#if 1
-- Experiment. Smaller Core?
type C1 (con :: u -> Constraint) a = con a
type C2 (con :: u -> Constraint) a b = (con a, con b)
type C3 (con :: u -> Constraint) a b c = (con a, con b, con c)
type C4 (con :: u -> Constraint) a b c d = (con a, con b, con c, con d)
type C5 (con :: u -> Constraint) a b c d e = (con a, con b, con c, con d, con e)
type C6 (con :: u -> Constraint) a b c d e f = (con a, con b, con c, con d, con e, con f)
#else
type C1 (con :: u -> Constraint) a = con a
type C2 con a b         = (C1 con a, con b)
type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C2 con a b, C2 con c d)
type C5 con a b c d e   = (C3 con a b c, C2 con d e)
type C6 con a b c d e f = (C3 con a b c, C3 con d e f)
#endif


-------------------------------------------------------------------------------
-- | Semirings
-------------------------------------------------------------------------------

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

instance Additive Double where { zero = 0 ; (+) = (P.+) }
instance Semiring Double where { one  = 1 ; (*) = (P.*) }

instance Additive Bool where { zero = False ; (+) = (||) }
instance Semiring Bool where { one  = True  ; (*) = (&&) }

newtype Sum a = Sum { getSum :: a }
  deriving (Eq, Ord, Read, Show, Bounded, Generic, Generic1, Num, Additive, Semiring)

instance Newtype (Sum a)

instance Additive a => Semigroup (Sum a) where
  (<>) = (+)

instance Additive a => Monoid (Sum a) where
  mempty = zero

instance Functor Sum where
  fmap = coerce

instance Applicative Sum where
  pure  = Sum
  (<*>) = coerce

instance Monad Sum where
  m >>= k = k (getSum m)

newtype Product a = Product { getProduct :: a }
  deriving (Eq, Ord, Read, Show, Bounded, Generic, Generic1, Num, Additive, Semiring)

instance Newtype (Product a)

instance Semiring a => Semigroup (Product a) where
  (<>) = (*)

instance Semiring a => Monoid (Product a) where
  mempty = one

instance Functor Product where
  fmap = coerce

instance Applicative Product where
  pure  = Product
  (<*>) = coerce

instance Monad Product where
  m >>= k = k (getProduct m)

sum :: (Foldable f, Additive a) => f a -> a
sum = ala Sum foldMap

product :: (Foldable f, Semiring a) => f a -> a
product = ala Product foldMap

-- Zero vector
zeroV :: (Representable a, Additive s) => a s
zeroV = pureRep zero

-- | Vector addition
infixl 6 +^
(+^) :: (Representable f, Additive s) => f s -> f s -> f s
(+^) = liftR2 (+)

-- | Vector scaling
infixl 7 *^
(*^) :: (Functor f, Semiring s) => s -> f s -> f s
s *^ a = (s *) <$> a

-- s *^ a = fmap (s *) a
-- (*^) s = fmap (s *)
-- (*^) = fmap . (*)


-------------------------------------------------------------------------------
-- | GHC.Generics utilities
-------------------------------------------------------------------------------

-- Natural transformation
infixl 1 -->
type a --> b = forall s. a s -> b s

exlF :: a :*: b --> a
exlF (a :*: _) = a

exrF :: a :*: b --> b
exrF (_ :*: b) = b

dupF :: a --> a :*: a
dupF a = a :*: a

inlF :: a --> a :+: b
inlF a = L1 a

inrF :: b --> a :+: b
inrF a = R1 a

eitherF :: (a t -> c) -> (b t -> c) -> ((a :+: b) t -> c)
eitherF f _ (L1 a) = f a
eitherF _ g (R1 b) = g b

curryF :: ((a :*: b) s -> c s) -> (a s -> b s -> c s)
curryF f a b = f (a :*: b)

uncurryF :: (a s -> b s -> c s) -> ((a :*: b) s -> c s)
uncurryF g (a :*: b) = g a b

-------------------------------------------------------------------------------
-- | Newtype helpers
-------------------------------------------------------------------------------

-- Type generalization of underF from newtype-generics.
underF :: (Newtype n, Newtype n', o' ~ O n', o ~ O n, Functor f, Functor g)
       => (o -> n) -> (f n -> g n') -> (f o -> g o')
underF _ f = fmap unpack . f . fmap pack
{-# INLINE underF #-}

-- Type generalization of overF from newtype-generics.
overF :: (Newtype n, Newtype n', o' ~ O n', o ~ O n, Functor f, Functor g)
      => (o -> n) -> (f o -> g o') -> (f n -> g n')
overF _ f = fmap pack . f . fmap unpack
{-# INLINE overF #-}

inNew :: (Newtype p, Newtype q) =>
         (O p -> O q) -> (p -> q)
inNew = pack <~ unpack
{-# INLINE inNew #-}

inNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (O p -> O q -> O r) -> (p -> q -> r)
inNew2 = inNew <~ unpack
{-# INLINE inNew2 #-}

-- TODO: inNew3, etc.

exNew :: (Newtype p, Newtype q) =>
         (p -> q) -> (O p -> O q)
exNew = unpack <~ pack
{-# INLINE exNew #-}

exNew2 :: (Newtype p, Newtype q, Newtype r) =>
          (p -> q -> r) -> (O p -> O q -> O r)
exNew2 = exNew <~ pack
{-# INLINE exNew2 #-}

-------------------------------------------------------------------------------
-- | Miscellany
-------------------------------------------------------------------------------

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

infixl 1 <~
infixr 1 ~>

-- | Add pre- and post-processing
(~>) :: forall a b a' b'. (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
(f ~> h) g = h . g . f
-- (~>) = flip (<~)
{-# INLINE (~>) #-}

-- | Add post- and pre-processing
(<~) :: forall a b a' b'. (b -> b') -> (a' -> a) -> ((a -> b) -> (a' -> b'))
(h <~ f) g = h . g . f
{-# INLINE (<~) #-}

-- TODO: Maybe move (<~) and (~>) to Category and generalize from (->)to any category.
