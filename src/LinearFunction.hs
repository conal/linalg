{-# LANGUAGE UndecidableInstances #-}  -- See below
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for all linear map
-- representations.

module LinearFunction where

import CatPrelude
import Category.Isomorphism

-- | Linear functions
newtype L (s :: *) a b = L { unL :: a s -> b s }

instance Category (L s) where
  type Obj' (L s) = Representable
  id = L id
  L g . L f = L (g . f)

instance Monoidal (:*:) (L s) where
  L f *** L g = L (\ (a :*: b) -> f a :*: g b)

instance Cartesian (:*:) (L s) where
  exl = L exlF
  exr = L exrF
  dup = L dupF

instance Comonoidal (:*:) (L s) where (+++) = (***)

instance Additive s => Cocartesian (:*:) (L s) where
  inl = L (:*: zeroV)
  inr = L (zeroV :*:)
  jam = L (uncurryF (+^))

instance Additive s => Biproduct (:*:) (L s)

instance Representable r => MonoidalR r (:.:) (L s) where
  cross :: Obj2 (L s) a b => r (L s a b) -> L s (r :.: a) (r :.: b)
  cross fs = L (Comp1 . liftR2 unL fs . unComp1)

#if 0
                   fs :: r (L s a b)
        liftR2 unL fs :: r (a s) -> r (b s)
Comp1 . liftR2 unL fs . unComp1 :: (r :.: a) s -> (r :.: b) s

cross = L . inNew (liftR2 unL)
#endif

instance Representable r => CartesianR r (:.:) (L s) where
  exs :: Obj (L s) a => r (L s (r :.: a) a)
  exs = tabulate (\ i -> L (\ (Comp1 as) -> as `index` i))
  dups :: Obj (L s) a => L s a (r :.: a)
  dups = L (Comp1 . pureRep)

instance Representable r => ComonoidalR r (:.:) (L s) where
  plus = cross

instance (Additive s, Representable r, Eq (Rep r), Foldable r)
      => CocartesianR r (:.:) (L s) where
  ins :: Obj (L s) a => r (L s a (r :.: a))
  ins = tabulate (L . oneHot)
        -- tabulate $ \ i -> L (oneHot i)
        -- tabulate $ \ i -> L (\ a -> oneHot i a)
  jams :: Obj (L s) a => L s (r :.: a) a
  jams = L (\ (Comp1 as) -> foldr (+^) zeroV as)

-- TODO: can we define ins without Eq (Rep r)?

-- Illegal nested constraint ‘Eq (Rep r)’
-- (Use UndecidableInstances to permit this)

oneHot :: (Obj (L s) a, Representable r, Eq (Rep r), Additive s)
       => Rep r -> a s -> (r :.: a) s
oneHot i a = Comp1 (tabulate (\ j -> if i == j then a else zeroV))

class Scalable l where
  scale :: Semiring s => s -> l s Par1 Par1

instance Scalable L where
  scale s = L (s *^)

class LinearMap l where
  -- | Semantic function for all linear map representations. Correctness of
  -- every operation on every representation is specified by requiring mu to be
  -- homomorphic for (distributes over) that operation. For instance, mu must be
  -- a functor (Category homomorphism).
  mu :: (Obj2 (L s) a b, Obj2 (l s) a b) => l s a b <-> L s a b

-- TODO: maybe generalize so that LHS and RHS objects needn't match. In other
-- words, the mu functor can have non-identity object maps.

-- Note that scale, join2, fork2, join, and fork (the basic building blocks of
-- linear maps) are all linear isomorphisms. With a little help, we can combine
-- them into a single isomorphism. That help can be something that combines five
-- arrows having signatures matching those building blocks into a single arrow.

-- Trivial instance
instance LinearMap L where mu = id

-- Linear map application (for all representations)
infixl 9 @@
(@@) :: (LinearMap l, C2 Representable a b, Obj2 (l s) a b)
     => l s a b -> a s -> b s
m @@ a = unL (isoFwd mu m) a


-------------------------------------------------------------------------------
-- | Linear map as vector
-------------------------------------------------------------------------------

newtype LV l (a :: * -> *) (b :: * -> *) s = LV { unLV :: l s a b }

#if 0
-- For now instances have l = L, but we will generalize.

instance (Representable a, Eq (Rep a), Foldable a, Representable b)
      => Functor (LV L a b) where
  fmap = fmapRep

instance (Representable a, Eq (Rep a), Foldable a, Representable b)
      => Distributive (LV L a b) where
  distribute = distributeRep

-- TODO: consider more efficient fmap and distribute definitions

instance (Representable a, Eq (Rep a), Foldable a, Representable b)
      => Representable (LV L a b) where
  type Rep (LV L a b) = Rep b :* Rep a
  tabulate = LV . unMat . tabulate
  index = index . toMat . unLV

-- Could not deduce (Semiring a1) arising from a use of ‘unMat’
-- from the context: (Representable a, Eq (Rep a), Foldable a,
--                    Representable b)
--   bound by the instance declaration

-- I don't think this error if we stick with Data.Functor.Rep, because it won't
-- let us constrain the codomain to be (for instance) a semiring (or later a
-- category morphism). We can add our own constrained Representable. While we're
-- at it, replace tabulate and index with a single isomorphism-valued method.
-- Bonus: we can define this Representable LV instance as a simple isomorphism
-- composition.
#endif

-- Row-major matrices, a common data representation for linear maps
type Mat a b = b :.: a

toMat :: (Representable a, Eq (Rep a), Distributive b, Semiring s)
      => L s a b -> Mat a b s
toMat (L f) = Comp1 (distribute (f <$> basis))

#if 0
                   f             :: a s -> b s
                         basis   :: a (a s)
                   f <$> basis   :: a (b s)
       distribute (f <$> basis)  :: b (a s)
Comp1 (distribute (f <$> basis)) :: (b :.: a) s
#endif

unMat :: (Representable a, Eq (Rep a), Foldable a, Functor b, Semiring s)
      => Mat a b s -> L s a b
unMat (Comp1 ab) = L (\ a -> dot a <$> ab)

matIso :: (Representable a, Eq (Rep a), Foldable a, Distributive b, Semiring s)
       => L s a b <-> Mat a b s
matIso = toMat :<-> unMat

-- TODO: generalize toMat from L.

-------------------------------------------------------------------------------
-- | Vector/map isomorphisms
-------------------------------------------------------------------------------

dot :: (Representable a, Foldable a, Semiring s) => a s -> (a s -> s)
dot u v = sum (liftR2 (*) u v)

dot' :: (Representable a, Eq (Rep a), Semiring s) => (a s -> s) -> a s
dot' f = f <$> basis

-- Basis vectors / identity matrix
basis :: (Representable a, Eq (Rep a), Semiring s) => a (a s)
basis = tabulate (\ i -> tabulate (\ j -> if i == j then one else zero))

dotIso :: (Representable a, Eq (Rep a), Foldable a, Semiring s) => a s <-> (a s -> s)
dotIso = dot :<-> dot'

-- TODO: prove that dot & dot' are inverses

-- TODO: basis vs oneHot

-- Convert vector to vector-to-scalar linear map ("dual vector")
toScalar :: (Representable a, Foldable a, Semiring s) => a s -> L s a Par1
toScalar a = L (Par1 . dot a)

toScalar' :: (Representable a, Eq (Rep a), Semiring s) => L s a Par1 -> a s
toScalar' f = dot' (unPar1 . unL f)

#if 0
  toScalar' (toScalar a)
= toScalar' (L (Par1 . dot a))
= dot' (unPar1 . unL (L (Par1 . dot a)))
= dot' (unPar1 . Par1 . dot a)
= dot' (dot a)
= a

  toScalar (toScalar' f)
= toScalar (dot' (unPar1 . unL f))
= toScalar (dot' (unPar1 . unL f))
= L (Par1 . dot (dot' (unPar1 . unL f)))
= L (Par1 . unPar1 . unL f)
= L (unL f)
= f
#endif

toScalarIso :: (Representable a, Eq (Rep a), Foldable a, Semiring s)
            => a s <-> L s a Par1
toScalarIso = toScalar :<-> toScalar'

-- TODO: build toScalarIso from isomorphisms rather than from explicit (:<->).
-- Probably use dom & cod from Closed (not yet in Category).

-- TODO: generalize dot from Semiring to Category

-- Convert vector to scalar-to-vector linear map ("dual vector")
fromScalar :: (Functor a, Semiring s) => a s -> L s Par1 a
fromScalar a = L ((*^ a) . unPar1)

fromScalar' :: Semiring s => L s Par1 a -> a s
fromScalar' (L f) = f (Par1 one)

fromScalarIso :: (Functor a, Semiring s) => a s <-> L s Par1 a
fromScalarIso = fromScalar :<-> fromScalar'

-- toScalar' is very expensive! The data representations are much more efficient.

#if 0
-- Isomorphism proofs

  (fromScalar' . fromScalar) a
= fromScalar' (fromScalar a)
= fromScalar' (L (*^ a) . unPar1)
= ((*^ a) . unPar1) (Par1 one)
= (*^ a) (unPar1 (Par1 one))
= (*^ a) one
= one *^ a
= (one *) <$> a
= id <$> a
= id <$> a
= a

  (fromScalar . fromScalar') (L f)
= fromScalar (fromScalar' (L f))
= fromScalar (f (Par1 one))
= L ((*^ (f (Par1 one))) . unPar1)
= L (\ (Par1 s) -> (*^ (f (Par1 one))) (unPar1 (Par1 s)))
= L (\ (Par1 s) -> (*^ (f (Par1 one))) s)
= L (\ (Par1 s) -> s *^ f (Par1 one))
= L (\ (Par1 s) -> f (s *^ Par1 one))
= L (\ (Par1 s) -> f (Par1 s))
= L f

-- TODO: build fromScalarIso from isomorphisms rather than from explicit (:<->).

#endif

scaleIso :: Semiring s => s <-> L s Par1 Par1
scaleIso = scale :<-> unscale

unscale :: Semiring s => L s Par1 Par1 -> s
unscale = unPar1 . toScalar'

-- unscale (L f) = exNew f one -- unPar1 (f (Par1 one))

-------------------------------------------------------------------------------
-- | Some "products", defined in terms of composition
-------------------------------------------------------------------------------

inner :: (Representable a, Foldable a, Semiring s) => a s -> a s -> L s Par1 Par1
b `inner` a = toScalar b . fromScalar a

outer :: (Representable a, Foldable a, Representable b, Semiring s)
      => b s -> a s -> L s a b
b `outer` a = fromScalar b . toScalar a

