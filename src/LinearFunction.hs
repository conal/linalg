{-# LANGUAGE UndecidableInstances #-}  -- See below
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for all linear map
-- representations.

module LinearFunction where

import CatPrelude
import Category.Isomorphism

-- | Linear functions
newtype L (s :: *) a b = L { unL :: a s -> b s }
  deriving (Generic)

instance Newtype (L s a b)

instance Category (L s) where
  type Obj' (L s) a = Representable a
  id = L id
  L g . L f = L (g . f)

instance Monoidal (:*:) (L s) where
  L f ### L g = L (\ (a :*: b) -> f a :*: g b)

instance Cartesian (:*:) (L s) where
  exl = L exlF
  exr = L exrF
  dup = L dupF

instance Additive s => Cocartesian (:*:) (L s) where
  inl = L (:*: zeroV)
  inr = L (zeroV :*:)
  jam = L (uncurryF (+^))

instance Additive s => Biproduct (:*:) (L s)

instance Representable r => MonoidalR r (:.:) (L s) where
  rmap :: Obj2 (L s) a b => r (L s a b) -> L s (r :.: a) (r :.: b)
  rmap fs = L (Comp1 . liftR2 unL fs . unComp1)

#if 0
                   fs :: r (L s a b)
        liftR2 unL fs :: r (a s) -> r (b s)
Comp1 . liftR2 unL fs . unComp1 :: (r :.: a) s -> (r :.: b) s

rmap = L . inNew (liftR2 unL)
#endif

instance Representable r => CartesianR r (:.:) (L s) where
  exs :: Obj (L s) a => r (L s (r :.: a) a)
  exs = tabulate (\ i -> L (\ (Comp1 as) -> as `index` i))
  dups :: Obj (L s) a => L s a (r :.: a)
  dups = L (Comp1 . pureRep)

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

class Scalable s k where
  scale :: s -> Par1 `k` Par1
  unscale :: Par1 `k` Par1 -> s

-- Will we need " | k -> s"? Not so far.

instance Semiring s => Scalable s (L s) where
  scale s = L (s *^)
  unscale (L f) = unPar1 (f (Par1 one))

class LinearMap s k where
  -- | Semantic function for all linear map representations. Correctness of
  -- every operation on every representation is specified by requiring mu to be
  -- homomorphic for (distributes over) that operation. For instance, mu must be
  -- a functor (Category homomorphism).
  mu :: (Obj2 (L s) a b, Obj2 k a b) => k a b <-> L s a b

-- TODO: maybe generalize so that LHS and RHS objects needn't match. In other
-- words, the mu functor can have non-identity object maps.

-- Note that scale, join2, fork2, join, and fork (the basic building blocks of
-- linear maps) are all linear isomorphisms. With a little help, we can combine
-- them into a single isomorphism. That help can be something that combines five
-- arrows having signatures matching those building blocks into a single arrow.

-- Trivial instance
instance LinearMap s (L s) where mu = id

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

scaleIso :: Scalable s k => s <-> (Par1 `k` Par1)
scaleIso = scale :<-> unscale

-------------------------------------------------------------------------------
-- | Some "products", defined in terms of composition
-------------------------------------------------------------------------------

inner :: (Representable a, Foldable a, Semiring s) => a s -> a s -> L s Par1 Par1
b `inner` a = toScalar b . fromScalar a

outer :: (Representable a, Foldable a, Representable b, Semiring s)
      => b s -> a s -> L s a b
b `outer` a = fromScalar b . toScalar a


-------------------------------------------------------------------------------
-- | Pattern synonyms
-------------------------------------------------------------------------------

-- If & when GHC allows more polymorphic patterns, these definitions will move
-- to Category.hs

pattern (:&) :: (Cartesian p k, Obj3 k a c d)
             => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
pattern f :& g <- (unfork2 -> (f,g)) where (:&) = (&&&)
{-# COMPLETE (:&) :: L #-}

pattern (:|) :: (Cocartesian co k, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
{-# COMPLETE (:|) :: L #-}

pattern Fork :: (CartesianR h p k, Obj2 k f g) => h (k f g) -> k f (p h g)
pattern Fork ms <- (unfork -> ms) where Fork = fork
{-# COMPLETE Fork :: L #-}

pattern Join :: (CocartesianR h p k, Obj2 k f g) => h (k f g) -> k (p h f) g
pattern Join ms <- (unjoin -> ms) where Join = join
{-# COMPLETE Join :: L #-}
