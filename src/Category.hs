{-# LANGUAGE UndecidableInstances #-} -- see below
{-# LANGUAGE UndecidableSuperClasses #-} -- see below

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Functor category classes

module Category where

import qualified Prelude as P
import Prelude hiding (id,(.),curry,uncurry)
import GHC.Types (Constraint)
import GHC.Exts (Coercible)
import Data.Monoid (Ap(..))
import Data.Functor.Rep

import Misc
import Orphans ()

-- https://github.com/conal/linalg/pull/28#issuecomment-670313952
class    Obj' k a => Obj k a
instance Obj' k a => Obj k a

-- Illegal constraint ‘Obj' k a’ in a superclass context
--   (Use UndecidableInstances to permit this)

-- Potential superclass cycle for ‘Obj’
--   one of whose superclass constraints is headed by a type family:
--     ‘Obj' k a’
-- Use UndecidableSuperClasses to accept this

class Category (k :: u -> u -> *) where
  type Obj' k (a :: u) :: Constraint
  type instance Obj' k u = ()
  infixr 9 .
  id :: Obj k a => a `k` a
  (.) :: Obj3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)

-- TODO: does (.) really need these constraints? We may know better when we try
-- "matrices" (non-inductive and inductive) with and without these (.)
-- constraints. Similarly for other classes.

type Obj2 k a b         = C2 (Obj k) a b
type Obj3 k a b c       = C3 (Obj k) a b c
type Obj4 k a b c d     = C4 (Obj k) a b c d
type Obj5 k a b c d e   = C5 (Obj k) a b c d e
type Obj6 k a b c d e f = C6 (Obj k) a b c d e f

-- TODO: Maybe eliminate all type definitions based on Obj2 .. Obj6 in favor of
-- their definitions, which are not much longer anyway.

-- Products, coproducts, exponentials of objects are objects.
-- Seee https://github.com/conal/linalg/pull/28#issuecomment-670313952
type ObjBin p k = ((forall a b. Obj2 k a b => Obj k (a `p` b)) :: Constraint)

class (Category k, ObjBin p k) => Monoidal p k where
  infixr 3 ###
  (###) :: Obj4 k a b c d => (a `k` c) -> (b `k` d) -> (a `p` b) `k` (c `p` d)

-- TODO: make p an associated type, and see how the class and instance
-- definitions look in comparison.
--
-- @dwincort (https://github.com/conal/linalg/pull/28#discussion_r466989563):
-- "From what I can tell, if we use `QuantifiedConstraints` with `p`, then we
-- can't turn it into an associated type. I'm not sure that's so bad, but it's
-- worth noting." See also the GHC error message there.
--
-- TODO: keep poking at this question.

-- TODO: Does it make any sense to move 'p' and its ObjBin into the method
-- signatures, as in MonoidalR below? Should we instead move 'r' in MonoidalR
-- from the method signatures to the class? It feels wrong to me (conal) that
-- there is only one binary product but many n-ary. In another sense, n-ary is
-- even more restrictive than binary: the (type-indexed) tuple-ness of
-- representable functors is wired in, and so is the object kind. For instance,
-- we cannot currently handle n-ary coproducts that are not n-ary cartesian
-- *products*.

first :: (Monoidal p k, Obj3 k a b c) => (a `k` c) -> ((a `p` b) `k` (c `p` b))
first f = f ### id

second :: (Monoidal p k, Obj3 k a b d) => (b `k` d) -> ((a `p` b) `k` (a `p` d))
second g = id ### g

class Monoidal p k => Cartesian p k where
  {-# MINIMAL ((exl, exr) | unfork2), ((&&&) | dup) #-}
  exl :: Obj2 k a b => (a `p` b) `k` a
  exl = fst $ unfork2 id
  exr :: Obj2 k a b => (a `p` b) `k` b
  exr = snd $ unfork2 id
  dup :: Obj  k a   => a `k` (a `p` a)
  dup = id &&& id
  infixr 3 &&&
  -- Binary fork
  (&&&) :: Obj3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
  f &&& g = (f ### g) . dup
  -- Inverse of fork2
  unfork2 :: Obj3 k a c d => (a `k` (c `p` d)) -> ((a `k` c) :* (a `k` d))
  unfork2 f = (exl . f , exr . f)

fork2 :: (Cartesian p k, Obj3 k a c d)
      => (a `k` c) :* (a `k` d) -> (a `k` (c `p` d))
fork2 = uncurry (&&&)

-- Exercise: Prove that uncurry (&&&) and unfork2 form an isomorphism.

class Associative p k where
  lassoc :: Obj3 k a b c => (a `p` (b `p` c)) `k` ((a `p` b) `p` c)
  rassoc :: Obj3 k a b c => ((a `p` b) `p` c) `k` (a `p` (b `p` c))

class Symmetric p k where
  swap :: Obj2 k a b => (a `p` b) `k` (b `p` a)

-- TODO: Maybe split Symmetric into Braided and Symmetric, with the latter
-- having an extra law. Maybe Associative as Braided superclass. See
-- <https://hackage.haskell.org/package/categories/docs/Control-Category-Braided.html>.
-- Note that Associative is a superclass of Monoidal in
-- <https://hackage.haskell.org/package/categories/docs/Control-Category-Monoidal.html>.

class Monoidal co k => Cocartesian co k where
  {-# MINIMAL ((inl, inr) | unjoin2), ((|||) | jam) #-}
  inl :: Obj2 k a b => a `k` (a `co` b)
  inl = fst $ unjoin2 id
  inr :: Obj2 k a b => b `k` (a `co` b)
  inr = snd $ unjoin2 id
  jam :: Obj  k a   => (a `co` a) `k` a
  jam = id ||| id
  -- Binary join
  infixr 2 |||
  (|||) :: Obj3 k a b c => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
  f ||| g = jam . (f ### g)
  -- Inverse of join2
  unjoin2 :: Obj3 k a b c => ((a `co` b) `k` c) -> ((a `k` c) :* (b `k` c))
  unjoin2 f = (f . inl , f . inr)

join2 :: (Cocartesian co k, Obj3 k a b c)
      => (a `k` c) :* (b `k` c) -> ((a `co` b) `k` c)
join2 = uncurry (|||)

-- Exercise: Prove that uncurry (|||) and unjoin2 form an isomorphism.

type Bicartesian p co k = (Cartesian p k, Cocartesian co k)

-- When products and coproducts coincide. A class rather than type synonym,
-- because there are more laws.
class Bicartesian p p k => Biproduct p k

class (Category k, ObjBin e k) => Closed e k where
  (^^^) :: Obj4 k a b c d => (a `k` b) -> (d `k` c) -> ((c `e` a) `k` (d `e` b))

dom :: (Closed e k, Obj3 k c a d) => (d `k` c) -> ((c `e` a) `k` (d `e` a))
dom f = id ^^^ f

cod :: (Closed e k, Obj3 k c a b) => (a `k` b) -> ((c `e` a) `k` (c `e` b))
cod g = g ^^^ id

-- The argument order in (^^^) is opposite that of concat.

class (Monoidal p k, Closed e k) => MonoidalClosed p e k where
  curry   :: Obj3 k a b c => ((a `p` b) `k` c) -> (a `k` (b `e` c))
  uncurry :: Obj3 k a b c => (a `k` (b `e` c)) -> ((a `p` b) `k` c)
  apply   :: Obj2 k a b => ((a `e` b) `p` a) `k` b
  apply = uncurry id
  uncurry g = apply . first g
  {-# MINIMAL curry, (uncurry | apply) #-}

-------------------------------------------------------------------------------
-- | n-ary counterparts (where n is a type, not a number).
-------------------------------------------------------------------------------

-- Assumes functor categories. TODO: look for a clean, poly-kinded alternative.
-- I guess we could generalize from functor composition and functor application.

type ObjR' r p k = ((forall z. Obj k z => Obj k (p r z)) :: Constraint)

class    (Representable r, ObjR' r p k) => ObjR r p k
instance (Representable r, ObjR' r p k) => ObjR r p k

class (Category k, ObjR r p k) => MonoidalR r p k where
  -- | n-ary version of '(###)'
  rmap :: Obj2 k a b => r (a `k` b) -> (p r a `k` p r b)

class MonoidalR r p k => CartesianR r p k where
  {-# MINIMAL ((exs | unfork), (fork | dups)) #-}
  exs  :: Obj k a => r (p r a `k` a)
  exs = unfork id
  dups :: Obj k a => a `k` p r a
  dups = fork (pureRep id)
  fork :: Obj2 k a c => r (a `k` c) -> (a `k` p r c)
  fork fs = rmap fs . dups
  unfork :: Obj2 k a b => a `k` p r b -> r (a `k` b)
  unfork f = (. f) <$> exs

-- Exercise: Prove that fork and unfork form an isomorphism.

-- N-ary biproducts
class MonoidalR r co k => CocartesianR r co k where
  {-# MINIMAL ((ins | unjoin), (join | jams)) #-}
  ins  :: Obj k a => r (a `k` co r a)
  ins = unjoin id
  jams :: Obj k a => co r a `k` a
  jams = join (pureRep id)
  join :: Obj2 k a b => r (a `k` b) -> co r a `k` b
  join fs = jams . rmap fs
  unjoin :: Obj2 k a b => co r a `k` b -> r (a `k` b)
  unjoin f = (f .) <$> ins

type BicartesianR r p co k = (CartesianR r p k, CocartesianR r co k)

-- When products and coproducts coincide. A class rather than type synonym,
-- because there are more laws.
class BicartesianR r p p k => BiproductR r p k

-- Add Abelian and AbelianR?
-- I think f + g = jam . (f ### g) . dup, and sum fs = jams . fork fs.

-------------------------------------------------------------------------------
-- | Deriving-via helpers
-------------------------------------------------------------------------------

-- For deriving via with n-ary products and coproducts.
-- See https://github.com/conal/linalg/pull/54#discussion_r481393523
type Representational1' r =
  ((forall p q. Coercible p q => Coercible (r p) (r q)) :: Constraint)

-- Wrap to avoid impredicativity
class    Representational1' r => Representational1 r
instance Representational1' r => Representational1 r

type RepresentableR r = (Representable r, Representational1 r)

-- | The 'ViaCartesian' type is designed to be used with `DerivingVia` to derive
-- `Associative` and `Symmetric` instances using the `Cartesian` operations.
newtype ViaCartesian k a b = ViaCartesian (a `k` b)
instance Category k => Category (ViaCartesian k) where
  type Obj' (ViaCartesian k) a = Obj k a
  id = ViaCartesian id
  ViaCartesian g . ViaCartesian f = ViaCartesian (g . f)

instance Cartesian p k => Monoidal p (ViaCartesian k) where
  f ### g = (f . exl) &&& (g . exr)
instance (RepresentableR r, CartesianR r p k) => MonoidalR r p (ViaCartesian k) where
  rmap fs = fork (liftR2 (.) fs exs)
deriving instance Cartesian p k => Cartesian p (ViaCartesian k)
deriving instance (CartesianR r p k, RepresentableR r) => CartesianR r p (ViaCartesian k)

instance Cartesian p k => Associative p (ViaCartesian k) where
  lassoc = second exl &&& (exr . exr)
  rassoc = (exl . exl) &&& first  exr
instance Cartesian p k => Symmetric p (ViaCartesian k) where
  swap = exr &&& exl

-- | The 'ViaCocartesian' type is designed to be used with `DerivingVia` to derive
-- `Associative` and `Symmetric` instances using the `Cocartesian` operations.
newtype ViaCocartesian k a b = ViaCocartesian (a `k` b)
instance Category k => Category (ViaCocartesian k) where
  type Obj' (ViaCocartesian k) a = Obj k a
  id = ViaCocartesian id
  ViaCocartesian g . ViaCocartesian f = ViaCocartesian (g . f)
instance Cocartesian co k => Monoidal co (ViaCocartesian k) where
  f ### g = (inl . f) ||| (inr . g)
instance (CocartesianR r p k, RepresentableR r) => MonoidalR r p (ViaCocartesian k) where
  rmap fs = join (liftR2 (.) ins fs)
deriving instance Cocartesian co k => Cocartesian co (ViaCocartesian k)
deriving instance (CocartesianR r p k, RepresentableR r) => CocartesianR r p (ViaCocartesian k)

instance Cocartesian co k => Associative co (ViaCocartesian k) where
  lassoc = inl.inl ||| (inl.inr ||| inr)
  rassoc = (inl ||| inr.inl) ||| inr.inr
instance Cocartesian co k => Symmetric co (ViaCocartesian k) where
  swap = inr ||| inl

-------------------------------------------------------------------------------
-- | Function instances
-------------------------------------------------------------------------------

instance Category (->) where
  id = P.id
  (.) = (P..)

instance Cartesian (:*) (->) where
  exl = fst
  exr = snd
  dup = \ a -> (a,a)

instance Cocartesian (:+) (->) where
  inl = P.Left
  inr = P.Right
  jam = id `either` id
  -- Equivalently,
  -- jam (Left  a) = a
  -- jam (Right a) = a

instance Closed (->) (->) where (h ^^^ f) g = h . g . f

instance MonoidalClosed (:*) (->) (->) where
  curry   = P.curry
  uncurry = P.uncurry

deriving via (ViaCartesian   (->)) instance Associative (:*) (->)
deriving via (ViaCartesian   (->)) instance Symmetric   (:*) (->)
deriving via (ViaCocartesian (->)) instance Associative (:+) (->)
deriving via (ViaCocartesian (->)) instance Symmetric   (:+) (->)

instance RepresentableR r => CartesianR r Ap (->) where
  exs = tabulate (flip index)
  dups = pureRep

data RepAnd r x = RepAnd (Rep r) x

instance RepresentableR r => CocartesianR r RepAnd (->) where
  ins = tabulate RepAnd
  jams (RepAnd _ a) = a

deriving via (ViaCartesian   (->)) instance Monoidal    (:*) (->)
deriving via (ViaCocartesian (->)) instance Monoidal    (:+) (->)

deriving via (ViaCartesian   (->))
  instance RepresentableR r => MonoidalR r Ap (->)
deriving via (ViaCocartesian (->))
  instance RepresentableR r => MonoidalR r RepAnd (->)

-------------------------------------------------------------------------------
-- | Pattern synonyms
-------------------------------------------------------------------------------

#if 0

-- GHC error:
--
--   A type signature must be provided for a set of polymorphic pattern synonyms.
--   In {-# COMPLETE :& #-}
--
-- See discussion https://github.com/conal/linalg/pull/54. This situation might
-- improve: http://mail.haskell.org/pipermail/ghc-devs/2020-August/019190.
-- Meanwhile, specialize these definitions for each representation.

pattern (:&) :: (Cartesian p k, Obj3 k a c d)
             => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
pattern f :& g <- (unfork2 -> (f,g)) where (:&) = (&&&)
{-# COMPLETE (:&) #-}

pattern (:|) :: (Cocartesian co k, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
{-# COMPLETE (:|) #-}

pattern Fork :: (CartesianR h p k, Obj2 k f g) => h (k f g) -> k f (p h g)
pattern Fork ms <- (unfork -> ms) where Fork = fork
{-# COMPLETE Fork #-}

pattern Join :: (CocartesianR h p k, Obj2 k f g) => h (k f g) -> k (p h f) g
pattern Join ms <- (unjoin -> ms) where Join = join
{-# COMPLETE Join #-}

#endif
