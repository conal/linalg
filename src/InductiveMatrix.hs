{-# LANGUAGE UndecidableInstances #-}

{- |
"Inductive matrices", as in "Type Your Matrices for Great Good: A Haskell
Library of Typed Matrices and Applications (Functional Pearl)" by Armando Santos
and José N Oliveira (Haskell Symposium 2020)
<https://github.com/bolt12/tymfgg-pearl>. The main differences:

- Representable functors rather than their index types (logarithms).
- Specified via denotational homomorphisms.
-}

module InductiveMatrix where

import CatPrelude

import qualified LinearFunction as F
import LinearFunction (Scalable(..),LinearMap(..))
import Category.Isomorphism

-------------------------------------------------------------------------------
-- | Representation and its denotation
-------------------------------------------------------------------------------

infixr 3 :&#
infixr 2 :|#

type V' a = (Representable a, Eq (Rep a))

class    V' a => V a
instance V' a => V a

type VR r = (V r, Representational1 r)

-- | Compositional linear map representation.
data L :: * -> (* -> *) -> (* -> *) -> * where
  Scale :: Semiring s => s -> L s Par1 Par1
  (:|#) :: (C3 V a b c, Additive s) => L s a c -> L s b c -> L s (a :*: b) c
  (:&#) :: C3 V a c k => L s a c -> L s a k -> L s a (c :*: k)
  JoinL :: (C2 V a b, VR r, Foldable r, Additive s)
        => r (L s a b) -> L s (r :.: a) b
  ForkL :: (C2 V a b, VR r) => r (L s a b) -> L s a (r :.: b)

instance LinearMap s (L s) where
  mu = fwd :<-> rev
   where
     fwd :: L s a b -> F.L s a b
     fwd (Scale s)  = scale s
     fwd (f :|# g)  = fwd f ||| fwd g
     fwd (f :&# g)  = fwd f &&& fwd g
     fwd (JoinL fs) = join (fwd <$> fs)
     fwd (ForkL fs) = fork (fwd <$> fs)
     rev = error "TODO: implement reverse mu on L"

-- TODO: rebuild this fwd definition by composing isomorphisms, eliminating the
-- explicit fwd/rev split. This fwd definition is already built from invertible
-- operations (including scale and fmap of an invertible operation). Dan's
-- failable patterns may be relevant. Can we do so without abstraction leak and
-- without building in a decomposition bias?

-- TODO: Generalize from F.L to all linear map representations. I guess we'll
-- need the intersection of Obj constraints. Or is there a single Obj that all
-- linear map representations can share (not just all _current_)? With careful
-- choice of primitives on all linear map representations, we can probably write
-- a single representation-polymorphic isomorphism that works for _all_ pairs of
-- representations (not just all current). On the other hand, we could instead
-- compose an isomorphism to F.L with an isomorphism from F.L to get the
-- representation-polymorphic isomorphism.

-------------------------------------------------------------------------------
-- | Instances (all deducible from denotational homomorphisms)
-------------------------------------------------------------------------------

instance (Representable f, Representable g, Semiring s) => Additive (L s f g) where
  zero = isoRev rowMajIso (pureRep (pureRep zero))
  Scale s   + Scale s' = Scale (s + s')
  (f :|# g) + (h :| k) = (f + h) :| (g + k)
  (f :&# g) + (h :& k) = (f + h) :& (g + k)
  ForkL fs  + Fork gs  = Fork (fs +^ gs)
  JoinL fs  + Join gs  = Join (fs +^ gs)

rowMajIso :: L s a b <-> b (a s)
rowMajIso = fwd :<-> rev
  where
    fwd :: L s a b -> b (a s)
    fwd (Scale s) = pureRep (pureRep s)
    fwd (f :|# g) = liftR2 (:*:) (fwd f) (fwd g)
    fwd (f :&# g) = fwd f :*: fwd g
    fwd (JoinL m) = cotraverse Comp1 $ fmap fwd m
    fwd (ForkL m) = Comp1 $ fmap fwd m
    rev :: b (a s) -> L s a b
    rev = undefined -- TODO: Write rev for toRowMajIso.

diagRep :: (Representable h, Eq (Rep h)) => a -> h a -> h (h a)
diagRep dflt as =
  tabulate (\ i -> tabulate (\ j -> if i == j then as `index` i else dflt))

instance Semiring s => Category (L s) where
  type Obj' (L s) a = V a
  id = isoRev rowMajIso (diagRep zero (pureRep one))
  Scale a   . Scale b   = Scale (a * b)           -- Scale denotation
  (p :&# q) . m         = p . m :&# q . m         -- binary product law
  m         . (p :|# q) = m . p :|# m . q         -- binary coproduct law
  (r :|# s) . (p :&# q) = r . p + s . q           -- biproduct law
  ForkL ms' . m         = ForkL (fmap (. m) ms')  -- n-ary product law
  m'        . JoinL ms  = JoinL (fmap (m' .) ms)  -- n-ary coproduct law
  JoinL ms' . ForkL ms  = sum (liftR2 (.) ms' ms) -- biproduct law

instance Semiring s => Cartesian (:*:) (L s) where
  (&&&) = (:&#)
  unfork2 (p :&# q)               = (p,q)
  unfork2 ((p :& q) :|# (r :& s)) = (p :|# r, q :|# s)
  unfork2 (JoinL ms)              = (JoinL ### JoinL) (unzip (unfork2 <$> ms))

instance Semiring s => Cocartesian (:*:) (L s) where
  (|||) = (:|#)
  unjoin2 (p :|# q)               = (p,q)
  unjoin2 ((p :| q) :&# (r :| s)) = (p :& r, q :& s)
  unjoin2 (ForkL fs)              = (ForkL ### ForkL) (unzip (unjoin2 <$> fs))

instance Semiring s => Biproduct (:*:) (L s)

instance (VR r, Semiring s) => CartesianR r (:.:) (L s) where
  fork = ForkL
  unfork (Fork fs :|# Fork gs) = liftR2 (:|#) fs gs
  unfork (ForkL fs)            = fs
  unfork (JoinL fs)            = JoinL <$> distribute (unfork <$> fs)

instance (VR r, Foldable r, Semiring s) => CocartesianR r (:.:) (L s) where
  join = JoinL
  unjoin (Join fs :&# Join gs) = liftR2 (:&#) fs gs
  unjoin (JoinL fs)            = fs
  unjoin (ForkL fs)            = fmap ForkL (distribute (fmap unjoin fs))

deriving via ViaCocartesian (L s) instance Semiring s => Monoidal (:*:) (L s)

deriving via ViaCartesian (L s)
  instance (VR r, Semiring s) => MonoidalR r (:.:) (L s)


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
