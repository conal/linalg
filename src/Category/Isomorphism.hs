-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Isomorphisms

module Category.Isomorphism where

import qualified GHC.Generics as G
import GHC.Exts (Coercible,coerce)
import Control.Newtype.Generics

import CatPrelude

-------------------------------------------------------------------------------
-- | Representation
-------------------------------------------------------------------------------

infix 0 :<->
-- | Isomorphism
data Iso k a b = (:<->) { isoFwd :: a `k` b, isoRev :: b `k` a }

-- | Inverse isomorphism
inv :: Iso k a b -> Iso k b a
inv (f :<-> f') = f' :<-> f

-- | Form an ivolution from a _self-inverse_ arrow.
involution :: (a `k` a) -> Iso k a a
involution f = f :<-> f

infix 0 <->
type (<->) = Iso (->)

-------------------------------------------------------------------------------
-- | As a category
-------------------------------------------------------------------------------

instance Category k => Category (Iso k) where
  type Obj' (Iso k) a = Obj k a
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')

instance Associative p k => Associative p (Iso k) where
  lassoc = lassoc :<-> rassoc
  rassoc = rassoc :<-> lassoc

instance Symmetric p k => Symmetric p (Iso k) where
  swap = swap :<-> swap

-- We cannot use the default definitions for Associative and Symmetric, because
-- Iso k is not cartesian.

instance Monoidal p k => Monoidal p (Iso k) where
  (f :<-> f') ### (g :<-> g') = (f ### g) :<-> (f' ### g')

#if 0
instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
#endif

instance Closed e k => Closed e (Iso k) where
  (p :<-> p') ^^^ (q :<-> q') = (p ^^^ q) :<-> (p' ^^^ q')

-- TODO: is there a MonoidalClosed instance? I don't think so.

-- TODO: n-ary products and coproducts

-------------------------------------------------------------------------------
-- | Utilities
-------------------------------------------------------------------------------

-- | Apply one isomorphism via another
via :: (Category k, Obj2 k a b) => Iso k b b -> Iso k a b -> Iso k a a
(g :<-> g') `via` (ab :<-> ba) = ba . g . ab :<-> ba . g' . ab

join2Iso :: (Cocartesian co k, Obj3 k a c d)
         => (c `k` a) :* (d `k` a) <-> ((c `co` d) `k` a)
join2Iso = join2 :<-> unjoin2

fork2Iso :: (Cartesian p k, Obj3 k a c d)
         => (a `k` c) :* (a `k` d) <-> (a `k` (c `p` d))
fork2Iso = fork2 :<-> unfork2

joinIso :: (CocartesianR r co k, Obj2 k a b) => r (a `k` b) <-> co r a `k` b
joinIso = join :<-> unjoin

forkIso :: (CartesianR r p k, Obj2 k a b) => r (a `k` b) <-> (a `k` p r b)
forkIso = fork :<-> unfork

curryIso :: (MonoidalClosed p e k, Obj3 k a b c) => ((a `p` b) `k` c) <-> (a `k` (b `e` c))
curryIso = curry :<-> uncurry

newIso :: Newtype a => a <-> O a
newIso = unpack :<-> pack

repIso :: Representable f => f a <-> (Rep f -> a)
repIso = index :<-> tabulate

coerceIso :: (Coercible a b, Coercible b a) => a <-> b
coerceIso = coerce :<-> coerce

genericIso :: G.Generic a => (a <-> G.Rep a x)
genericIso = G.from :<-> G.to

generic1Iso :: G.Generic1 f => (f <--> G.Rep1 f)
generic1Iso = G.from1 :<-> G.to1

-- | Natural isomorphism
infix 0 <-->
type f <--> g = forall a. f a <-> g a

fmapIso :: Functor f => a <-> b -> f a <-> f b
fmapIso (f :<-> g) = (fmap f :<-> fmap g)

flipIso :: (a -> b -> c) <-> (b -> a -> c)
flipIso = flip :<-> flip

distributeIso :: (Representable f, Representable g) => f (g a) <-> g (f a)
-- distributeIso = inv repIso . fmapIso (inv repIso) . flipIso . fmapIso repIso . repIso
distributeIso = distribute :<-> distribute

collectIso :: (Representable f, Representable g) => f a <-> b -> f (g a) <-> g b
collectIso f = fmapIso f . distributeIso
