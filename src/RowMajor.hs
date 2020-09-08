{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{- |
"Functor Matrices", or a "matrix" represented by a representable functor of
representable functors.
-}

module RowMajor where

import CatPrelude

import LinearFunction (LinearMap(..), Scalable(..), basis, dot, dot', dotIso)
import Category.Isomorphism


type V' a = (Foldable a, Representable a, Eq (Rep a))

class    V' a => V a
instance V' a => V a

type VR r = (V r, Representational1 r)

-- | Generalized matrices.
newtype L (s :: *) (f :: * -> *) (g :: * -> *) = L { unL :: g (f s) }
  deriving (Show, Generic)

instance Newtype (L s f g)
-- type O (L s f g) = g (f s)


instance LinearMap s (L s) where
  mu = inv newIso . distributeIso . fmapIso dotIso . newIso
  --                    L s f g
  -- newIso         ==> g (f s)
  -- fmapIso dotIso ==> g (f s -> s)
  -- distributeIso  ==> f s -> g s
  -- inv newIso     ==> F.L s f g

-- f (g s) ==> f s -> g s
-- I have (f s -> f s -> g s)

instance Category (L s) where
  type Obj' (L s) a = (Semiring s, V a)
  id = L basis
  (.) :: forall f g h. (Semiring s, C3 V f g h) => L s g h -> L s f g -> L s f h
  L b . L a
  -- Trying to prove:
  --  L b . L a = L $ fmap (flip fmap (distribute a) . dot) b
  -- which is synonymous with
  --  L b . L a = L $ flip cotraverse a . dot <$> b
  --
  -- Let's start from the definition as given by the isomorphism with linear maps.
  -- b . a = isoRev mu $ isoFwd mu b . isoFwd mu a
  -- = L $ fmap dot' $ distribute $ F.unL
  --   $ (F.L $ distribute $ fmap dot $ unL b)
  --   . (F.L $ distribute $ fmap dot $ unL a)
  --
  -- By definition of (.) on F.L
  -- = L $ fmap dot' $ distribute $ F.unL
  --   $ F.L $ (distribute $ fmap dot $ unL b)
  --         . (distribute $ fmap dot $ unL a)
  --
  -- F.unL . F.L = id
  -- = L $ fmap dot' $ distribute
  --     $ (distribute $ fmap dot $ unL b)
  --     . (distribute $ fmap dot $ unL a)
  --
  -- By definition of (.) and eta expansion
  -- = L $ fmap dot' $ distribute
  --     $ \x -> (distribute $ fmap dot $ unL b)
  --            ((distribute $ fmap dot $ unL a) x)
  --
  -- Recognize that (fmap dot $ unL b) :: h (g s -> s).
  -- Thus, `distribute (fmap dot $ unL b)` uses the `(e ->)` instance, which we unroll.
  -- Likewise with (distribute $ fmap dot $ unL a).
  -- = L $ fmap dot' $ distribute
  --     $ \x -> (\y -> fmap ($y) (fmap dot $ unL b))
  --            ((\z -> fmap ($z) (fmap dot $ unL a)) x)
  --
  -- fmap f (fmap g $ x) = fmap f . fmap g $ x, and
  -- fmap f . fmap g = fmap (f . g)
  -- = L $ fmap dot' $ distribute
  --     $ \x -> (\y -> fmap (flip dot y) (unL b))
  --            ((\z -> fmap (flip dot z) (unL a)) x)
  --
  -- Two rounds of eta reduction.
  -- = L $ fmap dot' $ distribute
  --     $ \x -> fmap (flip dot (fmap (flip dot x) (unL a))) (unL b)
  --
  -- flip dot == dot
   -- = L $ fmap (dot' @f) $ distribute @h @((->) (f s))
   --    $ \x -> fmap (dot @g (fmap (dot @f x) a)) b
  --
  -- pointfree
   = L $ fmap (dot' @f) $ distribute @h @((->) (f s))
      $ flip fmap b . dot @g . flip fmap a . dot @f
  --
  -- distribute (flip fmap y . f) ?= fmap (distribute f) y
   -- = L $ fmap (dot' @f) $ fmap
   --    (distribute (dot @g . flip fmap a . dot @f)) b
  --
  -- distribute the distribute by magic
   -- = L $ fmap (dot' @f) $ fmap
   --    (distribute (dot @f) . flip fmap (distribute a) . distribute (dot @g)) b
  --
  -- distribute dot == flip dot == dot
   -- = L $ fmap (dot' @f) $ fmap
   --    (dot @f . flip fmap (distribute a) . dot @g) b
  --
  -- combine fmap
   -- = L $ fmap (dot' @f . dot @f . flip fmap (distribute a) . dot @g) b
  --
  -- dot' . dot == id
   -- = L $ fmap (flip fmap (distribute a) . dot @g) b



-- Need to prove:
--     distribute (flip fmap b . dot . flip fmap a . dot)
--  == fmap (dot . flip fmap (distribute a) . dot) b

-- Perhaps by proving
--   distribute (flip fmap y . f) ?= fmap (distribute f) y
-- along with something about distributing distribute:
--   distribute (f . flip fmap a . g) ?= distribute g . flip fmap (distribute a) . distribute f

-- Is this true (and if so, useful)?
-- distribute (g . f) ?= fmap (. f) (distribute g)




instance (Representable f, Representable g, Semiring s) => Additive (L s f g) where
  zero = pureL zero
  (+)  = liftL2 (+)

pureL :: (Representable f, Representable g) => a -> L a f g
pureL = pack . pureRep . pureRep

liftL2 :: (Representable f, Representable g) => (a -> b -> c) -> L a f g -> L b f g -> L c f g
liftL2 = inNew2 . liftR2 . liftR2

scaleLIso :: s <-> L s Par1 Par1
scaleLIso = coerceIso

fork2LIso :: (L s a c :* L s a d) <-> L s a (c :*: d)
fork2LIso = inv newIso . inv newIso . (newIso ### newIso)

join2LIso :: (C3 Representable a c d) => (L s c a :* L s d a) <-> L s (c :*: d) a
join2LIso = inv newIso . distributeIso . inv newIso . (distributeIso . newIso ### distributeIso . newIso)

forkLIso :: RepresentableR r => r (L s a b) <-> L s a (r :.: b)
forkLIso = coerceIso

joinLIso :: (Representable b, RepresentableR r) => r (L s a b) <-> L s (r :.: a) b
joinLIso = inv newIso . collectIso (inv newIso) . coerceIso

instance Scalable s (L s) where
  scale   = isoFwd scaleLIso
  unscale = isoRev scaleLIso

instance Cartesian (:*:) (L s) where
  (&&&)   = curry $ isoFwd fork2LIso
  unfork2 = isoRev fork2LIso

pattern (:&) :: (Cartesian p k, Obj3 k a c d)
             => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
pattern f :& g <- (unfork2 -> (f,g)) where (:&) = (&&&)
{-# COMPLETE (:&) :: L #-}

instance Cocartesian (:*:) (L s) where
  (|||)   = curry $ isoFwd join2LIso
  unjoin2 = isoRev join2LIso

pattern (:|) :: (Cocartesian co k, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
{-# COMPLETE (:|) :: L #-}

instance VR r => CartesianR r (:.:) (L s) where
  fork   = isoFwd forkLIso
  unfork = isoRev forkLIso

pattern Fork :: (CartesianR h p k, Obj2 k f g) => h (k f g) -> k f (p h g)
pattern Fork ms <- (unfork -> ms) where Fork = fork
{-# COMPLETE Fork :: L #-}

instance VR r => CocartesianR r (:.:) (L s) where
  join   = isoFwd joinLIso
  unjoin = isoRev joinLIso

pattern Join :: (CocartesianR h p k, Obj2 k f g) => h (k f g) -> k (p h f) g
pattern Join ms <- (unjoin -> ms) where Join = join
{-# COMPLETE Join :: L #-}


instance Biproduct (:*:) (L s)
instance VR r => BiproductR r (:.:) (L s)

deriving via ViaCartesian (L s) instance Monoidal (:*:) (L s)

deriving via ViaCartesian (L s) instance VR r => MonoidalR r (:.:) (L s)


par1Iso :: Functor a => (a :.: Par1) <--> a
par1Iso = fmapIso newIso . newIso

par1IsoL :: (V f, Semiring s) => Iso (L s) (f :.: Par1) f
par1IsoL = L (isoRev par1Iso <$> basis) :<-> L (isoRev par1Iso basis)
