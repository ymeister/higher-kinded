{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Database.Beam.HigherKinded
  ( module Database.Beam.HigherKinded
  , Columnar
  , Columnar'
  ) where

import Data.Functor.Identity
import Data.Kind
import Database.Beam.Schema.Tables as Beam
import GHC.Generics (Generic)

import HigherKinded.HKT
import HigherKinded.HKD



--
-- | Beamed
--

type Beamed structure = HKD structure Beam'

pattern Beamed
  :: forall structure f.
     ConstructHKD (Beamed structure) structure Beam' f
  => f structure
  -> Beamed structure f
pattern Beamed { unBeamed } <- (fromHKD @(Beamed structure) @structure @Beam' @f -> unBeamed) where
  Beamed x = toHKD @(Beamed structure) @structure @Beam' @f x


#if MIN_VERSION_beam_core(0,10,3)
instance BeamableHKD structure Beam' => Beamable (Beamed structure)

class
    ( GTableSkeleton (HKD_ structure Beam' Ignored)
    , forall f g h. GZipTablesHKD structure Beam' f g h
    )
  => BeamableHKD structure hkt

instance
    ( GTableSkeleton (HKD_ structure Beam' Ignored)
    , forall f g h. GZipTablesHKD structure Beam' f g h
    )
  => BeamableHKD structure hkt

class
    ( GZipTables f g h
        (HKD_ structure hkt Beam.Exposed)
        (HKD_ structure hkt f)
        (HKD_ structure hkt g)
        (HKD_ structure hkt h)
    , GenericHKD_ structure hkt f
    , GenericHKD_ structure hkt g
    , GenericHKD_ structure hkt h
    )
  => GZipTablesHKD structure hkt f g h

instance
    ( GZipTables f g h
        (HKD_ structure hkt Beam.Exposed)
        (HKD_ structure hkt f)
        (HKD_ structure hkt g)
        (HKD_ structure hkt h)
    , GenericHKD_ structure hkt f
    , GenericHKD_ structure hkt g
    , GenericHKD_ structure hkt h
    )
  => GZipTablesHKD structure hkt f g h
#endif



bitraverseBeamed
  :: forall structure f g h t.
     ( Applicative t
     , BiTraversableHKD (Beamed structure) Beam' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> Beamed structure f
  -> Beamed structure g
  -> t (Beamed structure h)
bitraverseBeamed = bitraverseBeam @(Beamed structure) @f @g @h

zipBeamed
  :: forall structure f g h.
     ( ZippableHKD (Beamed structure) Beam' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> Beamed structure f
  -> Beamed structure g
  -> Beamed structure h
zipBeamed = zipBeam @(Beamed structure) @f @g @h

traverseBeamed
  :: forall structure f g t.
     ( Applicative t
     , TraversableHKD (Beamed structure) Beam' f g
     )
  => (forall x. f x -> t (g x))
  -> Beamed structure f
  -> t (Beamed structure g)
traverseBeamed = traverseBeam @(Beamed structure) @f @g

mapBeamed
  :: forall structure f g.
     ( FunctorHKD (Beamed structure) Beam' f g
     )
  => (forall x. f x -> g x)
  -> Beamed structure f
  -> Beamed structure g
mapBeamed = mapBeam @(Beamed structure) @f @g

pureBeamed
  :: forall structure f.
     ( FunctorHKD (Beamed structure) Beam' f f
     )
  => (forall a. f a)
  -> Beamed structure f
pureBeamed = pureBeam @(Beamed structure) @f

--
-- | Beam
--

type Beam :: (Type -> Type) -> Type -> Type
type family Beam f a where
  Beam f a = Columnar f a

newtype Beam' f a = Beam' { unBeam' :: Beam f a }
  deriving stock (Generic)

--
-- | 'FromHKT' Beam'
--

instance {-# OVERLAPPABLE #-} (Beam f a ~ Columnar f a, FromHKT Columnar' f a) => FromHKT Beam' f a where
  {-# INLINE fromHKT #-}
  fromHKT = fromHKT @Columnar' @f @a . Columnar' . unBeam'

--
-- | 'ToHKT' Beam'
--

instance {-# OVERLAPPABLE #-} (Beam f a ~ Columnar f a, ToHKT Columnar' f a) => ToHKT Beam' f a where
  {-# INLINE toHKT #-}
  toHKT = Beam' . unColumnar' . toHKT @Columnar' @f @a

--
-- | IsHKT' Beam'
--

instance (FromHKT Beam' f a, ToHKT Beam' f a) => IsHKT' (Beam' f a)

--
-- | Beam wrappers
--

pattern Beam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f a
  -> f_a
pattern Beam { unBeam } <- (fromBeam @f @a -> unBeam) where
  Beam f_a = toBeam @f @a f_a

{-# INLINE fromBeam #-}
fromBeam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f_a
  -> f a
fromBeam = fromHK @Beam' @f @a

{-# INLINE toBeam #-}
toBeam
  :: forall f a f_a.
     ( f_a ~$ Beam' f a
     )
  => f a
  -> f_a
toBeam = toHK @Beam' @f @a

--
-- | Beam transformers
--

{-# INLINE fmapBeam #-}
fmapBeam
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ Beam' f x
     , f_y ~$ Beam' f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapBeam = fmapHK @Beam' @f @x @y

{-# INLINE hoistBeam #-}
hoistBeam
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ Beam' f x
     , g_x ~$ Beam' g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistBeam = hoistHK @Beam' @f @g @x

{-# INLINE transformBeam #-}
transformBeam
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ Beam' f x
     , g_y ~$ Beam' g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformBeam = transformHK @Beam' @f @g @x @y



bitraverseBeam
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Beam' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseBeam = bitraverseHKD @hkd @Beam' @f @g @h

zipBeam
  :: forall hkd f g h.
     ( ZippableHKD hkd Beam' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipBeam = zipHKD @hkd @Beam' @f @g @h

traverseBeam
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Beam' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseBeam = traverseHKD @hkd @Beam' @f @g

mapBeam
  :: forall hkd f g.
     ( FunctorHKD hkd Beam' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapBeam = mapHKD @hkd @Beam' @f @g

pureBeam
  :: forall hkd f.
     ( FunctorHKD hkd Beam' f f
     )
  => (forall a. f a)
  -> hkd f
pureBeam = pureHKD @hkd @Beam' @f



transformBeam'
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Beam' f g
     , f_hkd_f ~$ Beam' f (hkd f)
     , f_hkd_g ~$ Beam' f (hkd g)
     , g_hkd_g ~$ Beam' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformBeam' = transformHKD @hkd @Beam' @Beam' @f @g @f_hkd_f @f_hkd_g @g_hkd_g

--
-- | Columnar
--

deriving stock instance (Generic (Columnar' f a))

{-# INLINE unColumnar' #-}
unColumnar' :: Columnar' f a -> Columnar f a
unColumnar' (Columnar' x) = x

--
-- | 'FromHKT' Columnar'
--

instance FromHKT Columnar' Identity a where
  {-# INLINE fromHKT #-}
  fromHKT (Columnar' a) = Identity a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => FromHKT Columnar' f a where
  {-# INLINE fromHKT #-}
  fromHKT (Columnar' a) = a

--
-- | 'ToHKT' Columnar'
--

instance ToHKT Columnar' Identity a where
  {-# INLINE toHKT #-}
  toHKT (Identity a) = Columnar' a

instance {-# OVERLAPPABLE #-} (Columnar f a ~ f a) => ToHKT Columnar' f a where
  {-# INLINE toHKT #-}
  toHKT = Columnar'

--
-- | 'IsHKT'' Columnar'
--

instance (FromHKT Columnar' f a, ToHKT Columnar' f a) => IsHKT' (Columnar' f a)

--
-- | Basic Columnar' instances
--

instance
    ( Functor f
    , IsHKT Columnar' f
    )
  =>
    Functor (Columnar' f)
  where
    {-# INLINE fmap #-}
    fmap f = HKT . fmap f . unHKT


instance {-# OVERLAPPING #-}
    ( Beamable hkd
    , IsHKT Columnar' f
    , IsHKT Columnar' g
    , IsHKT Columnar' h
    )
  =>
    BiTraversableHKD hkd Columnar' f g h
  where
    bitraverseHKD combine f g =
      zipBeamFieldsM
        (\(f' :: Columnar' f x)
          (g' :: Columnar' g x)
        -> fmap HKT $ combine (unHKT f') (unHKT g')
        ) f g

instance {-# OVERLAPPING #-}
    ( Beamable hkd
    , IsHKT Columnar' f
    , IsHKT Columnar' g
    )
  =>
    TraversableHKD hkd Columnar' f g
  where
    traverseHKD f x =
      zipBeamFieldsM
        (\(x' :: Columnar' f x)
          _
        -> fmap HKT $ f (unHKT x')
        ) x x

--
-- | Columnar wrappers
--

pattern Columnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
pattern Columnar { unColumnar } <- (fromColumnar @f @a -> unColumnar) where
  Columnar f_a = toColumnar @f @a f_a

{-# INLINE fromColumnar #-}
fromColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f_a
  -> f a
fromColumnar = fromHK @Columnar' @f @a

{-# INLINE toColumnar #-}
toColumnar
  :: forall f a f_a.
     ( f_a ~$ Columnar' f a
     )
  => f a
  -> f_a
toColumnar = toHK @Columnar' @f @a

--
-- | Columnar transformers
--

{-# INLINE fmapColumnar #-}
fmapColumnar
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ Columnar' f x
     , f_y ~$ Columnar' f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapColumnar = fmapHK @Columnar' @f @x @y

{-# INLINE hoistColumnar #-}
hoistColumnar
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ Columnar' f x
     , g_x ~$ Columnar' g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistColumnar = hoistHK @Columnar' @f @g @x

{-# INLINE transformColumnar #-}
transformColumnar
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ Columnar' f x
     , g_y ~$ Columnar' g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformColumnar = transformHK @Columnar' @f @g @x @y



bitraverseColumnar
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Columnar' f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseColumnar = bitraverseHKD @hkd @Columnar' @f @g @h

zipColumnar
  :: forall hkd f g h.
     ( ZippableHKD hkd Columnar' f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipColumnar = zipHKD @hkd @Columnar' @f @g @h

traverseColumnar
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Columnar' f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseColumnar = traverseHKD @hkd @Columnar' @f @g

mapColumnar
  :: forall hkd f g.
     ( FunctorHKD hkd Columnar' f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapColumnar = mapHKD @hkd @Columnar' @f @g

pureColumnar
  :: forall hkd f.
     ( FunctorHKD hkd Columnar' f f
     )
  => (forall a. f a)
  -> hkd f
pureColumnar = pureHKD @hkd @Columnar' @f



transformColumnar'
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Columnar' f g
     , f_hkd_f ~$ Columnar' f (hkd f)
     , f_hkd_g ~$ Columnar' f (hkd g)
     , g_hkd_g ~$ Columnar' g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformColumnar' = transformHKD @hkd @Columnar' @Columnar' @f @g @f_hkd_f @f_hkd_g @g_hkd_g
