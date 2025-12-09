{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

-- | Core type classes and functions for higher-kinded type transformations.
--
-- This module provides the fundamental building blocks for working with
-- higher-kinded types, including conversion classes and pattern synonyms.
module HigherKinded.HKT.Class
  (
  -- * Core Type Classes
  -- | The core type classes for HKT conversions.
    IsHKT
  , FromHKT(..)
  , ToHKT(..)
  
  -- * Pattern Synonyms
  -- | Bidirectional pattern synonyms for convenient HKT manipulation.
  , pattern HKT
  , unHKT

  -- * HKT wrapping/unwrapping
  , type (~$)
  , type ($~)
  , IsHKT'(..)
  , FromHKT'
  , ToHKT'
  , _UnHKT
  , fromHKT'
  , toHKT'
  , HKT'(..)
  , GIsHKT'(..)

  -- * HK wrapping/unwrapping
  , pattern HK
  , fromHK
  , toHK

  -- * HK transformers
  , fmapHK
  , hoistHK
  , transformHK

  -- * HKT isomorphism
  , IsoHKT
  , IsoHKT'
  , isoHK
  ) where

import Control.Lens
import Data.Kind
import Data.Monoid (Ap(..))
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G

import HigherKinded.HKT.Internal.Void

-- * Core Type Classes

-- | Constraint synonym that ensures both 'ToHKT' and 'FromHKT' instances exist.
--
-- This class provides evidence that a type can be converted bidirectionally
-- between its HKT representation and its normal form.
class (forall x. ToHKT hkt f x, forall x. FromHKT hkt f x) => IsHKT hkt f
instance (forall x. ToHKT hkt f x, forall x. FromHKT hkt f x) => IsHKT hkt f

-- | Class for converting from an HKT representation to the underlying functor.
--
-- @hkt@ is the higher-kinded transformer
-- @f@ is the underlying functor
-- @x@ is the element type
class FromHKT (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (x :: Type) where
  -- | Convert from HKT representation to the underlying functor.
  fromHKT :: hkt f x -> f x

-- | Class for converting from a functor to its HKT representation.
--
-- @hkt@ is the higher-kinded transformer
-- @f@ is the underlying functor  
-- @x@ is the element type
class ToHKT (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (x :: Type) where
  -- | Convert from the underlying functor to HKT representation.
  toHKT :: f x -> hkt f x

-- | Bidirectional pattern synonym for HKT conversion.
--
-- This pattern allows you to pattern match on HKT values and construct them
-- as if they were regular data constructors.
--
-- ==== __Examples__
--
-- @
-- -- Pattern matching
-- processHKT :: IsHKT hkt f => hkt f x -> f x
-- processHKT (HKT fx) = fx
--
-- -- Construction
-- makeHKT :: IsHKT hkt f => f x -> hkt f x
-- makeHKT fx = HKT fx
-- @
pattern HKT
  :: forall hkt f x.
     ( FromHKT hkt f x
     , ToHKT hkt f x
     )
  => f x
  -> hkt f x
pattern HKT { unHKT } <- (fromHKT @hkt @f @x -> unHKT) where
  HKT = toHKT @hkt @f @x

--
-- | Basic 'FromHKT'/'ToHKT' instances
--

instance FromHKT Void2 f x where
  {-# INLINABLE fromHKT #-}
  fromHKT = undefined

instance ToHKT Void2 f x where
  {-# INLINABLE toHKT #-}
  toHKT = undefined

--

instance FromHKT Ap f x where
  {-# INLINABLE fromHKT #-}
  fromHKT = getAp

instance ToHKT Ap f x where
  {-# INLINABLE toHKT #-}
  toHKT = Ap

-- * HKT Wrapping and Unwrapping
-- | Functions and types for wrapping and unwrapping HKT values.

-- | Constraint that relates an HKT-wrapped type to its representation.
--
-- @f_x ~$ hkt_f_x@ means that @f_x@ is the HKT representation of @hkt_f_x@.
class (IsHKT' hkt_f_x, f_x ~ HKT hkt_f_x) => (~$) f_x hkt_f_x
instance (IsHKT' hkt_f_x, f_x ~ HKT hkt_f_x) => (~$) f_x hkt_f_x

-- | Type family for applying an HKT transformer to a type.
--
-- This operator allows type-level application of HKT transformers.
infixr 0 $~
type family ($~) hkt_f x where
  ($~) (hkt f) x = HKT (hkt f x)

--

-- | Type-level class for HKT wrapping operations.
--
-- This class provides an isomorphism between an HKT-wrapped type and its
-- underlying representation.
class (FromHKT' hkt_f_x, ToHKT' hkt_f_x) => IsHKT' (hkt_f_x :: Type) where
  -- | The underlying representation of the HKT-wrapped type.
  type HKT hkt_f_x
  type HKT hkt_f_x = GHKT (Rep hkt_f_x)

  -- | Isomorphism between the HKT-wrapped type and its representation.
  _HKT :: Iso' hkt_f_x (HKT hkt_f_x)

  {-# INLINABLE _HKT #-}
  default _HKT
    :: ( Generic hkt_f_x
       , GIsHKT' (Rep hkt_f_x)
       , HKT hkt_f_x ~ GHKT (Rep hkt_f_x)
       )
    => Iso' hkt_f_x (HKT hkt_f_x)
  _HKT = iso G.from G.to . _GHKT

-- | Type family that extracts the 'FromHKT' constraint from a type.
type family FromHKT' hkt_f_x = r | r -> hkt_f_x where
  FromHKT' (hkt f x) = FromHKT hkt f x

-- | Type family that extracts the 'ToHKT' constraint from a type.
type family ToHKT' hkt_f_x = r | r -> hkt_f_x where
  ToHKT' (hkt f x) = ToHKT hkt f x

-- | Isomorphism for unwrapping HKT values.
--
-- This is the inverse of '_HKT'.
{-# INLINABLE _UnHKT #-}
_UnHKT :: IsHKT' hkt_f_x => Iso' (HKT hkt_f_x) hkt_f_x
_UnHKT = from _HKT

-- | Convert from an HKT-wrapped type to its representation.
{-# INLINABLE fromHKT' #-}
fromHKT' :: IsHKT' hkt_f_x => hkt_f_x -> HKT hkt_f_x
fromHKT' = view _HKT

-- | Convert from a representation to its HKT-wrapped type.
{-# INLINABLE toHKT' #-}
toHKT' :: IsHKT' hkt_f_x => HKT hkt_f_x -> hkt_f_x
toHKT' = view _UnHKT

--

-- | Newtype wrapper for HKT values.
--
-- This wrapper helps with type inference and provides a uniform interface
-- for working with different HKT representations.
newtype HKT' (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (x :: Type)
  = HKT' { unHKT' :: HKT (hkt f x) }
  deriving stock (Generic)

instance (FromHKT hkt f x, IsHKT' (hkt f x)) => FromHKT (HKT' hkt) f x where
  {-# INLINABLE fromHKT #-}
  fromHKT = fromHKT @hkt @f @x . toHKT' @(hkt f x) . unHKT'

instance (ToHKT hkt f x, IsHKT' (hkt f x)) => ToHKT (HKT' hkt) f x where
  {-# INLINABLE toHKT #-}
  toHKT = HKT' . fromHKT' @(hkt f x) . toHKT @hkt @f @x

instance IsHKT' (hkt f x) => IsHKT' (HKT' hkt f x) where
  type HKT (HKT' hkt f x) = HKT (hkt f x)

  {-# INLINABLE _HKT #-}
  _HKT = iso (unHKT') (HKT')

instance
    ( Functor f
    , IsHKT (HKT' hkt) f
    )
  =>
    Functor (HKT' hkt f)
  where
    {-# INLINABLE fmap #-}
    fmap f = HKT . fmap f . unHKT

--
-- | Generic 'IsHKT'' instance
--

-- | Generic representation class for HKT wrapping.
--
-- This class is used internally to derive 'IsHKT'' instances
-- using GHC generics.
class GIsHKT' rep_hkt_f_x where
  -- | The HKT representation of the generic type.
  type GHKT rep_hkt_f_x :: Type
  -- | Isomorphism between the generic representation and its HKT form.
  _GHKT :: Iso' (rep_hkt_f_x p) (GHKT rep_hkt_f_x)

instance GIsHKT' x => GIsHKT' (M1 i c x) where
  type GHKT (M1 i c x) = GHKT x

  {-# INLINABLE _GHKT #-}
  _GHKT = iso (unM1) (M1) . _GHKT

instance GIsHKT' (K1 i x) where
  type GHKT (K1 i x) = x

  {-# INLINABLE _GHKT #-}
  _GHKT = iso (unK1) (K1)

--
-- | Basic 'IsHKT'' instances
--

instance IsHKT' (Void2 (f :: Type -> Type) (x :: Type)) where
  type HKT (Void2 f x) = Void

  {-# INLINABLE _HKT #-}
  _HKT = undefined

instance IsHKT' (Ap (f :: Type -> Type) (x :: Type))

-- * Higher-Kinded Wrapping
-- | Pattern synonyms and functions for working with higher-kinded values.

-- | Bidirectional pattern synonym for higher-kinded wrapping.
--
-- Similar to 'HKT' but works with the (~$) constraint for type-level
-- HKT applications.
pattern HK
  :: forall hkt (f :: Type -> Type) x f_x.
     ( f_x ~$ hkt f x
     )
  => f x
  -> f_x
pattern HK unHK <- (fromHK @hkt @f @x -> unHK) where
  HK unHK = toHK @hkt @f @x unHK

-- | Convert from a higher-kinded wrapped value to the underlying functor.
--
-- This is the extraction function for the 'HK' pattern.
{-# INLINABLE fromHK #-}
fromHK
  :: forall hkt (f :: Type -> Type) x f_x.
     ( f_x ~$ hkt f x
     )
  => f_x
  -> f x
fromHK = unHKT @hkt @f @x . toHKT'

-- | Convert from a functor to its higher-kinded wrapped representation.
--
-- This is the injection function for the 'HK' pattern.
{-# INLINABLE toHK #-}
toHK
  :: forall hkt (f :: Type -> Type) x f_x.
     ( f_x ~$ hkt f x
     )
  => f x
  -> f_x
toHK = fromHKT' . HKT @hkt @f @x

-- * Higher-Kinded Transformers
-- | Functions for transforming values wrapped in higher-kinded types.

-- | Map a function over a higher-kinded wrapped value.
--
-- This is like 'fmap' but works with HKT-wrapped functors.
--
-- @
-- fmapHK (+1) :: (Functor f, f_x ~$ hkt f Int, f_y ~$ hkt f Int)
--             => f_x -> f_y
-- @
{-# INLINABLE fmapHK #-}
fmapHK
  :: forall hkt (f :: Type -> Type) x y f_x f_y.
     ( Functor f
     , f_x ~$ hkt f x
     , f_y ~$ hkt f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapHK f = toHK @hkt . fmap @f f . fromHK @hkt

-- | Lift a natural transformation to work with HKT-wrapped values.
--
-- This allows you to change the underlying functor while preserving
-- the HKT wrapper.
--
-- @
-- hoistHK (fmap (*2)) :: (f_x ~$ hkt f Int, g_x ~$ hkt g Int)
--                     => f_x -> g_x
-- @
{-# INLINABLE hoistHK #-}
hoistHK
  :: forall (hkt :: (Type -> Type) -> Type -> Type) f g x f_x g_x.
     ( f_x ~$ hkt f x
     , g_x ~$ hkt g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistHK f = toHK @hkt @g @x . f . fromHK @hkt @f @x

-- | Transform both the functor and the element type of an HKT-wrapped value.
--
-- This is the most general transformation, allowing changes to both
-- the underlying functor and the element type.
{-# INLINABLE transformHK #-}
transformHK
  :: forall (hkt :: (Type -> Type) -> Type -> Type) f g x y f_x g_y.
     ( f_x ~$ hkt f x
     , g_y ~$ hkt g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformHK f = toHK @hkt @g @y . f . fromHK @hkt @f @x

-- * HKT Isomorphisms
-- | Type classes and functions for HKT isomorphisms.

-- | Class for HKT transformers that are isomorphic.
--
-- This class witnesses that two HKT transformers @hkt1@ and @hkt2@ are
-- isomorphic when applied to the same functor @f@.
class (IsHKT hkt1 f, IsHKT hkt2 f, forall x. IsoHKT' hkt1 hkt2 f x) => IsoHKT hkt1 hkt2 f
instance (IsHKT hkt1 f, IsHKT hkt2 f, forall x. IsoHKT' hkt1 hkt2 f x) => IsoHKT hkt1 hkt2 f

-- | Pointwise isomorphism constraint for HKT transformers.
--
-- This class provides evidence that two HKT transformers produce
-- the same type when applied to the same functor and element type.
class (IsHKT hkt1 f, IsHKT hkt2 f, forall f_x_1 f_x_2. (f_x_1 ~$ hkt1 f x, f_x_2 ~$ hkt2 f x) => f_x_1 ~ f_x_2) => IsoHKT' hkt1 hkt2 f x
instance (IsHKT hkt1 f, IsHKT hkt2 f, forall f_x_1 f_x_2. (f_x_1 ~$ hkt1 f x, f_x_2 ~$ hkt2 f x) => f_x_1 ~ f_x_2) => IsoHKT' hkt1 hkt2 f x

-- | Convert between isomorphic HKT representations.
--
-- When two HKT transformers are isomorphic, this function provides
-- the conversion between them.
{-# INLINABLE isoHK #-}
isoHK
  :: forall hkt1 (hkt2 :: (Type -> Type) -> Type -> Type) f x f_x_1 f_x_2.
     ( f_x_1 ~$ hkt1 f x
     , f_x_2 ~$ hkt2 f x
     )
  => f_x_1
  -> f_x_2
isoHK = toHK @hkt2 @f @x . fromHK @hkt1 @f @x

--
-- | Void 'IsoHKT'/'IsoHKT'' instances
--

instance (IsHKT hkt2 f, forall x. IsoHKT' Void2 hkt2 f x) => IsoHKT Void2 hkt2 f
instance (IsHKT hkt1 f, forall x. IsoHKT' hkt1 Void2 f x) => IsoHKT hkt1 Void2 f

instance (IsHKT hkt2 f, forall f_x_1 f_x_2. (f_x_1 ~$ Void2 f x, f_x_2 ~$ hkt2 f x) => f_x_1 ~ f_x_2) => IsoHKT' Void2 hkt2 f x
instance (IsHKT hkt1 f, forall f_x_1 f_x_2. (f_x_1 ~$ hkt1 f x, f_x_2 ~$ Void2 f x) => f_x_1 ~ f_x_2) => IsoHKT' hkt1 Void2 f x
