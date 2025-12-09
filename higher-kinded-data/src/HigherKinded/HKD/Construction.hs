{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Construction and deconstruction of HKD values.
--
-- This module provides utilities for converting between regular data types
-- and their HKD representations, particularly useful when working with
-- applicative functors.
--
-- Based on 'Data.Generic.HKD.Construction from package 'higgledy'
-- by Tom Harding ((c) Tom Harding, 2019, MIT)
--
-- ==== __Examples__
--
-- @
-- data Person = Person { name :: String, age :: Int } deriving Generic
--
-- -- Convert from HKD to regular value
-- fromHKDPerson :: HKD Person Applied Identity -> Identity Person
-- fromHKDPerson = fromHKD
--
-- -- Convert from regular value to HKD
-- toHKDPerson :: Identity Person -> HKD Person Applied Identity
-- toHKDPerson = toHKD
-- @
module HigherKinded.HKD.Construction where

import Data.Kind
import GHC.Generics

import HigherKinded.HKT
import HigherKinded.HKT.Applied

import HigherKinded.HKD.Generic



-- | Class for constructing and deconstructing HKD values.
--
-- This class provides bidirectional conversion between HKD representations
-- and regular values wrapped in a functor.
--
-- @hkd@ - The HKD type constructor
-- @structure@ - The underlying structure type
-- @hkt@ - The HKT transformer
-- @f@ - The functor to use for wrapping
class ConstructHKD (hkd :: (Type -> Type) -> Type) (structure :: Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) where
  -- | Convert from an HKD representation to a wrapped structure.
  fromHKD :: hkd f -> f structure
  -- | Convert from a wrapped structure to an HKD representation.
  toHKD :: f structure -> hkd f

instance {-# OVERLAPPABLE #-} GConstructHKD hkd structure hkt f => ConstructHKD hkd structure hkt f where
  {-# INLINABLE fromHKD #-}
  fromHKD = fmap to . gFromHKD @(Rep structure) @hkt @f . from

  {-# INLINABLE toHKD #-}
  toHKD = to . gToHKD @(Rep structure) @hkt @f . fmap from

class
    ( Applicative f
    , Generic structure
    , GConstructHKDRep (Rep structure) hkt f
    , Generic (hkd f)
    , Rep (hkd f) ~ GHKD_ (Rep structure) hkt f
    )
  => GConstructHKD hkd structure hkt f

instance
    ( Applicative f
    , Generic structure
    , GConstructHKDRep (Rep structure) hkt f
    , Generic (hkd f)
    , Rep (hkd f) ~ GHKD_ (Rep structure) hkt f
    )
  => GConstructHKD hkd structure hkt f

pattern HKD
  :: forall hkd structure hkt f.
     ConstructHKD hkd structure hkt f
  => f structure
  -> hkd f
pattern HKD unHKD <- (fromHKD @hkd @structure @hkt @f -> unHKD) where
  HKD x = toHKD @hkd @structure @hkt @f x



instance GConstructHKD (HKD structure hkt) structure hkt f => ConstructHKD (HKD structure hkt) structure hkt f where
  {-# INLINABLE fromHKD #-}
  fromHKD = fmap to . gFromHKD @(Rep structure) @hkt @f . unGHKD

  {-# INLINABLE toHKD #-}
  toHKD = GHKD . gToHKD @(Rep structure) @hkt @f . fmap from



class GConstructHKDRep (rep :: Type -> Type) (hkt :: ((Type -> Type) -> Type -> Type)) (f :: Type -> Type) where
  gFromHKD :: GHKD_ rep hkt f () -> f (rep ())
  gToHKD :: f (rep ()) -> GHKD_ rep hkt f ()

instance
    ( Functor f
    , GConstructHKDRep inner hkt f
    )
  =>
    GConstructHKDRep (M1 index meta inner) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD = fmap M1 . gFromHKD @inner @hkt @f . unM1

    {-# INLINABLE gToHKD #-}
    gToHKD = M1 . gToHKD @inner @hkt @f . fmap unM1

instance
    ( Applicative f
    , GConstructHKDRep left hkt f
    , GConstructHKDRep right hkt f
    )
  =>
    GConstructHKDRep (left :*: right) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD (l :*: r) = (:*:) <$> gFromHKD @left @hkt @f l <*> gFromHKD @right @hkt @f r

    {-# INLINABLE gToHKD #-}
    gToHKD lr = gToHKD @left @hkt @f ((\(l :*: _) -> l) <$> lr) :*: gToHKD @right @hkt @f ((\(_ :*: r) -> r) <$> lr)

instance
    ( Functor f
    , ConstructHKD (HKD subHKD hkt) subHKD hkt f
    , GHKD_ (K1 index (NestedHKD subHKD)) hkt f ~ K1 index (HKD subHKD hkt f)
    )
  =>
    GConstructHKDRep (K1 index (NestedHKD subHKD)) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD = fmap (K1 . NestedHKD) . fromHKD @(HKD subHKD hkt) @subHKD @hkt @f . unK1

    {-# INLINABLE gToHKD #-}
    gToHKD = K1 . toHKD @(HKD subHKD hkt) @subHKD @hkt @f . fmap (unNestedHKD . unK1)

instance
    ( Functor f
    , Functor t
    , subHKD' ~ HKD subHKD Applied t
    , ConstructHKD (HKD subHKD Applied) subHKD Applied t
    , ConstructHKD (HKD subHKD' hkt) subHKD' hkt f
    , GHKD_ (K1 index (t (NestedHKD subHKD))) hkt f ~ K1 index (HKD subHKD' hkt f)
    )
  =>
    GConstructHKDRep (K1 index (t (NestedHKD subHKD))) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD =
        fmap (K1 . fmap NestedHKD)
      . fmap (fromHKD @(HKD subHKD Applied) @subHKD @Applied @t)
      . fromHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . unK1

    {-# INLINABLE gToHKD #-}
    gToHKD =
        K1
      . toHKD @(HKD subHKD' hkt) @subHKD' @hkt @f
      . fmap (toHKD @(HKD subHKD Applied) @subHKD @Applied @t)
      . fmap (fmap unNestedHKD . unK1)

instance
    ( Functor f
    , GConstructHKDRep (K1 index (k $~> t)) hkt f
    , GHKD_ (K1 index (Applied k t)) hkt f ~ GHKD_ (K1 index (k $~> t)) hkt f
    )
  =>
    GConstructHKDRep (K1 index (Applied k t)) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD = fmap (K1 . Applied . unK1) . gFromHKD @(K1 index (k $~> t)) @hkt @f

    {-# INLINABLE gToHKD #-}
    gToHKD = gToHKD @(K1 index (k $~> t)) @hkt @f . fmap (K1 . unApplied . unK1)

instance {-# OVERLAPPABLE #-}
    ( Functor f
    , FromHKT hkt f inner
    , ToHKT hkt f inner
    , IsHKT' (hkt f inner)
    , GHKD_ (K1 index inner) hkt f ~ K1 index (HKT (hkt f inner))
    )
  =>
    GConstructHKDRep (K1 index inner) hkt f
  where
    {-# INLINABLE gFromHKD #-}
    gFromHKD = fmap K1 . fromHKT @hkt @f @inner . toHKT' . unK1

    {-# INLINABLE gToHKD #-}
    gToHKD = K1 . (fromHKT' . toHKT @hkt @f @inner) . fmap unK1
