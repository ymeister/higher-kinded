{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Applied higher-kinded types.
--
-- This module provides tools for working with applied type constructors,
-- allowing type-level application of functors to their arguments.
module HigherKinded.HKT.Applied
  ( -- * Type-Level Application
    -- | Type family for applying functors at the type level.
    type ($~>)
  , Apply

    -- * Applied Type Wrapper
  , Applied(..)
  , type (:$~>)

    -- * Pattern Synonyms and Conversions
  , pattern App
  , unApp
  , fromApp
  , toApp
  
    -- * Transformations
  , fmapApp
  , hoistApp
  , transformApp
  ) where

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Kind
import Data.Monoid (Ap(..))
import GHC.Generics

import HigherKinded.HKT



-- | Type family for type-level application of functors.
--
-- This type family reduces nested type constructors to their applied forms.
-- It handles special cases for common functors from base and this library.
--
-- ==== __Examples__
--
-- @
-- type R1 = Identity $~> Int        -- Result: Int
-- type R2 = Const String $~> Int    -- Result: String
-- type R3 = (Maybe :.: []) $~> Int  -- Result: Maybe $~> ([] $~> Int)
-- @
infixr 0 $~>
type ($~>) :: (k1 -> k2) -> k1 -> k3
type family ($~>) f x where
  ($~>) Identity x = x
  --
  ($~>) (Ap f) x = f $~> x
  ($~>) (Compose f g) x = f $~> (g $~> x)
  ($~>) (f :.: g) x = f $~> (g $~> x)
  ($~>) (Const x) _ = x
  ($~>) (Op x) y = y -> x
  --
  ($~>) (Applied f) x = f $~> x
  ($~>) (HKT' hkt f) x = HKT (hkt f x)
  ($~>) (ComposeHKT' hkt1 hkt2 (Compose f g)) x = ComposeHKT hkt1 hkt2 (Compose f g) x
  --
  ($~>) f x = f x

-- | Type synonym for the application operator.
--
-- This is a more descriptive alias for @($~>)@.
type Apply f x = f $~> x


-- | Newtype wrapper for applied functors.
--
-- This wrapper provides a uniform interface for working with
-- type-level applied functors.
newtype Applied f x = Applied 
  { -- | Unwrap an applied functor value.
    unApplied :: f $~> x 
  }
  deriving stock (Generic)

-- | Infix type synonym for 'Applied'.
--
-- Allows writing @f :$~> x@ instead of @Applied f x@.
type (:$~>) = Applied

--
-- | FromHKT instances
--

instance FromHKT Applied Identity x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Identity x

--

instance (FromHKT Applied f x) => FromHKT Applied (Ap f) x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Ap $ (fromHKT @Applied @f @x . Applied) $ x

instance (Functor f, FromHKT Applied f (g $~> x), FromHKT Applied g x) => FromHKT Applied (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Compose $ fmap (fromHKT . Applied) $ (fromHKT . Applied) $ x

instance (Functor f, FromHKT Applied f (g $~> x), FromHKT Applied g x) => FromHKT Applied ((f :: Type -> Type) :.: (g :: Type -> Type)) x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Comp1 $ fmap (fromHKT . Applied) $ (fromHKT . Applied) $ x

instance FromHKT Applied (Const x) a where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Const x

instance FromHKT Applied (Op x) y where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Op x

--

instance FromHKT Applied (Applied f) x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = Applied x

instance
    ( (HKT' hkt f $~> x) ~ HKT (hkt f x)
    )
  =>
    FromHKT Applied (HKT' hkt f) x
  where
    {-# INLINABLE fromHKT #-}
    fromHKT = HKT' . unApplied

instance
    ( (ComposeHKT' hkt1 hkt2 (Compose f g) $~> x) ~ ComposeHKT hkt1 hkt2 (Compose f g) x
    )
  =>
    FromHKT Applied (ComposeHKT' hkt1 hkt2 (Compose f g)) x
  where
    {-# INLINABLE fromHKT #-}
    fromHKT = ComposeHKT' . unApplied

--

instance {-# OVERLAPPABLE #-} ((f $~> x) ~ (f x)) => FromHKT Applied f x where
  {-# INLINABLE fromHKT #-}
  fromHKT (Applied x) = x

--
-- | 'ToHKT' instances
--

instance ToHKT Applied Identity x where
  {-# INLINABLE toHKT #-}
  toHKT (Identity x) = Applied x

--

instance (ToHKT Applied f x) => ToHKT Applied (Ap f) x where
  {-# INLINABLE toHKT #-}
  toHKT (Ap f_x) = Applied $ (unApplied . toHKT @Applied @f @x) $ f_x

instance (Functor f, ToHKT Applied f (g $~> x), ToHKT Applied g x) => ToHKT Applied (Compose (f :: Type -> Type) (g :: Type -> Type)) x where
  {-# INLINABLE toHKT #-}
  toHKT (Compose x) = Applied $ unApplied . toHKT $ fmap (unApplied . toHKT) x

instance (Functor f, ToHKT Applied f (g $~> x), ToHKT Applied g x) => ToHKT Applied ((f :: Type -> Type) :.: (g :: Type -> Type)) x where
  {-# INLINABLE toHKT #-}
  toHKT (Comp1 x) = Applied $ unApplied . toHKT $ fmap (unApplied . toHKT) x

instance ToHKT Applied (Const x) a where
  {-# INLINABLE toHKT #-}
  toHKT (Const x) = Applied x

instance ToHKT Applied (Op x) y where
  {-# INLINABLE toHKT #-}
  toHKT (Op x) = Applied x

--

instance ToHKT Applied (Applied f) x where
  {-# INLINABLE toHKT #-}
  toHKT (Applied x) = Applied x

instance
    ( (HKT' hkt f $~> x) ~ HKT (hkt f x)
    )
  =>
    ToHKT Applied (HKT' hkt f) x
  where
    {-# INLINABLE toHKT #-}
    toHKT = Applied . unHKT'

instance
    ( (ComposeHKT' hkt1 hkt2 (Compose f g) $~> x) ~ ComposeHKT hkt1 hkt2 (Compose f g) x
    )
  =>
    ToHKT Applied (ComposeHKT' hkt1 hkt2 (Compose f g)) x
  where
    {-# INLINABLE toHKT #-}
    toHKT = Applied . unComposeHKT'

--

instance {-# OVERLAPPABLE #-} ((f $~> x) ~ (f x)) => ToHKT Applied f x where
  {-# INLINABLE toHKT #-}
  toHKT = Applied

--
-- | 'IsHKT'' instance
--

instance (FromHKT Applied f x, ToHKT Applied f x) => IsHKT' (Applied f x)

--
-- | Basic instances
--

instance
    ( Functor f
    , IsHKT Applied f
    )
  =>
    Functor (Applied f)
  where
    {-# INLINABLE fmap #-}
    fmap f = HKT . fmap f . unHKT

--
-- | Wrappers
--

-- | Bidirectional pattern synonym for applied functors.
--
-- This pattern allows you to work with applied functors as if they
-- were regular data constructors.
--
-- ==== __Examples__
--
-- @
-- -- Pattern matching
-- processApp :: f_x ~$ (Maybe :$~> Int) => f_x -> Maybe Int
-- processApp (App mx) = mx
--
-- -- Construction
-- makeApp :: f_x ~$ (Maybe :$~> Int) => Maybe Int -> f_x
-- makeApp mx = App mx
-- @
pattern App
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~> x)
     )
  => f x
  -> f_x
pattern App { unApp } <- (fromApp @f @x -> unApp) where
  App f_x = toApp @f @x f_x

-- | Convert from an applied functor representation to the underlying functor.
{-# INLINABLE fromApp #-}
fromApp
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~> x)
     )
  => f_x
  -> f x
fromApp = fromHK @Applied @f @x

-- | Convert from a functor to its applied representation.
{-# INLINABLE toApp #-}
toApp
  :: forall (f :: Type -> Type) x f_x.
     ( f_x ~$ (f :$~> x)
     )
  => f x
  -> f_x
toApp = toHK @Applied @f @x

--
-- | Transformers
--

-- | Map a function over an applied functor.
--
-- This is 'fmap' lifted to work with applied functors.
{-# INLINABLE fmapApp #-}
fmapApp
  :: forall x y f f_x f_y.
     ( Functor f
     , f_x ~$ (f :$~> x)
     , f_y ~$ (f :$~> y)
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapApp = fmapHK @Applied @f @x @y

-- | Lift a natural transformation to work with applied functors.
--
-- This allows changing the underlying functor while preserving
-- the applied structure.
{-# INLINABLE hoistApp #-}
hoistApp
  :: forall
       x
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_x.
     ( f_x ~$ (f :$~> x)
     , g_x ~$ (g :$~> x)
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistApp = hoistHK @Applied @f @g @x

-- | Transform both the functor and element type of an applied functor.
--
-- This is the most general transformation for applied functors.
{-# INLINABLE transformApp #-}
transformApp
  :: forall
       x y
       (f :: Type -> Type)
       (g :: Type -> Type)
       f_x g_y.
     ( f_x ~$ (f :$~> x)
     , g_y ~$ (g :$~> y)
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformApp = transformHK @Applied @f @g @x @y
