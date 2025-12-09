{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Composition of higher-kinded type transformers.
--
-- This module provides tools for composing multiple HKT transformers,
-- allowing you to build complex type transformations from simpler ones.
module HigherKinded.HKT.Compose
  ( -- * Type Families
    -- | Type-level composition of HKT transformers.
    ComposeHKT
  
    -- * Composition Wrapper
  , ComposeHKT'(..)
  ) where

import Data.Functor.Compose
import GHC.Generics

import HigherKinded.HKT.Class



-- | Type family for composing two HKT transformers.
--
-- This type family handles composition of HKT transformers, with special
-- cases for 'Compose' and '(:.:)' from "Data.Functor.Compose".
--
-- ==== __Examples__
--
-- @
-- -- Composing two HKT transformers with Compose
-- type MyComposition = ComposeHKT HKT1 HKT2 (Compose Maybe []) Int
-- -- Result: HKT (HKT1 Maybe (HKT (HKT2 [] Int)))
--
-- -- Default case for single functor
-- type SimpleHKT = ComposeHKT HKT1 HKT2 Maybe Int
-- -- Result: HKT (HKT1 Maybe Int)
-- @
type family ComposeHKT hkt1 hkt2 f_g x where
  ComposeHKT hkt1 hkt2 (Compose f g) x = HKT (hkt1 f (HKT (hkt2 g x)))
  ComposeHKT hkt1 hkt2 (f :.: g) x = HKT (hkt1 f (HKT (hkt2 g x)))
  ComposeHKT hkt1 _ f x = HKT (hkt1 f x)


-- | Newtype wrapper for HKT composition.
--
-- This wrapper provides instances for 'FromHKT' and 'ToHKT' that handle
-- the composition of two HKT transformers.
--
-- @hkt1@ - The outer HKT transformer
-- @hkt2@ - The inner HKT transformer  
-- @f_g@ - The composed functor (e.g., 'Compose f g')
-- @x@ - The element type
newtype ComposeHKT' hkt1 hkt2 f_g x
  = ComposeHKT' 
    { -- | Unwrap the composed HKT value.
      unComposeHKT' :: ComposeHKT hkt1 hkt2 f_g x 
    }
  deriving stock (Generic)

--
-- | 'FromHKT' instances
--

instance
    ( Functor (hkt1 f)
    , IsHKT' (hkt1 f (HKT (hkt2 g x)))
    , IsHKT' (hkt2 g x)
    , FromHKT hkt1 f (g x)
    , FromHKT hkt2 g x
    )
  =>
    FromHKT (ComposeHKT' hkt1 hkt2) (Compose f g) x
  where
    {-# INLINABLE fromHKT #-}
    fromHKT =
        Compose
      . fromHKT @hkt1 @f @(g x)
      . fmap
          ( fromHKT @hkt2 @g @x
          . toHKT' @(hkt2 g x)
          )
      . toHKT' @(hkt1 f (HKT (hkt2 g x)))
      . unComposeHKT'

instance
    ( Functor (hkt1 f)
    , IsHKT' (hkt1 f (HKT (hkt2 g x)))
    , IsHKT' (hkt2 g x)
    , FromHKT hkt1 f (g x)
    , FromHKT hkt2 g x
    )
  =>
    FromHKT (ComposeHKT' hkt1 hkt2) (f :.: g) x
  where
    {-# INLINABLE fromHKT #-}
    fromHKT =
        Comp1
      . fromHKT @hkt1 @f @(g x)
      . fmap
          ( fromHKT @hkt2 @g @x
          . toHKT' @(hkt2 g x)
          )
      . toHKT' @(hkt1 f (HKT (hkt2 g x)))
      . unComposeHKT'

instance {-# OVERLAPPABLE #-}
    ( ComposeHKT hkt1 hkt2 f x ~ HKT (hkt1 f x)
    , IsHKT' (hkt1 f x)
    )
  =>
    FromHKT (ComposeHKT' hkt1 hkt2) f x
  where
    {-# INLINABLE fromHKT #-}
    fromHKT = fromHKT @hkt1 @f @x . toHKT' @(hkt1 f x) . unComposeHKT'

--
-- | 'ToHKT' instances
--

instance
    ( Functor f
    , IsHKT' (hkt1 f (HKT (hkt2 g x)))
    , IsHKT' (hkt2 g x)
    , ToHKT hkt1 f (HKT (hkt2 g x))
    , ToHKT hkt2 g x
    )
  =>
    ToHKT (ComposeHKT' hkt1 hkt2) (Compose f g) x
  where
    {-# INLINABLE toHKT #-}
    toHKT =
        ComposeHKT'
      . fromHKT' @(hkt1 f (HKT (hkt2 g x)))
      . toHKT @hkt1 @f @(HKT (hkt2 g x))
      . fmap
          ( fromHKT' @(hkt2 g x)
          . toHKT @hkt2 @g @x
          )
      . getCompose

instance
    ( Functor f
    , IsHKT' (hkt1 f (HKT (hkt2 g x)))
    , IsHKT' (hkt2 g x)
    , ToHKT hkt1 f (HKT (hkt2 g x))
    , ToHKT hkt2 g x
    )
  =>
    ToHKT (ComposeHKT' hkt1 hkt2) (f :.: g) x
  where
    {-# INLINABLE toHKT #-}
    toHKT =
        ComposeHKT'
      . fromHKT' @(hkt1 f (HKT (hkt2 g x)))
      . toHKT @hkt1 @f @(HKT (hkt2 g x))
      . fmap
          ( fromHKT' @(hkt2 g x)
          . toHKT @hkt2 @g @x
          )
      . unComp1

instance {-# OVERLAPPABLE #-}
    ( ComposeHKT hkt1 hkt2 f x ~ HKT (hkt1 f x)
    , IsHKT' (hkt1 f x)
    )
  =>
    ToHKT (ComposeHKT' hkt1 hkt2) f x
  where
    {-# INLINABLE toHKT #-}
    toHKT = ComposeHKT' . fromHKT' @(hkt1 f x) . toHKT @hkt1 @f @x

--
-- | 'IsHKT'' instance
--

instance
    ( FromHKT (ComposeHKT' hkt1 hkt2) f_g x
    , ToHKT (ComposeHKT' hkt1 hkt2) f_g x
    )
  =>
    IsHKT' (ComposeHKT' hkt1 hkt2 f_g x)

--
-- | Basic instances
--

instance
    ( Functor f
    , IsHKT (ComposeHKT' hkt1 hkt2) f
    )
  =>
    Functor (ComposeHKT' hkt1 hkt2 f)
  where
    {-# INLINABLE fmap #-}
    fmap f = HKT . fmap f . unHKT
