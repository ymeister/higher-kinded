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

module HigherKinded.HKT.Compose
  ( ComposeHKT
  , ComposeHKT'(..)
  ) where

import Data.Functor.Compose
import GHC.Generics

import HigherKinded.HKT.Class



type family ComposeHKT hkt1 hkt2 f_g x where
  ComposeHKT hkt1 hkt2 (Compose f g) x = HKT (hkt1 f (HKT (hkt2 g x)))
  ComposeHKT hkt1 hkt2 (f :.: g) x = HKT (hkt1 f (HKT (hkt2 g x)))
  ComposeHKT hkt1 _ f x = HKT (hkt1 f x)


newtype ComposeHKT' hkt1 hkt2 f_g x
  = ComposeHKT' { unComposeHKT' :: ComposeHKT hkt1 hkt2 f_g x }
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
