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


newtype ComposeHKT' hkt1 hkt2 f_g x
  = ComposeHKT' { unComposeHKT' :: ComposeHKT hkt1 hkt2 f_g x }
  deriving stock (Generic)


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
    {-# INLINE fromHKT #-}
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
    ( Functor f
    , IsHKT' (hkt1 f (HKT (hkt2 g x)))
    , IsHKT' (hkt2 g x)
    , ToHKT hkt1 f (HKT (hkt2 g x))
    , ToHKT hkt2 g x
    )
  =>
    ToHKT (ComposeHKT' hkt1 hkt2) (Compose f g) x
  where
    {-# INLINE toHKT #-}
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
    ( FromHKT (ComposeHKT' hkt1 hkt2) (Compose f g) x
    , ToHKT (ComposeHKT' hkt1 hkt2) (Compose f g) x
    )
  =>
    IsHKT' (ComposeHKT' hkt1 hkt2 (Compose f g) x)


instance
    ( Functor f
    , IsHKT (ComposeHKT' hkt1 hkt2) f
    )
  =>
    Functor (ComposeHKT' hkt1 hkt2 f)
  where
    {-# INLINE fmap #-}
    fmap f = HKT . fmap f . unHKT
