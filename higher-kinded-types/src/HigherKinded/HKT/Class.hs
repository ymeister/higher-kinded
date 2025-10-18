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

module HigherKinded.HKT.Class
  (
  -- * Core
    IsHKT
  , FromHKT(..)
  , ToHKT(..)
  , pattern HKT
  , unHKT

  -- * HKT wrapping/unwrapping
  , type (~$)
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

--
-- | Core
--

class (forall x. ToHKT hkt f x, forall x. FromHKT hkt f x) => IsHKT hkt f
instance (forall x. ToHKT hkt f x, forall x. FromHKT hkt f x) => IsHKT hkt f

class FromHKT hkt f x where
  fromHKT :: hkt f x -> f x

class ToHKT hkt f x where
  toHKT :: f x -> hkt f x

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
  {-# INLINE fromHKT #-}
  fromHKT = undefined

instance ToHKT Void2 f x where
  {-# INLINE toHKT #-}
  toHKT = undefined

--

instance FromHKT Ap f x where
  {-# INLINE fromHKT #-}
  fromHKT = getAp

instance ToHKT Ap f x where
  {-# INLINE toHKT #-}
  toHKT = Ap

--
-- | HKT wrapping/unwrapping
--

class (IsHKT' hkt_f_x, f_x ~ HKT hkt_f_x) => (~$) f_x hkt_f_x
instance (IsHKT' hkt_f_x, f_x ~ HKT hkt_f_x) => (~$) f_x hkt_f_x

--

class (FromHKT' hkt_f_x, ToHKT' hkt_f_x) => IsHKT' hkt_f_x where
  type HKT hkt_f_x
  type HKT hkt_f_x = GHKT (Rep hkt_f_x)

  _HKT :: Iso' hkt_f_x (HKT hkt_f_x)

  {-# INLINE _HKT #-}
  default _HKT
    :: ( Generic hkt_f_x
       , GIsHKT' (Rep hkt_f_x)
       , HKT hkt_f_x ~ GHKT (Rep hkt_f_x)
       )
    => Iso' hkt_f_x (HKT hkt_f_x)
  _HKT = iso G.from G.to . _GHKT

type family FromHKT' hkt_f_x = r | r -> hkt_f_x where
  FromHKT' (hkt f x) = FromHKT hkt f x

type family ToHKT' hkt_f_x = r | r -> hkt_f_x where
  ToHKT' (hkt f x) = ToHKT hkt f x

{-# INLINE _UnHKT #-}
_UnHKT :: IsHKT' hkt_f_x => Iso' (HKT hkt_f_x) hkt_f_x
_UnHKT = from _HKT

{-# INLINE fromHKT' #-}
fromHKT' :: IsHKT' hkt_f_x => hkt_f_x -> HKT hkt_f_x
fromHKT' = view _HKT

{-# INLINE toHKT' #-}
toHKT' :: IsHKT' hkt_f_x => HKT hkt_f_x -> hkt_f_x
toHKT' = view _UnHKT

--

newtype HKT' hkt (f :: Type -> Type) x = HKT' { unHKT' :: HKT (hkt f x) }
  deriving stock (Generic)

instance (FromHKT hkt f x, IsHKT' (hkt f x)) => FromHKT (HKT' hkt) f x where
  {-# INLINE fromHKT #-}
  fromHKT = fromHKT @hkt @f @x . toHKT' @(hkt f x) . unHKT'

instance (ToHKT hkt f x, IsHKT' (hkt f x)) => ToHKT (HKT' hkt) f x where
  {-# INLINE toHKT #-}
  toHKT = HKT' . fromHKT' @(hkt f x) . toHKT @hkt @f @x

instance IsHKT' (hkt f x) => IsHKT' (HKT' hkt f x) where
  type HKT (HKT' hkt f x) = HKT (hkt f x)

  {-# INLINE _HKT #-}
  _HKT = iso (unHKT') (HKT')

instance
    ( Functor f
    , IsHKT (HKT' hkt) f
    )
  =>
    Functor (HKT' hkt f)
  where
    {-# INLINE fmap #-}
    fmap f = HKT . fmap f . unHKT

--
-- | Generic 'IsHKT'' instance
--

class GIsHKT' rep_hkt_f_x where
  type GHKT rep_hkt_f_x :: Type
  _GHKT :: Iso' (rep_hkt_f_x p) (GHKT rep_hkt_f_x)

instance GIsHKT' x => GIsHKT' (M1 i c x) where
  type GHKT (M1 i c x) = GHKT x

  {-# INLINE _GHKT #-}
  _GHKT = iso (unM1) (M1) . _GHKT

instance GIsHKT' (K1 i x) where
  type GHKT (K1 i x) = x

  {-# INLINE _GHKT #-}
  _GHKT = iso (unK1) (K1)

--
-- | Basic 'IsHKT'' instances
--

instance IsHKT' (Void2 (f :: Type -> Type) x) where
  type HKT (Void2 f x) = Void

  {-# INLINE _HKT #-}
  _HKT = undefined

instance IsHKT' (Ap f x)

--
-- | HK wrapping/unwrapping
--

pattern HK
  :: forall hkt f x f_x.
     ( f_x ~$ hkt f x
     )
  => f x
  -> f_x
pattern HK unHK <- (fromHK @hkt @f @x -> unHK) where
  HK unHK = toHK @hkt @f @x unHK

{-# INLINE fromHK #-}
fromHK
  :: forall hkt f x f_x.
     ( f_x ~$ hkt f x
     )
  => f_x
  -> f x
fromHK = unHKT @hkt @f @x . toHKT'

{-# INLINE toHK #-}
toHK
  :: forall hkt f x f_x.
     ( f_x ~$ hkt f x
     )
  => f x
  -> f_x
toHK = fromHKT' . HKT @hkt @f @x

--
-- | HK transformers
--

{-# INLINE fmapHK #-}
fmapHK
  :: forall hkt f x y f_x f_y.
     ( Functor f
     , f_x ~$ hkt f x
     , f_y ~$ hkt f y
     )
  => (x -> y)
  -> f_x
  -> f_y
fmapHK f = toHK @hkt . fmap @f f . fromHK @hkt

{-# INLINE hoistHK #-}
hoistHK
  :: forall (hkt :: (Type -> Type) -> Type -> Type) f g x f_x g_x.
     ( f_x ~$ hkt f x
     , g_x ~$ hkt g x
     )
  => (forall a. f a -> g a)
  -> f_x
  -> g_x
hoistHK f = toHK @hkt @g @x . f . fromHK @hkt @f @x

{-# INLINE transformHK #-}
transformHK
  :: forall (hkt :: (Type -> Type) -> Type -> Type) f g x y f_x g_y.
     ( f_x ~$ hkt f x
     , g_y ~$ hkt g y
     )
  => (f x -> g y)
  -> f_x
  -> g_y
transformHK f = toHK @hkt @g @y . f . fromHK @hkt @f @x

--
-- | HKT isomorphism
--

class (IsHKT hkt1 f, IsHKT hkt2 f, forall x. IsoHKT' hkt1 hkt2 f x) => IsoHKT hkt1 hkt2 f
instance (IsHKT hkt1 f, IsHKT hkt2 f, forall x. IsoHKT' hkt1 hkt2 f x) => IsoHKT hkt1 hkt2 f

class (IsHKT hkt1 f, IsHKT hkt2 f, forall f_x_1 f_x_2. (f_x_1 ~$ hkt1 f x, f_x_2 ~$ hkt2 f x) => f_x_1 ~ f_x_2) => IsoHKT' hkt1 hkt2 f x
instance (IsHKT hkt1 f, IsHKT hkt2 f, forall f_x_1 f_x_2. (f_x_1 ~$ hkt1 f x, f_x_2 ~$ hkt2 f x) => f_x_1 ~ f_x_2) => IsoHKT' hkt1 hkt2 f x

{-# INLINE isoHK #-}
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
