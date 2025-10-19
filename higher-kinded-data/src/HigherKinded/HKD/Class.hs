{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module HigherKinded.HKD.Class
  ( module HigherKinded.HKD.Class
  , FunctorB (..)
  , ApplicativeB (..)
  , TraversableB (..)
  , ConstraintsB (..)
  , Dict (..)
  ) where

import Barbies (ConstraintsB (..), FunctorB (..), ApplicativeB (..), TraversableB (..))
import Barbies.Constraints (Dict (..))
import Data.Coerce
import Data.Functor.Identity
import Data.Functor.Product (Product (..))
import Data.Kind
import Data.Proxy
import GHC.Generics hiding (from, to)
import GHC.Generics qualified as G

import HigherKinded.HKT

import HigherKinded.HKD.Internal.Exposed



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt Exposed
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , rep_exp ~ NormalHKDRep hkd hkt Exposed
          , rep_f' ~ NormalHKDRep hkd hkt f'
          , rep_g' ~ NormalHKDRep hkd hkt g'
          ) => GTraversableNormalHKDRep hkt f' g' rep_exp rep_f' rep_g'
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (h' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        (rep_h' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , IsNormalHKD hkd hkt h'
          , rep_exp ~ NormalHKDRep hkd hkt Exposed
          , rep_f' ~ NormalHKDRep hkd hkt f'
          , rep_g' ~ NormalHKDRep hkd hkt g'
          , rep_h' ~ NormalHKDRep hkd hkt h'
          ) => GBiTraversableNormalHKDRep hkt f' g' h' rep_exp rep_f' rep_g' rep_h'
    )
  => IsHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt Exposed
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , rep_exp ~ NormalHKDRep hkd hkt Exposed
          , rep_f' ~ NormalHKDRep hkd hkt f'
          , rep_g' ~ NormalHKDRep hkd hkt g'
          ) => GTraversableNormalHKDRep hkt f' g' rep_exp rep_f' rep_g'
    , forall
        (f' :: Type -> Type)
        (g' :: Type -> Type)
        (h' :: Type -> Type)
        (rep_exp :: Type -> Type)
        (rep_f' :: Type -> Type)
        (rep_g' :: Type -> Type)
        (rep_h' :: Type -> Type)
        . ( IsNormalHKD hkd hkt f'
          , IsNormalHKD hkd hkt g'
          , IsNormalHKD hkd hkt h'
          , rep_exp ~ NormalHKDRep hkd hkt Exposed
          , rep_f' ~ NormalHKDRep hkd hkt f'
          , rep_g' ~ NormalHKDRep hkd hkt g'
          , rep_h' ~ NormalHKDRep hkd hkt h'
          ) => GBiTraversableNormalHKDRep hkt f' g' h' rep_exp rep_f' rep_g' rep_h'
    )
  => IsHKD hkd hkt f

--------------------------------------------------------------------------------

newtype NormalHKD hkd hkt f x = NormalHKD
  { unNormalHKD :: NormalHKDRep hkd hkt f x
  }

type NormalHKDRep hkd hkt f = GNormalHKDRep hkt f (Rep (hkd Exposed)) (Rep (hkd f))

class
    ( Generic (hkd f)
    , Generic (hkd Exposed)
    , GIsNormalHKDRep hkt f (Rep (hkd Exposed)) (Rep (hkd f))
    )
  =>
    IsNormalHKD hkd hkt f
  where
    toNormalHKD :: hkd f -> NormalHKDRep hkd hkt f x
    fromNormalHKD :: NormalHKDRep hkd hkt f x -> hkd f

instance
    ( Generic (hkd f)
    , Generic (hkd Exposed)
    , GIsNormalHKDRep hkt f (Rep (hkd Exposed)) (Rep (hkd f))
    )
  =>
    IsNormalHKD hkd hkt f
  where
    {-# INLINABLE toNormalHKD #-}
    toNormalHKD hkd = gtoNormalHKDRep @hkt @f @(Rep (hkd Exposed)) @(Rep (hkd f)) $ G.from hkd

    {-# INLINABLE fromNormalHKD #-}
    fromNormalHKD hkd = G.to $ gfromNormalHKDRep @hkt @f @(Rep (hkd Exposed)) @(Rep (hkd f)) hkd



class GIsNormalHKDRep hkt f rep_exp rep where
  type GNormalHKDRep hkt f rep_exp rep :: Type -> Type

  gtoNormalHKDRep
    :: rep p
    -> GNormalHKDRep hkt f rep_exp rep p

  gfromNormalHKDRep
    :: GNormalHKDRep hkt f rep_exp rep p
    -> rep p

instance GIsNormalHKDRep hkt f V1 V1 where
  type GNormalHKDRep hkt f V1 V1 = V1

  {-# INLINABLE gtoNormalHKDRep #-}
  gtoNormalHKDRep _ = undefined

  {-# INLINABLE gfromNormalHKDRep #-}
  gfromNormalHKDRep _ = undefined

instance GIsNormalHKDRep hkt f U1 U1 where
  type GNormalHKDRep hkt f U1 U1 = U1

  {-# INLINABLE gtoNormalHKDRep #-}
  gtoNormalHKDRep _ = U1

  {-# INLINABLE gfromNormalHKDRep #-}
  gfromNormalHKDRep _ = U1

instance
    GIsNormalHKDRep hkt f rep_exp rep
  =>
    GIsNormalHKDRep hkt f (Rec1 rep_exp) (Rec1 rep)
  where
    type GNormalHKDRep hkt f (Rec1 rep_exp) (Rec1 rep) = Rec1 (GNormalHKDRep hkt f rep_exp rep)

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep (Rec1 rep) = Rec1 $ gtoNormalHKDRep @hkt @f @rep_exp @rep rep

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep (Rec1 rep) = Rec1 $ gfromNormalHKDRep @hkt @f @rep_exp @rep rep

instance
    GIsNormalHKDRep hkt f rep_exp rep
  =>
    GIsNormalHKDRep hkt f (M1 i c rep_exp) (M1 i c rep)
  where
    type GNormalHKDRep hkt f (M1 i c rep_exp) (M1 i c rep) = M1 i c (GNormalHKDRep hkt f rep_exp rep)

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep ~(M1 rep) = M1 $ gtoNormalHKDRep @hkt @f @rep_exp @rep rep

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep ~(M1 rep) = M1 $ gfromNormalHKDRep @hkt @f @rep_exp @rep rep

instance
    ( GIsNormalHKDRep hkt f rep_exp1 rep1
    , GIsNormalHKDRep hkt f rep_exp2 rep2
    )
  =>
    GIsNormalHKDRep hkt f (rep_exp1 :*: rep_exp2) (rep1 :*: rep2)
  where
    type GNormalHKDRep hkt f (rep_exp1 :*: rep_exp2) (rep1 :*: rep2) = GNormalHKDRep hkt f rep_exp1 rep1 :*: GNormalHKDRep hkt f rep_exp2 rep2

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep ~(rep1 :*: rep2) =
          gtoNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      :*: gtoNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep ~(rep1 :*: rep2) =
          gfromNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      :*: gfromNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

instance
    ( GIsNormalHKDRep hkt f rep_exp1 rep1
    , GIsNormalHKDRep hkt f rep_exp2 rep2
    )
  =>
    GIsNormalHKDRep hkt f (rep_exp1 :+: rep_exp2) (rep1 :+: rep2)
  where
    type GNormalHKDRep hkt f (rep_exp1 :+: rep_exp2) (rep1 :+: rep2) = GNormalHKDRep hkt f rep_exp1 rep1 :+: GNormalHKDRep hkt f rep_exp2 rep2

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep = \case
      L1 rep1 -> L1 $ gtoNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      R1 rep2 -> R1 $ gtoNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep = \case
      L1 rep1 -> L1 $ gfromNormalHKDRep @hkt @f @rep_exp1 @rep1 rep1
      R1 rep2 -> R1 $ gfromNormalHKDRep @hkt @f @rep_exp2 @rep2 rep2

instance
    ( f_x ~$ hkt f x
    )
  =>
    GIsNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f (K1 i (Exposed x)) (K1 i f_x)
  where
    type GNormalHKDRep hkt f (K1 i (Exposed x)) (K1 i f_x) = K1 i (f x)

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep ~(K1 f_x) = K1 $ fromHK @hkt @f @x f_x

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep ~(K1 f_x) = K1 $ toHK @hkt @f @x f_x

instance
    IsNormalHKD hkd hkt f
  =>
    GIsNormalHKDRep hkt f (K1 i (hkd Exposed)) (K1 i (hkd f))
  where
    type GNormalHKDRep hkt f (K1 i (hkd Exposed)) (K1 i (hkd f)) = K1 i (NormalHKD hkd hkt f ())

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep ~(K1 hkd) = K1 $ NormalHKD $ toNormalHKD @hkd @hkt @f hkd

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep ~(K1 ~(NormalHKD hkd)) = K1 $ fromNormalHKD @hkd @hkt @f hkd

instance
    IsNormalHKD hkd hkt (t f)
  =>
    GIsNormalHKDRep hkt f (K1 i (hkd (t Exposed))) (K1 i (hkd (t f)))
  where
    type GNormalHKDRep hkt f (K1 i (hkd (t Exposed))) (K1 i (hkd (t f))) = K1 i (NormalHKD hkd hkt (t f) ())

    {-# INLINABLE gtoNormalHKDRep #-}
    gtoNormalHKDRep ~(K1 hkd) = K1 $ NormalHKD $ toNormalHKD @hkd @hkt @(t f) hkd

    {-# INLINABLE gfromNormalHKDRep #-}
    gfromNormalHKDRep ~(K1 ~(NormalHKD hkd)) = K1 $ fromNormalHKD @hkd @hkt @(t f) hkd

--------------------------------------------------------------------------------

class
    IsoHKD
      (hkd1 :: (Type -> Type) -> Type)
      (hkd2 :: (Type -> Type) -> Type)
      (hkt1 :: (Type -> Type) -> Type -> Type)
      (hkt2 :: (Type -> Type) -> Type -> Type)
      (f :: Type -> Type)
  where
    isoHKD :: hkd1 f -> hkd2 f

    {-# INLINABLE isoHKD #-}
    default isoHKD
      :: ( IsNormalHKD hkd1 hkt1 f
         , IsNormalHKD hkd2 hkt2 f
         , NormalHKDRep hkd1 hkt1 f ~ NormalHKDRep hkd2 hkt2 f
         )
      => hkd1 f -> hkd2 f
    isoHKD = fromNormalHKD @hkd2 @hkt2 @f @() . toNormalHKD @hkd1 @hkt1 @f @()

instance {-# OVERLAPPABLE #-}
    ( IsNormalHKD hkd1 hkt1 f
    , IsNormalHKD hkd2 hkt2 f
    , NormalHKDRep hkd1 hkt1 f ~ NormalHKDRep hkd2 hkt2 f
    )
  => IsoHKD hkd1 hkd2 hkt1 hkt2 f

--------------------------------------------------------------------------------

{-# INLINABLE coerceHKD #-}
coerceHKD
  :: forall
       (hkd1 :: (Type -> Type) -> Type)
       (hkd2 :: (Type -> Type) -> Type)
       (hkt1 :: (Type -> Type) -> Type -> Type)
       (hkt2 :: (Type -> Type) -> Type -> Type)
       (f :: Type -> Type).
     ( IsNormalHKD hkd1 hkt1 f
     , IsNormalHKD hkd2 hkt2 f
     , Coercible
         (GNormalHKDRep hkt1 f (Rep (hkd1 Exposed)) (Rep (hkd1 f)) ())
         (GNormalHKDRep hkt2 f (Rep (hkd2 Exposed)) (Rep (hkd2 f)) ())
     )
  => hkd1 f -> hkd2 f
coerceHKD = fromNormalHKD @hkd2 @hkt2 @f @() . coerce . toNormalHKD @hkd1 @hkt1 @f @()

--------------------------------------------------------------------------------

class BiTraversableHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (g :: Type -> Type) (h :: Type -> Type) where
  bitraverseHKD
    :: Applicative t
    => (forall a. f a -> g a -> t (h a))
    -> hkd f
    -> hkd g
    -> t (hkd h)

  {-# INLINABLE bitraverseHKD #-}
  default bitraverseHKD
    :: ( Applicative t
       , GBiTraversableHKD hkd hkt f g h
       )
    => (forall a. f a -> g a -> t (h a))
    -> hkd f
    -> hkd g
    -> t (hkd h)
  bitraverseHKD combine (hkd_f :: hkd f) (hkd_g :: hkd g) =
    gbitraverseHKD @hkd @hkt @f @g @h combine hkd_f hkd_g

instance {-# OVERLAPPABLE #-} GBiTraversableHKD hkd hkt f g h => BiTraversableHKD hkd hkt f g h



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , IsNormalHKD hkd hkt h
    , GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g) (NormalHKDRep hkd hkt h)
    )
  =>
    GBiTraversableHKD hkd hkt f g h
  where
    gbitraverseHKD
      :: Applicative t
      => (forall a. f a -> g a -> t (h a))
      -> hkd f
      -> hkd g
      -> t (hkd h)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , IsNormalHKD hkd hkt h
    , GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g) (NormalHKDRep hkd hkt h)
    )
  =>
    GBiTraversableHKD hkd hkt f g h
  where
    {-# INLINABLE gbitraverseHKD #-}
    gbitraverseHKD combine (hkd_f :: hkd f) (hkd_g :: hkd g) =
          fromNormalHKD @hkd @hkt @h @()
      <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKDRep hkd hkt Exposed) @(NormalHKDRep hkd hkt f) @(NormalHKDRep hkd hkt g) @(NormalHKDRep hkd hkt h)
            combine
            (toNormalHKD @hkd @hkt @f @() hkd_f)
            (toNormalHKD @hkd @hkt @g @() hkd_g)



class GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h where
  gbitraverseNormalHKDRep
    :: Applicative t
    => (forall a. f a -> g a -> t (h a))
    -> rep_f p
    -> rep_g p
    -> t (rep_h p)

instance GBiTraversableNormalHKDRep hkt f g h V1 V1 V1 V1 where
  {-# INLINABLE gbitraverseNormalHKDRep #-}
  gbitraverseNormalHKDRep _ _ _ = pure undefined

instance GBiTraversableNormalHKDRep hkt f g h U1 U1 U1 U1 where
  {-# INLINABLE gbitraverseNormalHKDRep #-}
  gbitraverseNormalHKDRep _ _ _ = pure U1

instance
    GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h
  =>
    GBiTraversableNormalHKDRep hkt f g h (Rec1 rep_exp) (Rec1 rep_f) (Rec1 rep_g) (Rec1 rep_h)
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(Rec1 rep_f) ~(Rec1 rep_g) = Rec1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

instance
    GBiTraversableNormalHKDRep hkt f g h rep_exp rep_f rep_g rep_h
  =>
    GBiTraversableNormalHKDRep hkt f g h (M1 i c rep_exp) (M1 i c rep_f) (M1 i c rep_g) (M1 i c rep_h)
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(M1 rep_f) ~(M1 rep_g) = M1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp @rep_f @rep_g @rep_h combine rep_f rep_g

instance
    ( GBiTraversableNormalHKDRep hkt f g h rep_exp1 rep_f1 rep_g1 rep_h1
    , GBiTraversableNormalHKDRep hkt f g h rep_exp2 rep_f2 rep_g2 rep_h2
    )
  =>
    GBiTraversableNormalHKDRep hkt f g h (rep_exp1 :*: rep_exp2) (rep_f1 :*: rep_f2) (rep_g1 :*: rep_g2) (rep_h1 :*: rep_h2)
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(rep_f1 :*: rep_f2) ~(rep_g1 :*: rep_g2) =
      (:*:)
        <$> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp1 @rep_f1 @rep_g1 @rep_h1 combine rep_f1 rep_g1
        <*> gbitraverseNormalHKDRep @hkt @f @g @h @rep_exp2 @rep_f2 @rep_g2 @rep_h2 combine rep_f2 rep_g2

instance
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (K1 i (Exposed x)) (K1 i (f x)) (K1 i (g x)) (K1 i (h x))
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(K1 f_x) ~(K1 g_x) = K1 <$> combine f_x g_x

instance
    ( GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g) (NormalHKDRep hkd hkt h)
    )
  =>
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (K1 i (NormalHKD hkd hkt Exposed ())) (K1 i (NormalHKD hkd hkt f ())) (K1 i (NormalHKD hkd hkt g ())) (K1 i (NormalHKD hkd hkt h ()))
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(K1 hkd_f) ~(K1 hkd_g) =
      K1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKD hkd hkt Exposed) @(NormalHKD hkd hkt f) @(NormalHKD hkd hkt g) @(NormalHKD hkd hkt h) combine hkd_f hkd_g

instance
    ( GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g) (NormalHKDRep hkd hkt h)
    )
  =>
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (NormalHKD hkd hkt Exposed) (NormalHKD hkd hkt f) (NormalHKD hkd hkt g) (NormalHKD hkd hkt h)
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(NormalHKD hkd_f) ~(NormalHKD hkd_g) =
      NormalHKD <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKDRep hkd hkt Exposed) @(NormalHKDRep hkd hkt f) @(NormalHKDRep hkd hkt g) @(NormalHKDRep hkd hkt h) combine hkd_f hkd_g

instance
    ( GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt (t Exposed)) (NormalHKDRep hkd hkt (t f)) (NormalHKDRep hkd hkt (t g)) (NormalHKDRep hkd hkt (t h))
    )
  =>
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (K1 i (NormalHKD hkd hkt (t Exposed) ())) (K1 i (NormalHKD hkd hkt (t f) ())) (K1 i (NormalHKD hkd hkt (t g) ())) (K1 i (NormalHKD hkd hkt (t h) ()))
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(K1 hkd_f) ~(K1 hkd_g) =
      K1 <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKD hkd hkt (t Exposed)) @(NormalHKD hkd hkt (t f)) @(NormalHKD hkd hkt (t g)) @(NormalHKD hkd hkt (t h)) combine hkd_f hkd_g

instance
    ( GBiTraversableNormalHKDRep hkt f g h (NormalHKDRep hkd hkt (t Exposed)) (NormalHKDRep hkd hkt (t f)) (NormalHKDRep hkd hkt (t g)) (NormalHKDRep hkd hkt (t h))
    )
  =>
    GBiTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g h (NormalHKD hkd hkt (t Exposed)) (NormalHKD hkd hkt (t f)) (NormalHKD hkd hkt (t g)) (NormalHKD hkd hkt (t h))
  where
    {-# INLINABLE gbitraverseNormalHKDRep #-}
    gbitraverseNormalHKDRep combine ~(NormalHKD hkd_f) ~(NormalHKD hkd_g) =
      NormalHKD <$> gbitraverseNormalHKDRep @hkt @f @g @h @(NormalHKDRep hkd hkt (t Exposed)) @(NormalHKDRep hkd hkt (t f)) @(NormalHKDRep hkd hkt (t g)) @(NormalHKDRep hkd hkt (t h)) combine hkd_f hkd_g

--------------------------------------------------------------------------------

class TraversableHKD (hkd :: (Type -> Type) -> Type) (hkt :: (Type -> Type) -> Type -> Type) (f :: Type -> Type) (g :: Type -> Type) where
  traverseHKD
    :: Applicative t
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)

  {-# INLINABLE traverseHKD #-}
  default traverseHKD
    :: ( Applicative t
       , GTraversableHKD hkd hkt f g
       )
    => (forall a. f a -> t (g a))
    -> hkd f
    -> t (hkd g)
  traverseHKD = gtraverseHKD @hkd @hkt @f @g

instance {-# OVERLAPPABLE #-} GTraversableHKD hkd hkt f g => TraversableHKD hkd hkt f g



class
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g)
    )
  =>
    GTraversableHKD hkd hkt f g
  where
    gtraverseHKD
      :: Applicative t
      => (forall a. f a -> t (g a))
      -> hkd f
      -> t (hkd g)

instance
    ( IsNormalHKD hkd hkt f
    , IsNormalHKD hkd hkt g
    , GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g)
    )
  =>
    GTraversableHKD hkd hkt f g
  where
    {-# INLINABLE gtraverseHKD #-}
    gtraverseHKD f (hkd_f :: hkd f) =
          fromNormalHKD @hkd @hkt @g @()
      <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKDRep hkd hkt Exposed) @(NormalHKDRep hkd hkt f) @(NormalHKDRep hkd hkt g)
            f
            (toNormalHKD @hkd @hkt @f @() hkd_f)



class GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g where
  gtraverseNormalHKDRep
    :: Applicative t
    => (forall a. f a -> t (g a))
    -> rep_f p
    -> t (rep_g p)

instance GTraversableNormalHKDRep hkt f g V1 V1 V1 where
  {-# INLINABLE gtraverseNormalHKDRep #-}
  gtraverseNormalHKDRep _ _ = pure undefined

instance GTraversableNormalHKDRep hkt f g U1 U1 U1 where
  {-# INLINABLE gtraverseNormalHKDRep #-}
  gtraverseNormalHKDRep _ _ = pure U1

instance
    GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g
  =>
    GTraversableNormalHKDRep hkt f g (Rec1 rep_exp) (Rec1 rep_f) (Rec1 rep_g)
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(Rec1 rep_f) = Rec1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp @rep_f @rep_g f rep_f

instance
    GTraversableNormalHKDRep hkt f g rep_exp rep_f rep_g
  =>
    GTraversableNormalHKDRep hkt f g (M1 i c rep_exp) (M1 i c rep_f) (M1 i c rep_g)
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(M1 rep_f) = M1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp @rep_f @rep_g f rep_f

instance
    ( GTraversableNormalHKDRep hkt f g rep_exp1 rep_f1 rep_g1
    , GTraversableNormalHKDRep hkt f g rep_exp2 rep_f2 rep_g2
    )
  =>
    GTraversableNormalHKDRep hkt f g (rep_exp1 :*: rep_exp2) (rep_f1 :*: rep_f2) (rep_g1 :*: rep_g2)
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(rep_f1 :*: rep_f2) =
      (:*:)
        <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp1 @rep_f1 @rep_g1 f rep_f1
        <*> gtraverseNormalHKDRep @hkt @f @g @rep_exp2 @rep_f2 @rep_g2 f rep_f2

instance
    ( GTraversableNormalHKDRep hkt f g rep_exp1 rep_f1 rep_g1
    , GTraversableNormalHKDRep hkt f g rep_exp2 rep_f2 rep_g2
    )
  =>
    GTraversableNormalHKDRep hkt f g (rep_exp1 :+: rep_exp2) (rep_f1 :+: rep_f2) (rep_g1 :+: rep_g2)
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f = \case
      L1 rep_f -> L1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp1 @rep_f1 @rep_g1 f rep_f
      R1 rep_f -> R1 <$> gtraverseNormalHKDRep @hkt @f @g @rep_exp2 @rep_f2 @rep_g2 f rep_f

instance
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (K1 i (Exposed x)) (K1 i (f x)) (K1 i (g x))
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(K1 f_x) = K1 <$> f f_x

instance
    ( GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g)
    )
  =>
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (K1 i (NormalHKD hkd hkt Exposed ())) (K1 i (NormalHKD hkd hkt f ())) (K1 i (NormalHKD hkd hkt g ()))
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(K1 hkd_f) =
      K1 <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKD hkd hkt Exposed) @(NormalHKD hkd hkt f) @(NormalHKD hkd hkt g) f hkd_f

instance
    ( GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt Exposed) (NormalHKDRep hkd hkt f) (NormalHKDRep hkd hkt g)
    )
  =>
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (NormalHKD hkd hkt Exposed) (NormalHKD hkd hkt f) (NormalHKD hkd hkt g)
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(NormalHKD hkd_f) =
      NormalHKD <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKDRep hkd hkt Exposed) @(NormalHKDRep hkd hkt f) @(NormalHKDRep hkd hkt g) f hkd_f

instance
    ( GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt (t Exposed)) (NormalHKDRep hkd hkt (t f)) (NormalHKDRep hkd hkt (t g))
    )
  =>
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (K1 i (NormalHKD hkd hkt (t Exposed) ())) (K1 i (NormalHKD hkd hkt (t f) ())) (K1 i (NormalHKD hkd hkt (t g) ()))
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(K1 hkd_f) =
      K1 <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKD hkd hkt (t Exposed)) @(NormalHKD hkd hkt (t f)) @(NormalHKD hkd hkt (t g)) f hkd_f

instance
    ( GTraversableNormalHKDRep hkt f g (NormalHKDRep hkd hkt (t Exposed)) (NormalHKDRep hkd hkt (t f)) (NormalHKDRep hkd hkt (t g))
    )
  =>
    GTraversableNormalHKDRep (hkt :: (Type -> Type) -> Type -> Type) f g (NormalHKD hkd hkt (t Exposed)) (NormalHKD hkd hkt (t f)) (NormalHKD hkd hkt (t g))
  where
    {-# INLINABLE gtraverseNormalHKDRep #-}
    gtraverseNormalHKDRep f ~(NormalHKD hkd_f) =
      NormalHKD <$> gtraverseNormalHKDRep @hkt @f @g @(NormalHKDRep hkd hkt (t Exposed)) @(NormalHKDRep hkd hkt (t f)) @(NormalHKDRep hkd hkt (t g)) f hkd_f

--------------------------------------------------------------------------------

class FunctorHKD hkd hkt f g where
  mapHKD
    :: (forall a. f a -> g a)
    -> hkd f
    -> hkd g

  {-# INLINABLE mapHKD #-}
  default mapHKD
    :: TraversableHKD hkd hkt f g
    => (forall a. f a -> g a)
    -> hkd f
    -> hkd g
  mapHKD f hkd = runIdentity $ traverseHKD @hkd @hkt @f @g (Identity . f) hkd

instance {-# OVERLAPPABLE #-} TraversableHKD hkd hkt f g => FunctorHKD hkd hkt f g



{-# INLINABLE pureHKD #-}
pureHKD
  :: forall hkd hkt f.
     ( FunctorHKD hkd hkt f f
     )
  => (forall a. f a)
  -> hkd f
pureHKD zero = mapHKD @hkd @hkt @f @f (const zero) undefined

{-# INLINABLE transformHKD #-}
transformHKD
  :: forall hkd hkt1 hkt2 f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd hkt2 f g
     , f_hkd_f ~$ hkt1 f (hkd f)
     , f_hkd_g ~$ hkt1 f (hkd g)
     , g_hkd_g ~$ hkt1 g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformHKD f = hoistHK @hkt1 @f @g @(hkd g) f . fmapHK @hkt1 @f (mapHKD @hkd @hkt2 f)

--------------------------------------------------------------------------------

class ZippableHKD hkd hkt f g h where
  zipHKD
    :: (forall a. f a -> g a -> h a)
    -> hkd f
    -> hkd g
    -> hkd h

  {-# INLINABLE zipHKD #-}
  default zipHKD
    :: ( BiTraversableHKD hkd hkt f g h
       )
    => (forall a. f a -> g a -> h a)
    -> hkd f
    -> hkd g
    -> hkd h
  zipHKD combine f g = runIdentity $ bitraverseHKD @hkd @hkt @f @g @h (\f' g' -> Identity $ combine f' g') f g

instance {-# OVERLAPPABLE #-} BiTraversableHKD hkd hkt f g h => ZippableHKD hkd hkt f g h

--------------------------------------------------------------------------------

{-# INLINABLE withConstrainedFieldsHKD #-}
withConstrainedFieldsHKD
  :: forall c hkd hkt f.
     ( HKDFieldsHave c hkd
     , ZippableHKD hkd hkt (Dict c) f (Dict c `Product` f)
     )
  => hkd f -> hkd (Dict c `Product` f)
withConstrainedFieldsHKD = zipHKD @hkd @hkt (Pair) (withConstraintsHKD @c @hkd)

{-# INLINABLE withConstraintsHKD #-}
withConstraintsHKD :: forall c hkd. HKDFieldsHave c hkd => hkd (Dict c)
withConstraintsHKD = G.to $ gWithConstrainedFields (Proxy @c) (Proxy @(Rep (hkd Exposed)))



class
    ( Generic (t (Dict c)), Generic (t Identity), Generic (t Exposed)
    , GHKDFieldsHave c (Rep (t Exposed)) (Rep (t (Dict c)))
    )
  => HKDFieldsHave (c :: Type -> Constraint) t

instance
    ( Generic (t (Dict c)), Generic (t Identity), Generic (t Exposed)
    , GHKDFieldsHave c (Rep (t Exposed)) (Rep (t (Dict c)))
    )
  => HKDFieldsHave (c :: Type -> Constraint) t



class
    ( Generic (t (f (Dict c))), Generic (t (f Identity)), Generic (t (f Exposed))
    , GHKDFieldsHave c (Rep (t (f Exposed))) (Rep (t (f (Dict c))))
    )
  => HKDFieldsHaveF (c :: Type -> Constraint) t f

instance
    ( Generic (t (f (Dict c))), Generic (t (f Identity)), Generic (t (f Exposed))
    , GHKDFieldsHave c (Rep (t (f Exposed))) (Rep (t (f (Dict c))))
    )
  => HKDFieldsHaveF (c :: Type -> Constraint) t f



class GHKDFieldsHave (c :: Type -> Constraint) (exposed :: Type -> Type) withconstraint where
  gWithConstrainedFields :: Proxy c -> Proxy exposed -> withconstraint ()
instance GHKDFieldsHave c exposed withconstraint =>
    GHKDFieldsHave c (M1 s m exposed) (M1 s m withconstraint) where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields c _ = M1 (gWithConstrainedFields c (Proxy @exposed))
instance GHKDFieldsHave c U1 U1 where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields _ _ = U1
instance (GHKDFieldsHave c aExp aC, GHKDFieldsHave c bExp bC) =>
  GHKDFieldsHave c (aExp :*: bExp) (aC :*: bC) where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields be _ = gWithConstrainedFields be (Proxy @aExp) :*: gWithConstrainedFields be (Proxy @bExp)
instance (c x) => GHKDFieldsHave c (K1 i (Exposed x)) (K1 i (Dict c x)) where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields _ _ = K1 Dict
instance HKDFieldsHave c t =>
    GHKDFieldsHave c (K1 i (t Exposed)) (K1 i (t (Dict c))) where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t Exposed)))))
instance HKDFieldsHaveF c t f =>
    GHKDFieldsHave c (K1 i (t (f Exposed))) (K1 i (t (f (Dict c)))) where
  {-# INLINABLE gWithConstrainedFields #-}
  gWithConstrainedFields _ _ = K1 (G.to (gWithConstrainedFields (Proxy @c) (Proxy @(Rep (t (f Exposed))))))

--------------------------------------------------------------------------------

type DefaultHKD :: ((Type -> Type) -> Type) -> (Type -> Type) -> k
type family DefaultHKD hkd def where
  DefaultHKD hkd def = hkd def
  DefaultHKD hkd _ = hkd

--------------------------------------------------------------------------------
