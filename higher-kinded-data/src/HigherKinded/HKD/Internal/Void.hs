{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Internal module for void types used in HKD machinery.
--
-- This module is internal and should not be imported directly.
-- Use "HigherKinded.HKD" instead.
module HigherKinded.HKD.Internal.Void where

import GHC.Generics (Generic)

import HigherKinded.HKD.Generic

-- Note [Uncluttering type signatures]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Because the various instances in the library always match, they get replaced with
-- their constraints, resulting in large, unreadable types.
--
-- Writing an (overlapping instance) for this Void type means that the original
-- instance might not be the one selected, thus GHC leaves the constraints in
-- place until further information is provided, at which point the type
-- machinery has sufficient information to reduce to sensible types.

-- | Uninhabited type for type-level programming.
data Void

-- | Uninhabited type constructor.
data Void1 a

-- | Uninhabited binary type constructor.
data Void2 a b



instance {-# OVERLAPPING #-} Generic (HKD Void hkt f)
