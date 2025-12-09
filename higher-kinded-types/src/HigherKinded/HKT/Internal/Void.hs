{-# LANGUAGE PolyKinds #-}

-- | Internal module for void types used in HKT machinery.
--
-- This module is internal and should not be imported directly.
-- Use "HigherKinded.HKT" instead.
module HigherKinded.HKT.Internal.Void where

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

-- | Uninhabited type with kind @Type@.
data Void

-- | Uninhabited type constructor with kind @Type -> Type@.
data Void1 a

-- | Uninhabited type constructor with kind @Type -> Type -> Type@.
--
-- This is used as a placeholder HKT transformer that can never be instantiated,
-- useful for type-level programming and constraint resolution.
data Void2 a b
