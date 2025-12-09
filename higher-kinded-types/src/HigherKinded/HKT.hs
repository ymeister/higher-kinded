-- | Main module for higher-kinded types functionality.
--
-- This module re-exports the core functionality for working with higher-kinded types,
-- including type classes for HKT conversions and composition operations.
--
-- = Overview
--
-- The higher-kinded-types library provides abstractions for working with higher-kinded
-- type transformers and their compositions. It allows you to:
--
-- * Convert between different HKT representations using 'IsHKT', 'FromHKT', and 'ToHKT'
-- * Compose multiple HKT transformers using 'ComposeHKT'
-- * Work with applied type constructors
--
-- = Usage
--
-- @
-- import HigherKinded.HKT
--
-- -- Use HKT pattern for bidirectional conversions
-- example :: IsHKT hkt f => hkt f x -> f x
-- example = unHKT
-- @
module HigherKinded.HKT
  ( -- * Core Classes
    module X
  ) where

import HigherKinded.HKT.Class as X
import HigherKinded.HKT.Compose as X
