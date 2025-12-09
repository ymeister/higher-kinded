-- | Main module for higher-kinded data types.
--
-- This module provides a comprehensive framework for working with higher-kinded
-- data types, allowing you to parameterize data structures over type constructors.
--
-- = Overview
--
-- Higher-kinded data (HKD) allows you to define data types that are parameterized
-- by a type constructor rather than just a type. This enables powerful abstractions
-- such as:
--
-- * Validation and parsing with different functor wrappers
-- * Building data structures incrementally
-- * Generic programming over structures with higher-kinded fields
-- * Uniform transformations across all fields of a data type
--
-- = Basic Usage
--
-- @
-- {-\# LANGUAGE DeriveGeneric \#-}
-- {-\# LANGUAGE TypeFamilies \#-}
-- 
-- import HigherKinded.HKD
-- import GHC.Generics
-- 
-- data User f = User
--   { name :: f String
--   , age  :: f Int
--   } deriving Generic
-- 
-- -- Use with Identity for normal values
-- regularUser :: User Identity
-- regularUser = User (Identity \"Alice\") (Identity 30)
-- 
-- -- Use with Maybe for partial values
-- partialUser :: User Maybe
-- partialUser = User (Just \"Bob\") Nothing
-- @
--
-- = Re-exports
--
-- This module re-exports the key functionality from:
--
-- * "HigherKinded.HKD.Build": Building HKD values with named fields
-- * "HigherKinded.HKD.Class": Core type classes and instances
-- * "HigherKinded.HKD.Construction": Construction helpers
-- * "HigherKinded.HKD.Generic": Generic HKD representations
module HigherKinded.HKD
  ( -- * Re-exported modules
    module X
  ) where

import HigherKinded.HKD.Build as X
import HigherKinded.HKD.Class as X
import HigherKinded.HKD.Construction as X
import HigherKinded.HKD.Generic as X
import HigherKinded.HKD.Internal.Orphans ()
import HigherKinded.HKD.Internal.Void ()
