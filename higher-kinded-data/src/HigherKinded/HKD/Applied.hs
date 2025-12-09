{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Applied functor utilities for HKD.
--
-- This module provides convenient functions and pattern synonyms for
-- working with HKD types using the 'Applied' HKT transformer, which
-- simplifies type signatures and provides cleaner APIs.
--
-- ==== __Examples__
--
-- @
-- data Person = Person { name :: String, age :: Int } deriving Generic
--
-- -- Using the F pattern synonym
-- personF :: F Person Identity
-- personF = F (Identity (Person \"Alice\" 30))
--
-- -- Traversing with applied functors
-- validatePerson :: F Person Maybe -> Maybe (F Person Identity)
-- validatePerson = traverseF (maybe Nothing (Just . Identity))
-- @
module HigherKinded.HKD.Applied
  ( module HigherKinded.HKD.Applied
  , module HigherKinded.HKT.Applied
  ) where

import HigherKinded.HKD.Class
import HigherKinded.HKD.Construction
import HigherKinded.HKD.Generic
import HigherKinded.HKT
import HigherKinded.HKT.Applied



-- | Type synonym for HKD with the 'Applied' transformer.
--
-- This provides a simpler way to write HKD types:
-- @structure |~> f@ instead of @HKD structure Applied f@.
type (|~>) structure = HKD structure Applied

-- | Convenient type synonym for applied HKD.
--
-- @F Person Maybe@ is equivalent to @Person |~> Maybe@.
type F structure = (|~>) structure

-- | Pattern synonym for constructing and deconstructing applied HKD values.
--
-- This pattern provides a convenient way to work with HKD values
-- using the 'Applied' transformer.
--
-- @
-- -- Construction
-- mkPerson :: F Person Identity
-- mkPerson = F (Identity (Person \"Bob\" 25))
--
-- -- Pattern matching
-- getName :: F Person Identity -> String
-- getName (F (Identity person)) = name person
-- @
pattern F
  :: forall structure f.
     ConstructHKD (F structure) structure Applied f
  => f structure
  -> F structure f
pattern F { unF } <- (fromHKD @(F structure) @structure @Applied @f -> unF) where
  F x = toHKD @(F structure) @structure @Applied @f x



-- | Traverse two HKD structures simultaneously.
--
-- This function applies a binary operation to corresponding fields
-- of two HKD structures, collecting the results in an applicative context.
--
-- @
-- -- Combine two partial structures
-- mergeMaybe :: F Person Maybe -> F Person Maybe -> Maybe (F Person Identity)
-- mergeMaybe = bitraverseF (\mx my -> case (mx, my) of
--   (Just x, _) -> Just (Identity x)
--   (_, Just y) -> Just (Identity y)
--   _ -> Nothing)
-- @
bitraverseF
  :: forall structure f g h t.
     ( Applicative t
     , BiTraversableHKD (F structure) Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> structure |~> f
  -> structure |~> g
  -> t (structure |~> h)
bitraverseF = bitraverseApp @(F structure) @f @g @h

-- | Zip two applied HKD structures field-by-field.
--
-- Combines corresponding fields from two structures using the given function.
zipF
  :: forall structure f g h.
     ( ZippableHKD (F structure) Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> structure |~> f
  -> structure |~> g
  -> structure |~> h
zipF = zipApp @(F structure) @f @g @h

-- | Traverse an applied HKD structure.
--
-- Apply an applicative function to each field of the structure.
traverseF
  :: forall structure f g t.
     ( Applicative t
     , TraversableHKD (F structure) Applied f g
     )
  => (forall x. f x -> t (g x))
  -> structure |~> f
  -> t (structure |~> g)
traverseF = traverseApp @(F structure) @f @g

-- | Map a natural transformation over an applied HKD structure.
--
-- Transform each field using the given function.
mapF
  :: forall structure f g.
     ( FunctorHKD (F structure) Applied f g
     )
  => (forall x. f x -> g x)
  -> structure |~> f
  -> structure |~> g
mapF = mapApp @(F structure) @f @g

-- | Create an applied HKD structure with all fields set to the same value.
--
-- @
-- emptyStructure :: Structure |~> Maybe
-- emptyStructure = pureF Nothing
-- @
pureF
  :: forall structure f.
     ( FunctorHKD (F structure) Applied f f
     )
  => (forall a. f a)
  -> structure |~> f
pureF = pureApp @(F structure) @f



-- | Bi-traverse an HKD structure with the Applied transformer.
--
-- Combines two structures using an applicative binary operation.
bitraverseApp
  :: forall hkd f g h t.
     ( Applicative t
     , BiTraversableHKD hkd Applied f g h
     )
  => (forall x. f x -> g x -> t (h x))
  -> hkd f
  -> hkd g
  -> t (hkd h)
bitraverseApp = bitraverseHKD @hkd @Applied @f @g @h

-- | Zip two HKD structures with the Applied transformer.
--
-- Combines corresponding fields using the given function.
zipApp
  :: forall hkd f g h.
     ( ZippableHKD hkd Applied f g h
     )
  => (forall a. f a -> g a -> h a)
  -> hkd f
  -> hkd g
  -> hkd h
zipApp = zipHKD @hkd @Applied @f @g @h

-- | Traverse an HKD structure with the Applied transformer.
--
-- Apply an applicative function to each field.
traverseApp
  :: forall hkd f g t.
     ( Applicative t
     , TraversableHKD hkd Applied f g
     )
  => (forall x. f x -> t (g x))
  -> hkd f
  -> t (hkd g)
traverseApp = traverseHKD @hkd @Applied @f @g

-- | Map over an HKD structure with the Applied transformer.
--
-- Transform each field using a natural transformation.
mapApp
  :: forall hkd f g.
     ( FunctorHKD hkd Applied f g
     )
  => (forall x. f x -> g x)
  -> hkd f
  -> hkd g
mapApp = mapHKD @hkd @Applied @f @g

-- | Create an HKD structure with all fields set to the same value.
--
-- Uses the Applied transformer.
pureApp
  :: forall hkd f.
     ( FunctorHKD hkd Applied f f
     )
  => (forall a. f a)
  -> hkd f
pureApp = pureHKD @hkd @Applied @f



-- | Transform an HKD structure wrapped with Applied functors.
--
-- Combines mapping over the structure with functor transformations.
transformApplied
  :: forall hkd f g f_hkd_f f_hkd_g g_hkd_g.
     ( Functor f
     , FunctorHKD hkd Applied f g
     , f_hkd_f ~$ Applied f (hkd f)
     , f_hkd_g ~$ Applied f (hkd g)
     , g_hkd_g ~$ Applied g (hkd g)
     )
  => (forall x. f x -> g x)
  -> f_hkd_f
  -> g_hkd_g
transformApplied = transformHKD @hkd @Applied @Applied @f @g @f_hkd_f @f_hkd_g @g_hkd_g
