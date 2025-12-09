# higher-kinded-data

A Haskell library for working with higher-kinded data types that supports multiple higher-kinded transformers, going beyond the capabilities of libraries like `barbies` and `higgledy`.

## Overview

While libraries like `barbies` and `higgledy` provide excellent support for higher-kinded data, they typically work with a fixed transformation pattern. The `higher-kinded-data` library extends this concept by allowing you to work with **different higher-kinded transformers (HKTs)**, enabling more flexible and powerful abstractions.

### What Makes This Library Different

The key innovation is the ability to parameterize not just by the functor (`f`) but also by the **transformer** (`hkt`) that determines how that functor is applied to each field:

```haskell
-- Traditional HKD (barbies/higgledy style)
data User f = User { name :: f String, age :: f Int }

-- This library: also parameterized by HKT transformer
data UserHKD hkt f = User { name :: hkt f $~ String, age :: hkt f $~ Int }
```

This extra level of abstraction enables:
- **Multiple transformation strategies** for the same data type
- **Composable HKT transformers** that can be mixed and matched
- **Type-level computation** on how functors are applied
- **Interoperability** between different HKD representations

### Key Features

- **Flexible HKT Transformers**: Use different transformers (`Applied`, `HKT'`, custom) for different use cases
- **HKT Composition**: Compose multiple transformers with `ComposeHKT`
- **Transformer Isomorphisms**: Convert between different HKT representations with `IsoHKD`
- **Type-Level Application**: The `($~>)` type family for type-level functor application
- **Generic Programming**: Automatic derivation via GHC Generics
- **Barbies Integration**: Built on `barbies` for familiar operations

## Installation

Add `higher-kinded-data` to your project's dependencies:

```cabal
build-depends:
    higher-kinded-data,
    higher-kinded-types  -- For HKT transformers
```

## Core Concepts: HKT Transformers

### The Applied Transformer

The most common transformer is `Applied`, which directly applies functors:

```haskell
import HigherKinded.HKD
import HigherKinded.HKT.Applied

-- Using Applied transformer
type PersonBasic = HKD Person Applied

-- Applied directly applies the functor to each field
-- Person Applied Maybe ≈ Person { name :: Maybe String, age :: Maybe Int }
```

### Custom Transformers

You can define custom transformers for specific behaviors:

```haskell
import HigherKinded.HKT

-- A transformer that adds logging
data Logged

instance FromHKT Logged f String where
  fromHKT = -- extract from logged representation

instance ToHKT Logged f String where  
  toHKT = -- wrap with logging

-- Now use with HKD
type PersonLogged = HKD Person Logged
```

### Transformer Composition

Compose multiple transformers for complex behaviors:

```haskell
import HigherKinded.HKT.Compose

-- Compose two transformers
type PersonComposed = HKD Person (ComposeHKT' Logged Validated)

-- This gives you both logging and validation!
```

### Isomorphic Transformers

Convert between different HKT representations:

```haskell
-- Define two different transformation strategies
type PersonV1 = HKD Person Applied
type PersonV2 = HKD Person MyCustomHKT

-- Convert between them (if isomorphic)
convert :: IsoHKD PersonV1 PersonV2 Applied MyCustomHKT f g 
        => PersonV1 f -> PersonV2 g
convert = isoHKD
```

## Practical Examples

### Example 1: Multiple Validation Strategies

```haskell
{-# LANGUAGE DeriveGeneric #-}

import HigherKinded.HKD
import GHC.Generics

data Form = Form 
  { email :: String
  , age :: Int
  , terms :: Bool
  } deriving (Generic)

-- Strategy 1: Simple validation with Applied
type SimpleValidation = HKD Form Applied Maybe

validateSimple :: Form -> SimpleValidation
validateSimple form = -- validation logic

-- Strategy 2: Detailed validation with custom HKT
data Validated  -- Custom HKT with error messages

type DetailedValidation = HKD Form (HKT' Validated) (Either ValidationError)

validateDetailed :: Form -> DetailedValidation  
validateDetailed form = -- detailed validation with errors

-- Convert between strategies when needed
simplifyValidation :: IsoHKD ... => DetailedValidation -> SimpleValidation
simplifyValidation = isoHKD
```

### Example 2: Database Mappings with Different ORMs

```haskell
-- Different ORMs might represent fields differently
data SqlPersistent  -- HKT for Persistent library
data SqlBeam        -- HKT for Beam library

data User = User { id :: Int, name :: String } deriving Generic

-- Same data, different database representations
type UserPersistent = HKD User (HKT' SqlPersistent)
type UserBeam = HKD User (HKT' SqlBeam)

-- Convert between representations when switching ORMs
migrateUser :: UserPersistent Identity -> UserBeam Identity
migrateUser = isoHKD  -- If transformers are isomorphic
```

### Example 3: Composable Effects

```haskell
-- Different effect transformers
data Async     -- Async computation
data Cached    -- Cached values
data Validated -- Validated inputs

-- Compose effects as needed
type FormAsync = HKD Form (HKT' Async) IO
type FormCached = HKD Form (HKT' Cached) IO  
type FormBoth = HKD Form (ComposeHKT' Async Cached) IO

-- Process with different effect combinations
processAsync :: FormAsync -> IO Result
processCached :: FormCached -> IO Result
processBoth :: FormBoth -> IO Result
```

## Why Multiple HKT Transformers Matter

Unlike `barbies` and `higgledy` which excel at the standard HKD pattern, this library's support for multiple HKT transformers enables:

1. **Gradual Type Refinement**: Use different transformers as data moves through processing stages
2. **Library Interoperability**: Bridge between different HKD representations used by various libraries
3. **Custom Semantics**: Define domain-specific transformers that encode your business logic
4. **Effect Composition**: Combine multiple effect systems at the type level
5. **Zero-Cost Abstraction**: Use `CoercibleHKD` for conversions that compile away

## API Overview

### Working with HKT Transformers

```haskell
-- Choose your transformer
type MyData1 = HKD Data Applied          -- Direct application
type MyData2 = HKD Data (HKT' Custom)    -- Custom transformer
type MyData3 = HKD Data (ComposeHKT' T1 T2) -- Composed transformers

-- Convert between representations
convert :: IsoHKD MyData1 MyData2 hkt1 hkt2 f g => MyData1 f -> MyData2 g
convert = isoHKD

-- Transform with specific HKT
transform :: IsHKD MyData hkt f => MyData f -> MyData g
transform = mapHKD @MyData @hkt transformation
```

### Core Modules

- **`HigherKinded.HKD`**: Main module, re-exports everything
- **`HigherKinded.HKD.Generic`**: Generic HKD with HKT support
- **`HigherKinded.HKD.Class`**: Type classes for HKT transformations
- **`HigherKinded.HKD.Applied`**: Applied transformer utilities
- **`HigherKinded.HKT`**: HKT transformers (from higher-kinded-types)

### Key Type Classes

- `IsHKD`: Core constraint for HKD with specific HKT
- `IsoHKD`: Isomorphism between different HKT representations
- `CoercibleHKD`: Zero-cost conversions between HKTs
- `FunctorHKD`, `TraversableHKD`: Operations parameterized by HKT
- `BiTraversableHKD`: Binary operations with HKT

### Key Functions

- `isoHKD`: Convert between different HKT representations
- `coerceHKD`: Zero-cost HKT conversion when possible
- `mapHKD @hkd @hkt`: Map with specific transformer
- `traverseHKD @hkd @hkt`: Traverse with specific transformer
- `transformHKD`: Complex transformations with multiple HKTs

## Complete Example: Multi-Stage Processing Pipeline

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

import HigherKinded.HKD
import HigherKinded.HKT
import GHC.Generics

-- Define the data
data Order = Order
  { orderId :: Int
  , customerId :: Int  
  , amount :: Double
  , status :: String
  } deriving (Generic)

-- Stage 1: Raw input with Applied
type RawOrder = HKD Order Applied Maybe
parseRaw :: String -> RawOrder

-- Stage 2: Validated with custom HKT
data ValidationHKT  -- Custom validation transformer
type ValidatedOrder = HKD Order (HKT' ValidationHKT) (Either Error)
validate :: RawOrder -> ValidatedOrder

-- Stage 3: Enriched with async HKT  
data AsyncHKT  -- Async enrichment transformer
type EnrichedOrder = HKD Order (HKT' AsyncHKT) IO
enrich :: ValidatedOrder -> EnrichedOrder

-- Stage 4: Final with composed HKT
type FinalOrder = HKD Order (ComposeHKT' ValidationHKT AsyncHKT) Identity
finalize :: EnrichedOrder -> IO FinalOrder

-- Pipeline can use different transformers at each stage!
processPipeline :: String -> IO FinalOrder
processPipeline = parseRaw >>> validate >>> enrich >>> finalize
```

## Standard HKD Operations

For users familiar with `barbies` or `higgledy`, all the standard operations are available:

```haskell
-- Define a simple HKD type
data User f = User
  { userId   :: f Int
  , userName :: f String
  , userAge  :: f Int
  } deriving (Generic)

-- All familiar operations work
traverseUser :: Applicative t => User t -> t (User Identity)
traverseUser = traverseHKD @User @Applied (pure . Identity)

-- Build with named fields (like higgledy)
buildUser :: User Identity
buildUser = build @(User Identity)
  ("userId" :! Identity 1)
  ("userName" :! Identity "Alice")
  ("userAge" :! Identity 30)

-- But you can also switch transformers!
type UserCustom = HKD User MyTransformer
convertUser :: User Identity -> UserCustom Identity
convertUser = isoHKD  -- If transformers are isomorphic
```

## Contributing

Contributions are welcome! Please submit issues and pull requests on the project repository.

## License

See the LICENSE file in the project repository for licensing information.