# higher-kinded-types

A Haskell library providing abstractions for working with higher-kinded type transformers and their compositions.

## Overview

The `higher-kinded-types` library offers a unified framework for:

- **Type-level transformations**: Convert between different higher-kinded type representations
- **Composition**: Compose multiple HKT transformers together
- **Applied functors**: Work with type-level application of functors
- **Pattern synonyms**: Convenient bidirectional patterns for HKT manipulation

## Installation

Add `higher-kinded-types` to your project's dependencies in your `.cabal` file:

```cabal
build-depends:
    higher-kinded-types
```

## Quick Start

```haskell
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

import HigherKinded.HKT

-- Use the HKT pattern for bidirectional conversions
processHKT :: IsHKT hkt f => hkt f x -> f x
processHKT = unHKT

-- Pattern matching with HKT
example :: IsHKT hkt Maybe => hkt Maybe Int -> Maybe Int
example (HKT mx) = mx

-- Construction with HKT
makeHKT :: IsHKT hkt Maybe => Maybe Int -> hkt Maybe Int
makeHKT mx = HKT mx
```

## Core Concepts

### HKT Type Classes

The library provides three fundamental type classes:

- **`IsHKT`**: Constraint synonym ensuring bidirectional conversion
- **`FromHKT`**: Convert from HKT representation to underlying functor
- **`ToHKT`**: Convert from functor to HKT representation

```haskell
class FromHKT hkt f x where
  fromHKT :: hkt f x -> f x

class ToHKT hkt f x where
  toHKT :: f x -> hkt f x

class (forall x. ToHKT hkt f x, forall x. FromHKT hkt f x) => IsHKT hkt f
```

### Pattern Synonyms

The library provides convenient pattern synonyms for working with HKT values:

```haskell
-- Bidirectional pattern for HKT conversion
pattern HKT :: (FromHKT hkt f x, ToHKT hkt f x) => f x -> hkt f x

-- Pattern for higher-kinded wrapping
pattern HK :: (f_x ~$ hkt f x) => f x -> f_x

-- Pattern for applied functors
pattern App :: (f_x ~$ (f :$~> x)) => f x -> f_x
```

### Type-Level Application

The `($~>)` type family reduces nested type constructors to their applied forms:

```haskell
type family ($~>) f x where
  ($~>) Identity x = x
  ($~>) (Const a) x = a
  ($~>) (Compose f g) x = f $~> (g $~> x)
  ($~>) f x = f x
```

### HKT Transformers

Transform values wrapped in higher-kinded types:

```haskell
-- Map over HKT-wrapped functors
fmapHK :: (Functor f, f_x ~$ hkt f x, f_y ~$ hkt f y)
       => (x -> y) -> f_x -> f_y

-- Lift natural transformations
hoistHK :: (f_x ~$ hkt f x, g_x ~$ hkt g x)
        => (forall a. f a -> g a) -> f_x -> g_x

-- General transformation
transformHK :: (f_x ~$ hkt f x, g_y ~$ hkt g y)
            => (f x -> g y) -> f_x -> g_y
```

## Advanced Features

### HKT Composition

Compose multiple HKT transformers using `ComposeHKT`:

```haskell
import HigherKinded.HKT.Compose

-- Type-level composition
type MyComposition = ComposeHKT HKT1 HKT2 (Compose Maybe []) Int

-- Use ComposeHKT' for the wrapper
example :: ComposeHKT' hkt1 hkt2 (Compose Maybe []) Int
```

### Applied Functors

Work with type-level applied functors:

```haskell
import HigherKinded.HKT.Applied

-- Type-level application
type Applied1 = Maybe :$~> Int        -- Maybe Int
type Applied2 = Const String :$~> Int -- String

-- Pattern matching with App
processApp :: f_x ~$ (Maybe :$~> Int) => f_x -> Maybe Int
processApp (App mx) = mx

-- Transformations
fmapApp :: (Functor f, f_x ~$ (f :$~> x), f_y ~$ (f :$~> y))
        => (x -> y) -> f_x -> f_y
```

### Isomorphisms

Convert between isomorphic HKT representations:

```haskell
-- Convert between isomorphic HKTs
isoHK :: (f_x_1 ~$ hkt1 f x, f_x_2 ~$ hkt2 f x) => f_x_1 -> f_x_2

-- Type class for witnessing isomorphisms
class IsoHKT hkt1 hkt2 f
```

## Use Cases

### 1. Generic Programming

Use HKT abstractions to write generic code that works with multiple type representations:

```haskell
genericTransform :: (IsHKT hkt1 f, IsHKT hkt2 g)
                 => (forall x. f x -> g x)
                 -> hkt1 f a -> hkt2 g a
genericTransform nat = HKT . nat . unHKT
```

### 2. Type-Safe Wrappers

Create type-safe wrappers with controlled conversions:

```haskell
newtype Validated f x = Validated (f x)

instance FromHKT Validated f x where
  fromHKT (Validated fx) = fx

instance ToHKT Validated f x where
  toHKT = Validated

-- Now use with HKT patterns
process :: Validated Maybe Int -> Maybe Int
process (HKT mx) = mx
```

### 3. Functor Composition

Work with composed functors at the type level:

```haskell
type Nested = Compose Maybe [] :$~> Int

processNested :: Nested -> Maybe [Int]
processNested (App nested) = getCompose nested
```

## API Reference

### Modules

- **`HigherKinded.HKT`**: Main module, re-exports core functionality
- **`HigherKinded.HKT.Class`**: Core type classes and functions
- **`HigherKinded.HKT.Compose`**: HKT composition utilities
- **`HigherKinded.HKT.Applied`**: Applied functor abstractions

### Key Types

- `IsHKT`, `FromHKT`, `ToHKT`: Core conversion type classes
- `HKT'`: Newtype wrapper for HKT values
- `Applied`: Wrapper for applied functors
- `ComposeHKT'`: Wrapper for composed HKTs

### Key Functions

- `fromHKT`, `toHKT`: Basic conversion functions
- `fromHK`, `toHK`: Higher-kinded conversion functions
- `fmapHK`, `hoistHK`, `transformHK`: HKT transformations
- `fmapApp`, `hoistApp`, `transformApp`: Applied functor transformations
- `isoHK`: Isomorphism conversion

## Contributing

Contributions are welcome! Please submit issues and pull requests on the project repository.

## License

See the LICENSE file in the project repository for licensing information.
