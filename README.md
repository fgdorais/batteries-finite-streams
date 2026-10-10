# BatteriesStream

Finite streams, stream combinators and stream iterators for Lean 4, as a Batteries cell.

- `BatteriesStream.Finite` defines the classes `Std.Stream.Finite` (a specific stream is finite)
  and `Std.Stream.WellFounded` (every stream of a type is finite), with instances for lists,
  subarrays, raw substrings, byte slices and legacy ranges. Finite streams support terminating
  folds and conversions: `foldl`, `foldr`, `foldlM`, `foldrM`, `length`, `toList`, `toListRev`
  and `toArray`.
- `BatteriesStream.Combinators` provides `const`, `takeUpTo`, `map`, `Union`, `concat` and
  `join`, together with finiteness instances for these and for zipped (product) streams.
- `BatteriesStream.Iterator` converts streams to productive pure iterators with
  `Std.Stream.iter`, and connects finiteness both ways: iterators of well-founded stream types
  are finite, and finite pure iterators form a well-founded stream type.

```lean
import BatteriesStream

open Std.Stream

#eval toList (takeUpTo 3 (const 'a'))           -- ['a', 'a', 'a']
#eval toList (concat [1, 2, 3] [4, 5])          -- [1, 2, 3, 4, 5]
#eval toList ([1, 2, 3], ['a', 'b', 'c', 'd'])  -- [(1, 'a'), (2, 'b'), (3, 'c')]
```

## Usage

Add the cell to your `lakefile.toml`:

```toml
[[require]]
name = "batteries-stream"
git = "https://github.com/fgdorais/batteries-stream"
rev = "main"
```

The `main` branch tracks the Lean toolchain of Batteries `main`. The `nightly-testing` branch
tracks Batteries `nightly-testing`.

## Maintenance

The GitHub workflows come from the [Batteries cell template][1]. They need a repository secret
called `BATTERIES_CELL_TOKEN` holding a [fine-grained personal access token][2] with read and
write access to contents, pull requests and workflows of this repository.

[1]: https://github.com/leanprover-community/batteries-cell-template
[2]: https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens#creating-a-fine-grained-personal-access-token
