# BatteriesFiniteStreams

Finite streams, stream combinators and stream iterators for Lean 4, as a Batteries cell.

- `BatteriesFiniteStreams.Finite` defines the classes `Std.Stream.Finite` (a specific stream is
  finite) and `Std.Stream.WellFounded` (every stream of a type is finite), with instances for
  lists, subarrays, raw substrings, byte slices and legacy ranges. The namespace
  `Std.Stream.Finite` provides terminating folds and conversions for finite streams: `foldl`,
  `foldr`, `foldlM`, `foldrM`, `length`, `toList` and `toArray`.
- `BatteriesFiniteStreams.Combinators` provides `takeUpTo`, `map`, `concat` and `join`, together
  with finiteness instances for these and for zipped (product) streams.
- `BatteriesFiniteStreams.Iterator` identifies streams with productive pure iterators that
  never skip, via `Std.Stream.iter`, with lemmas to transfer `toList`, `toArray` and `length`.
  Finiteness is the same notion on both sides: `Std.Stream.WellFounded` corresponds to
  `Std.Iterators.Finite`, and `Std.Stream.Finite s` to accessibility of `Std.Stream.iter s`.

```lean
import BatteriesFiniteStreams

open Std.Stream Std.Stream.Finite

#eval toList (takeUpTo 3 [1, 2, 3, 4, 5])        -- [1, 2, 3]
#eval toList (concat [1, 2, 3] [4, 5])          -- [1, 2, 3, 4, 5]
#eval toList ([1, 2, 3], ['a', 'b', 'c', 'd'])  -- [(1, 'a'), (2, 'b'), (3, 'c')]
```

## Usage

Add the cell to your `lakefile.toml`:

```toml
[[require]]
name = "batteries-finite-streams"
git = "https://github.com/fgdorais/batteries-finite-streams"
rev = "main"
```

The `main` branch tracks the Lean toolchain of Batteries `main`. The `nightly-testing` branch
tracks Batteries `nightly-testing`.

## Acknowledgements

This cell grew out of several pull requests to Batteries (formerly Std):

- [std4#127][1] by Mario Carneiro: well-founded stream class, with per-stream accessibility
  (`StreamAcc`) and well-founded stream types.
- [batteries#985][2] by François G. Dorais: `drop` and `take` for streams (merged).
- [batteries#1079][3] by François G. Dorais: well-founded streams and folds.
- [batteries#1331][4] and [batteries#1372][5] by François G. Dorais: finite and well-founded
  streams.
- [batteries#1334][6] by François G. Dorais: stream combinators.

[1]: https://github.com/leanprover-community/batteries/pull/127
[2]: https://github.com/leanprover-community/batteries/pull/985
[3]: https://github.com/leanprover-community/batteries/pull/1079
[4]: https://github.com/leanprover-community/batteries/pull/1331
[5]: https://github.com/leanprover-community/batteries/pull/1372
[6]: https://github.com/leanprover-community/batteries/pull/1334

---

Copyright (c) 2025 François G. Dorais. Released under the Apache 2.0 license, see
[LICENSE](LICENSE).
