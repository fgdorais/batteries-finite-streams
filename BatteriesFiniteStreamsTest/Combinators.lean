import BatteriesFiniteStreams.Combinators

/- Examples from docstrings -/

open Std.Stream Std.Stream.Finite

/-- The infinite stream of natural numbers starting from `n`. -/
structure Nats where
  n : Nat

instance : Std.Stream Nats Nat where
  next? s := some (s.n, ⟨s.n + 1⟩)

-- TakeUpTo
#guard toList (takeUpTo 3 [1,2,3,4,5,6]) == [1,2,3]
#guard toList (takeUpTo 3 [1,2]) == [1,2]
#guard toList (takeUpTo 3 (Nats.mk 0)) == [0, 1, 2]

-- Map
#guard toList (map (· ^ 2) [1,2,3,4,5]) == [1,4,9,16,25]

-- Concat
#guard toList (concat [1,2,3] [4,5]) == [1,2,3,4,5]

-- Join
#guard toList (join [[1,2],[3,4,5],[6]]) == [1,2,3,4,5,6]

-- Zip
#guard toList ([1,2,3], ['a','b','c','d','e']) == [(1, 'a'), (2, 'b'), (3, 'c')]
#guard toList (Nats.mk 0, [1,2]) == [(0, 1), (1, 2)]
