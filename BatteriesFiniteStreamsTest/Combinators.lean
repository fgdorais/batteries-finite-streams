import BatteriesFiniteStreams.Combinators

/- Examples from docstrings -/

open Std.Stream

-- Constant
#guard next? (const 'a') == some ('a', const 'a')

-- TakeUpTo
#guard toList (takeUpTo 3 [1,2,3,4,5,6]) == [1,2,3]
#guard toList (takeUpTo 3 [1,2]) == [1,2]
#guard toList (takeUpTo 3 (const 'a')) == ['a', 'a', 'a']

-- Map
#guard toList (map (· ^ 2) [1,2,3,4,5]) == [1,4,9,16,25]

-- Union
#guard toList (Union.inl [1,2,3] : Union (List Nat) (Subarray Nat) Nat) == [1,2,3]
#guard toList (Union.inr #[1,2,3][*...*] : Union (List Nat) (Subarray Nat) Nat) == [1,2,3]

-- Concat
#guard toList (concat [1,2,3] [4,5]) == [1,2,3,4,5]

-- Join
#guard toList (join [[1,2],[3,4,5],[6]]) == [1,2,3,4,5,6]

-- Zip
#guard toList ([1,2,3], ['a','b','c','d','e']) == [(1, 'a'), (2, 'b'), (3, 'c')]
#guard toList (const 0, [1,2]) == [(0, 1), (0, 2)]
