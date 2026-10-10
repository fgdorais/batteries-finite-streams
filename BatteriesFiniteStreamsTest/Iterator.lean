import BatteriesFiniteStreams.Iterator

#guard (Std.Stream.iter [1, 2, 3]).toList == [1, 2, 3]
#guard ((Std.Stream.iter [1, 2, 3]).map (· * 2)).toArray == #[2, 4, 6]

-- Finite iterators are well-founded streams
#guard Std.Stream.Finite.toList (Std.toStream (0...3)) == [0, 1, 2]

def sumFor (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in Std.Stream.iter l do
    s := s + x
  return s

#guard sumFor [1, 2, 3] == 6

-- Round trip
#guard Std.Stream.Finite.toList (Std.Stream.iter [1, 2, 3]) == [1, 2, 3]
#guard Std.Stream.Finite.toList (Std.Stream.iter (Std.Stream.iter "abc".toRawSubstring)) ==
  ['a', 'b', 'c']
#guard (Std.Stream.iter [1, 2, 3]).atIdx? 1 == some 2
#guard (Std.Stream.iter [1, 2, 3]).atIdx? 3 == none

-- Lemmas
example : (Std.Stream.iter [1, 2, 3]).toList = [1, 2, 3] := by simp
example : (Std.Stream.iter [1, 2, 3]).toArray = #[1, 2, 3] := by simp
example : (Std.Stream.iter [1, 2, 3]).length = 3 := by simp
example [Std.Stream.WellFounded σ α] (s : σ) :
    (Std.Stream.iter s).toListRev = Std.Stream.Finite.toListRev s := by
  simp
example [Std.Stream σ α] {s t : σ} (h : Std.Stream.next? s = some (x, t)) :
    (Std.Stream.iter s).step.val = .yield (Std.Stream.iter t) x := by
  simp [Std.Stream.step_iter_of_next?_eq_some h]

-- Finiteness
example : Acc Std.Iter.IsPlausibleSuccessorOf (Std.Stream.iter [1, 2, 3]) :=
  Std.Stream.Finite.acc_iter _

example [Std.Stream σ α]
    (h : WellFounded fun t s : σ => ∃ x, Std.Stream.next? s = some (x, t)) :
    Std.Iterators.Finite (Std.Iterators.Types.StreamIterator σ α) Id :=
  Std.Stream.finite_streamIterator_iff.2 h
