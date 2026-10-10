import BatteriesStream.Finite

/- Example of a stream type which is not well-founded but has many derivable finite instances. -/
structure Test where
  decr : Bool
  val : Nat
  deriving Repr

instance : Std.Stream Test Nat where
  next? s :=
    if ¬ s.decr then
      some (s.val, {s with val := s.val+1})
    else if s.val ≠ 0 then
      some (s.val-1, {s with val := s.val-1})
    else
      none

instance : Std.Stream.WithNextRelation Test Nat where
  rel s t := t.decr → s.decr ∧ s.val < t.val
  rel_of_next?_eq_some := by
    intro _ _ _ h
    simp only [Std.Stream.next?] at h
    split at h
    · cases h; simp [*]
    · split at h
      · cases h; intro h; exact ⟨h, Nat.sub_one_lt ‹_›⟩
      · contradiction

instance : Std.Stream.Finite (Test.mk true n) :=
  have wf : WellFounded (Std.Stream.RestrictedNext (Test.decr ·)) :=
    Subrelation.wf (fun h => (h.2 h.1).2) (measure Test.val).wf
  Std.Stream.Finite.ofRestrictedNext (p := (Test.decr ·))
    (fun h h' => (h h').1) rfl (wf.apply _)

#guard Std.Stream.toList (Test.mk true 3) == [2, 1, 0]

/--
error: failed to synthesize instance of type class
  Std.Stream.Finite { decr := false, val := 3 }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval Std.Stream.toList (Test.mk false 3)

/- Standard well-founded stream types -/

#guard Std.Stream.toList [1, 2, 3] == [1, 2, 3]
#guard Std.Stream.toArray #[1, 2, 3][1...*] == #[2, 3]
#guard Std.Stream.toList "abc".toRawSubstring == ['a', 'b', 'c']
#guard Std.Stream.length (ByteArray.mk #[1, 2, 3]).toByteSlice == 3
#guard Std.Stream.toList [0:10:3] == [0, 3, 6, 9]
#guard Std.Stream.foldr [1, 2, 3] (· :: ·) [] == [1, 2, 3]
#guard Std.Stream.toListRev [1, 2, 3] == [3, 2, 1]

example : Std.Stream.toList [1, 2, 3] = [1, 2, 3] := by simp
