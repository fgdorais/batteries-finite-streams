import BatteriesFiniteStreams.Finite

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

instance : Std.Stream.HasNextRelation Test Nat where
  rel s t := t.decr → s.decr ∧ s.val < t.val
  rel_of_next?_eq_some := by
    intro _ _ _ h
    simp only [Std.Stream.next?] at h
    split at h
    · cases h; simp [*]
    · split at h
      · cases h; intro h; exact ⟨h, Nat.sub_one_lt ‹_›⟩
      · contradiction

theorem Test.acc : ∀ n, Acc Std.Stream.Next (Test.mk true n)
  | n => ⟨_, fun ⟨d, m⟩ h => by
    obtain ⟨hd, hm⟩ := h rfl
    simp only at hd hm
    subst hd
    exact Test.acc m⟩

instance : Std.Stream.Finite (Test.mk true n) := ⟨Test.acc n⟩

#guard Std.Stream.Finite.toList (Test.mk true 3) == [2, 1, 0]

/--
error: failed to synthesize instance of type class
  Std.Stream.Finite { decr := false, val := 3 }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval Std.Stream.Finite.toList (Test.mk false 3)

/- Standard well-founded stream types -/

#guard Std.Stream.Finite.toList [1, 2, 3] == [1, 2, 3]
#guard Std.Stream.Finite.toArray #[1, 2, 3][1...*] == #[2, 3]
#guard Std.Stream.Finite.toList "abc".toRawSubstring == ['a', 'b', 'c']
#guard Std.Stream.Finite.length (ByteArray.mk #[1, 2, 3]).toByteSlice == 3
#guard Std.Stream.Finite.toList [0:10:3] == [0, 3, 6, 9]
#guard Std.Stream.Finite.foldr [1, 2, 3] (· :: ·) [] == [1, 2, 3]

example : Std.Stream.Finite.toList [1, 2, 3] = [1, 2, 3] := by simp

example : Std.Stream.Finite.length [1, 2, 3] = 3 := by simp
example : Std.Stream.Finite.toArray [1, 2, 3] = #[1, 2, 3] := by simp

/- Folds -/

#guard Std.Stream.Finite.foldlM (m := Option) [1, 2, 3] (fun b a => some (b + a)) 0 == some 6
#guard Std.Stream.Finite.foldrM (m := Option) [1, 2, 3] (fun a b => some (a :: b)) [] ==
  some [1, 2, 3]
#guard Std.Stream.Finite.foldl [1, 2, 3] (fun b a => 10 * b + a) 0 == 123
#guard Std.Stream.Finite.foldr [1, 2, 3] (fun a b => 10 * b + a) 0 == 321

/- Documented recursion patterns -/

def sumWF [Std.Stream.WellFounded σ Nat] (s : σ) : Nat :=
  match _hint : Std.Stream.next? s with
  | none => 0
  | some (x, t) => x + sumWF t
termination_by s

def sumFinite [Std.Stream.HasNextRelation σ Nat] (s : σ) [Std.Stream.Finite s] : Nat :=
  match hint : Std.Stream.next? s with
  | none => 0
  | some (x, t) =>
    have : Std.Stream.Finite t := .ofSome hint
    x + sumFinite t
termination_by Std.Stream.Finite.wrap s

#guard sumWF [1, 2, 3] == 6
#guard sumFinite [1, 2, 3] == 6
#guard sumFinite (Test.mk true 4) == 6
