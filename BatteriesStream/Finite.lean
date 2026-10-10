/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import Batteries.Data.ByteSlice
import all Std.Data.ByteSlice -- for unfolding `ByteSlice.slice` and `ByteSlice.size`

/-! # Finite and Well-Founded Streams

This module defines two main classes:

- `Std.Stream.Finite` provides a proof that a specific stream is finite.
- `Std.Stream.WellFounded` extends the `Std.Stream` class and provides an instance of
  `Std.Stream.Finite` for every stream of the given type.

The importance of these classes is that iterating along a finite stream is guaranteed to terminate.
Therefore, it is possible to prove facts about such iterations.

The `Stream.WellFounded` class is easiest to use: match on `Stream.next?` and provide a termination
hint. The general pattern is this:
```
def foo [Stream.WellFounded σ α] (s : σ) : β :=
  match _hint : Stream.next? s with
  | none => _
  | some (x, t) => _
termination_by s
```
The underscore in `_hint` only silences the unused variable linter: the hypothesis is used by the
termination checker.

The `Stream.Finite` class is more general but is slightly trickier to use:
```
def foo [Stream σ α] (s : σ) [Stream.Finite s] : β :=
  match hint : Stream.next? s with
  | none => _
  | some (x, t) =>
    have : Stream.Finite t := .ofSome hint
    _
termination_by Stream.Finite.wrap s
```
Several examples of this pattern can be found below.
-/

namespace Std.Stream

/-- Class to define the next relation of a stream type. -/
public class WithNextRelation (σ : Type _) (α : outParam <| Type _) extends Stream σ α where
  /-- Next relation for a stream type `σ`. -/
  rel : σ → σ → Prop -- named `rel` to match `WellFoundedRelation`
  /-- The next relation extends the default one. -/
  rel_of_next?_eq_some : next? s = some (x, t) → rel t s

/-- Default next relation for a stream type. -/
public instance (priority := low) defaultNextRelation (σ) [Stream σ α] :
    WithNextRelation σ α where
  rel t s := ∃ x, next? s = some (x, t)
  rel_of_next?_eq_some h := ⟨_, h⟩

/-- Next relation for a stream. -/
public abbrev Next [WithNextRelation σ α] : σ → σ → Prop := WithNextRelation.rel

/-- Next relation, restricted to a subset of streams. -/
public abbrev RestrictedNext [WithNextRelation σ α] (p : σ → Prop) (s t : σ) : Prop :=
  p t ∧ Next s t

public theorem next_of_next?_eq_some [WithNextRelation σ α] {s t : σ} :
    next? s = some (x, t) → Next t s := WithNextRelation.rel_of_next?_eq_some

/-- Class for well-founded stream types. -/
public protected class WellFounded.{u, v} (σ : Type u) (α : outParam <| Type v) extends
  WithNextRelation σ α, WellFoundedRelation σ

/-- Defines a well-founded stream type instance from a well-founded relation. -/
@[expose, instance_reducible] public def WellFounded.ofRelation.{u, v} [Stream.{u, v} σ α]
    [inst : WellFoundedRelation σ]
    (h : {s t : σ} → {x : α} → next? s = (x, t) → WellFoundedRelation.rel t s) :
    Stream.WellFounded σ α := { inst with rel_of_next?_eq_some := h }

/-- Defines a well-founded stream type instance from a measure. -/
@[expose, instance_reducible] public def WellFounded.ofMeasure.{u, v} [Stream.{u, v} σ α]
    (f : σ → Nat)
    (h : {s t : σ} → {x : α} → next? s = (x, t) → f t < f s) :
    Stream.WellFounded σ α := { measure f with rel_of_next?_eq_some := h }

macro_rules
| `(tactic| decreasing_trivial) => `(tactic| apply Std.Stream.next_of_next?_eq_some; assumption)

public instance (α) : Stream.WellFounded (List α) α :=
  .ofMeasure List.length <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · contradiction
    · cases h; simp

public instance : Stream.WellFounded Substring.Raw Char :=
  .ofMeasure Substring.Raw.bsize <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · next hlt =>
      cases h
      simp only [Substring.Raw.bsize, String.Pos.Raw.next, String.Pos.Raw.byteIdx_add_char]
      apply Nat.sub_lt_sub_left hlt
      apply Nat.lt_add_of_pos_right
      exact Char.utf8Size_pos _
    · contradiction

public instance (α) : Stream.WellFounded (Subarray α) α :=
  .ofMeasure (fun s => s.stop - s.start) <| by
    intro s _ _ h
    simp only [next?] at h
    split at h
    · cases h; show s.stop - (s.start + 1) < s.stop - s.start; omega
    · contradiction

private theorem size_popFront_lt {s : ByteSlice} (h : 0 < s.size) : s.popFront.size < s.size := by
  have h₁ := s.stop_eq_start_add_size
  have h₂ := s.stop_le_size_byteArray
  unfold ByteSlice.popFront ByteSlice.slice
  dsimp only
  rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  show (s.start + min s.size s.size) - (s.start + min 1 s.size) < s.size
  omega

public instance : Stream.WellFounded ByteSlice UInt8 :=
  .ofMeasure ByteSlice.size <| by
    intro _ _ _ h
    simp only [next?, bind, Option.bind] at h
    split at h
    · contradiction
    · next heq =>
      rw [getElem?_def] at heq
      split at heq
      · cases h; exact size_popFront_lt ‹_›
      · contradiction

public instance : Stream.WellFounded Legacy.Range Nat :=
  .ofMeasure (fun r => r.stop - r.start) <| by
    intro _ _ _ h
    simp only [next?] at h
    split at h
    · next hlt =>
      cases h
      apply Nat.sub_lt_sub_left hlt
      apply Nat.lt_add_of_pos_right
      exact Legacy.Range.step_pos _
    · contradiction

/-- Class for a finite stream of type `σ`. -/
public protected class Finite [WithNextRelation σ α] (s : σ) : Prop where
  /-- A finite stream is accessible with respect to the `Next` relation. -/
  acc : Acc Next s

public instance [Stream.WellFounded σ α] (s : σ) : Stream.Finite s where
  acc := match WellFounded.wf (σ := σ) with | ⟨h⟩ => h s

namespace Finite

/-- Successor of a finite stream is finite. -/
public theorem ofNext [WithNextRelation σ α] {s t : σ} [Stream.Finite s] (h : Next t s) :
    Stream.Finite t where
  acc := match acc (s := s) with | ⟨_, a⟩ => a _ h

/-- Successor of a finite stream is finite. -/
public theorem ofSome [WithNextRelation σ α] {s t : σ} [Stream.Finite s]
    (h : next? s = some (x, t)) : Stream.Finite t := .ofNext <| next_of_next?_eq_some h

/-- Introduces a predicate `p` into an accessibility relation, provided that it holds of the
initial point. -/
private theorem acc_restriction (p : α → Prop) {r : α → α → Prop} {a : α}
    (acc : Acc r a) (h : p a) : Acc (fun x y => p y → p x ∧ r x y) a := by
  induction acc with
  | intro x _ ih => exact ⟨_, fun y hr => ih y (hr h).2 (hr h).1⟩

/-- Defines a finite stream instance for a restricted subset of streams. -/
public theorem ofRestrictedNext.{u, v} [WithNextRelation.{u, v} σ α] {p : σ → Prop}
    (H : ∀ {s t}, Next s t → p t → p s) (h : p s) (acc : Acc (RestrictedNext p) s) :
    Stream.Finite s where
  acc :=
    Subrelation.accessible (fun h₁ h₂ => ⟨H h₁ h₂, h₂, h₁⟩) (acc_restriction p acc h)

/-- Wraps a finite stream into a well-founded type for use in termination proofs. -/
@[expose] public def wrap [WithNextRelation σ α] (s : σ) [Stream.Finite s] :
    { s : σ // Acc Next s } :=
  ⟨s, Finite.acc⟩

end Finite

/-- Folds a monadic function over a finite stream from left to right. -/
@[specialize]
public def foldlM [Monad m] [WithNextRelation σ α] (s : σ) [Stream.Finite s]
    (f : β → α → m β) (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    f init x >>= foldlM t f
termination_by Finite.wrap s

public theorem foldlM_none [Monad m] [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    {f : β → α → m β} (h : next? s = none) : foldlM s f init = pure init := by
  rw [foldlM]; split <;> simp_all

public theorem foldlM_some [Monad m] [WithNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] {f : β → α → m β} (h : next? s = some (x, t)) :
    foldlM s f init = f init x >>= foldlM t f := by
  rw [foldlM]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a monadic function over a finite stream from right to left. -/
@[specialize]
public def foldrM [Monad m] [WithNextRelation σ α] (s : σ) [Stream.Finite s]
    (f : α → β → m β) (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    foldrM t f init >>= f x
termination_by Finite.wrap s

public theorem foldrM_none [Monad m] [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    {f : α → β → m β} (h : next? s = none) : foldrM s f init = pure init := by
  rw [foldrM]; split <;> simp_all

public theorem foldrM_some [Monad m] [WithNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] {f : α → β → m β} (h : next? s = some (x, t)) :
    foldrM s f init = foldrM t f init >>= f x := by
  rw [foldrM]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a function over a finite stream from left to right. -/
@[specialize]
public def foldl [WithNextRelation σ α] (s : σ) [Stream.Finite s] (f : β → α → β)
    (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    foldl t f (f init x)
termination_by Finite.wrap s

public theorem foldl_none [WithNextRelation σ α] {s : σ} [Stream.Finite s] {f : β → α → β}
    (h : next? s = none) : foldl s f init = init := by
  rw [foldl]; split <;> simp_all

public theorem foldl_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    {f : β → α → β} (h : next? s = some (x, t)) : foldl s f init = foldl t f (f init x) := by
  rw [foldl]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a function over a finite stream from right to left. -/
@[specialize]
public def foldr [WithNextRelation σ α] (s : σ) [Stream.Finite s] (f : α → β → β)
    (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    f x <| foldr t f init
termination_by Finite.wrap s

public theorem foldr_none [WithNextRelation σ α] {s : σ} [Stream.Finite s] {f : α → β → β}
    (h : next? s = none) : foldr s f init = init := by
  rw [foldr]; split <;> simp_all

public theorem foldr_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    {f : α → β → β} (h : next? s = some (x, t)) : foldr s f init = f x (foldr t f init) := by
  rw [foldr]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Length of a finite stream. -/
@[inline]
public def length [WithNextRelation σ α] (s : σ) [Stream.Finite s] : Nat :=
  foldl s (fun l _ => l + 1) 0

public theorem length_none [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : length s = 0 := foldl_none h

private theorem foldl_succ [WithNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s (fun l _ => l + 1) n = foldl s (fun l _ => l + 1) 0 + n := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_succ (n := 0 + 1), foldl_succ (s := t)]
    omega
termination_by Finite.wrap s

public theorem length_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : length s = length t + 1 := by
  rw [length, foldl_some h, foldl_succ]; rfl

/-- Sequence of values of a finite stream as a `List` in reverse order. -/
@[inline]
public def toListRev [WithNextRelation σ α] (s : σ) [Stream.Finite s] : List α :=
  foldl s (fun r x => x :: r) []

public theorem toListRev_none [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toListRev s = [] := foldl_none h

private theorem foldl_cons [WithNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s (fun r x => x :: r) l = foldl s (fun r x => x :: r) [] ++ l := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_cons (l := [x]), foldl_cons (s := t)]
    simp
termination_by Finite.wrap s

public theorem toListRev_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] (h : next? s = some (x, t)) : toListRev s = toListRev t ++ [x] := by
  rw [toListRev, foldl_some h, foldl_cons]; rfl

/-- Sequence of values of a finite stream as a `List`. -/
@[inline]
public def toList [WithNextRelation σ α] (s : σ) [Stream.Finite s] : List α :=
  toListRev s |>.reverse

public theorem toList_none [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toList s = [] := by
  simp [toList, toListRev_none h]

public theorem toList_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : toList s = x :: toList t := by
  simp [toList, toListRev_some h]

/-- Sequence of values of a finite stream as an `Array`. -/
@[inline]
public def toArray [WithNextRelation σ α] (s : σ) [Stream.Finite s] : Array α :=
  foldl s Array.push #[]

public theorem toArray_none [WithNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toArray s = #[] := foldl_none h

private theorem foldl_push [WithNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s Array.push l = l ++ foldl s Array.push #[] := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_push (l := #[].push x), foldl_push (s := t)]
    simp
termination_by Finite.wrap s

public theorem toArray_some [WithNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : toArray s = #[x] ++ toArray t := by
  rw [toArray, foldl_some h, foldl_push]; rfl

@[simp] public theorem toArray_toList_eq_toArray [WithNextRelation σ α] {s : σ}
    [Stream.Finite s] : (toList s).toArray = toArray s := by
  match h : next? s with
  | none => simp [toList_none h, toArray_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [toList_some h, toArray_some h, List.toArray_cons, toArray_toList_eq_toArray]
termination_by Finite.wrap s

@[simp] public theorem toList_eq_self (l : List α) : toList l = l := by
  induction l with
  | nil => rw [toList_none rfl]
  | cons x l ih => rw [toList_some rfl, ih]

end Std.Stream
