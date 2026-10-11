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
- `Std.Stream.WellFounded` asserts that the next relation of a stream type is well-founded, which
  provides an instance of `Std.Stream.Finite` for every stream of the given type.

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
def foo [Stream.HasNextRelation σ α] (s : σ) [Stream.Finite s] : β :=
  match hint : Stream.next? s with
  | none => _
  | some (x, t) =>
    have : Stream.Finite t := .ofSome hint
    _
termination_by Stream.Finite.wrap s
```
Several examples of this pattern can be found below. Note that `Stream.Finite s` depends on the
`Stream.HasNextRelation` instance, so functions should take that instance rather than a plain
`Stream` instance: a plain `Stream` instance only provides the default next relation, for which
there are no `Stream.Finite` instances.

The total operations on finite streams live in the `Std.Stream.Finite` namespace: the folds
`foldl`, `foldr`, `foldlM` and `foldrM`, as well as `length`, `toList` and `toArray`.
-/

namespace Std.Stream

/-- Class to define the next relation of a stream type. -/
public class HasNextRelation (σ : Type _) (α : outParam <| Type _) extends Stream σ α where
  /-- Next relation for a stream type `σ`. -/
  rel : σ → σ → Prop -- named `rel` to match `WellFoundedRelation`
  /-- The next relation extends the default one. -/
  rel_of_next?_eq_some : next? s = some (x, t) → rel t s

/-- Default next relation for a stream type. -/
public instance (priority := low) defaultNextRelation (σ) [Stream σ α] :
    HasNextRelation σ α where
  rel t s := ∃ x, next? s = some (x, t)
  rel_of_next?_eq_some h := ⟨_, h⟩

/-- Next relation for a stream. -/
public abbrev Next [HasNextRelation σ α] : σ → σ → Prop := HasNextRelation.rel

public theorem next_of_next?_eq_some [HasNextRelation σ α] {s t : σ} :
    next? s = some (x, t) → Next t s := HasNextRelation.rel_of_next?_eq_some

/-- Class for well-founded stream types. -/
public protected class WellFounded.{u, v} (σ : Type u) (α : outParam <| Type v) extends
  HasNextRelation σ α, WellFoundedRelation σ

/-- Defines a well-founded stream type instance from a well-founded relation. -/
@[expose, instance_reducible] public def WellFounded.ofRelation.{u, v} [Stream.{u, v} σ α]
    [inst : WellFoundedRelation σ]
    (h : {s t : σ} → {x : α} → next? s = some (x, t) → WellFoundedRelation.rel t s) :
    Stream.WellFounded σ α := { inst with rel_of_next?_eq_some := h }

/-- Defines a well-founded stream type instance from a measure. -/
@[expose, instance_reducible] public def WellFounded.ofMeasure.{u, v} [Stream.{u, v} σ α]
    (f : σ → Nat)
    (h : {s t : σ} → {x : α} → next? s = some (x, t) → f t < f s) :
    Stream.WellFounded σ α := { measure f with rel_of_next?_eq_some := h }

/- Prove termination goals `Next t s` for `termination_by s` on a well-founded stream type, given a
hypothesis `next? s = some (x, t)` in context. -/
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
public protected class Finite [HasNextRelation σ α] (s : σ) : Prop where
  /-- A finite stream is accessible with respect to the `Next` relation. -/
  acc : Acc Next s

public instance [Stream.WellFounded σ α] (s : σ) : Stream.Finite s where
  acc := match WellFounded.wf (σ := σ) with | ⟨h⟩ => h s

namespace Finite

/-- A stream related to a finite stream by the next relation is finite. -/
public theorem ofNext [HasNextRelation σ α] {s t : σ} [Stream.Finite s] (h : Next t s) :
    Stream.Finite t where
  acc := match acc (s := s) with | ⟨_, a⟩ => a _ h

/-- The stream following a finite stream is finite. -/
public theorem ofSome [HasNextRelation σ α] {s t : σ} [Stream.Finite s]
    (h : next? s = some (x, t)) : Stream.Finite t := .ofNext <| next_of_next?_eq_some h

/-- Wraps a finite stream into a well-founded type for use in termination proofs. -/
@[expose] public def wrap [HasNextRelation σ α] (s : σ) [Stream.Finite s] :
    { s : σ // Acc Next s } :=
  ⟨s, Finite.acc⟩

/-- Folds a monadic function over a finite stream from left to right. -/
@[specialize]
public def foldlM [Monad m] [HasNextRelation σ α] (s : σ) [Stream.Finite s]
    (f : β → α → m β) (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    f init x >>= foldlM t f
termination_by wrap s

public theorem foldlM_none [Monad m] [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    {f : β → α → m β} (h : next? s = none) : foldlM s f init = pure init := by
  rw [foldlM]; split <;> simp_all

public theorem foldlM_some [Monad m] [HasNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] {f : β → α → m β} (h : next? s = some (x, t)) :
    foldlM s f init = f init x >>= foldlM t f := by
  rw [foldlM]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a monadic function over a finite stream from right to left. -/
@[specialize]
public def foldrM [Monad m] [HasNextRelation σ α] (s : σ) [Stream.Finite s]
    (f : α → β → m β) (init : β) : m β :=
  match h : next? s with
  | none => pure init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    foldrM t f init >>= f x
termination_by wrap s

public theorem foldrM_none [Monad m] [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    {f : α → β → m β} (h : next? s = none) : foldrM s f init = pure init := by
  rw [foldrM]; split <;> simp_all

public theorem foldrM_some [Monad m] [HasNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] {f : α → β → m β} (h : next? s = some (x, t)) :
    foldrM s f init = foldrM t f init >>= f x := by
  rw [foldrM]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a function over a finite stream from left to right. -/
@[specialize]
public def foldl [HasNextRelation σ α] (s : σ) [Stream.Finite s] (f : β → α → β)
    (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    foldl t f (f init x)
termination_by wrap s

public theorem foldl_none [HasNextRelation σ α] {s : σ} [Stream.Finite s] {f : β → α → β}
    (h : next? s = none) : foldl s f init = init := by
  rw [foldl]; split <;> simp_all

public theorem foldl_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    {f : β → α → β} (h : next? s = some (x, t)) : foldl s f init = foldl t f (f init x) := by
  rw [foldl]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Folds a function over a finite stream from right to left. -/
@[specialize]
public def foldr [HasNextRelation σ α] (s : σ) [Stream.Finite s] (f : α → β → β)
    (init : β) : β :=
  match h : next? s with
  | none => init
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    f x <| foldr t f init
termination_by wrap s

public theorem foldr_none [HasNextRelation σ α] {s : σ} [Stream.Finite s] {f : α → β → β}
    (h : next? s = none) : foldr s f init = init := by
  rw [foldr]; split <;> simp_all

public theorem foldr_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    {f : α → β → β} (h : next? s = some (x, t)) : foldr s f init = f x (foldr t f init) := by
  rw [foldr]; split
  · simp_all
  · next heq => rw [h] at heq; cases heq; rfl

/-- Length of a finite stream. -/
@[inline]
public def length [HasNextRelation σ α] (s : σ) [Stream.Finite s] : Nat :=
  foldl s (fun l _ => l + 1) 0

public theorem length_none [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : length s = 0 := foldl_none h

private theorem foldl_succ [HasNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s (fun l _ => l + 1) n = foldl s (fun l _ => l + 1) 0 + n := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_succ (n := 0 + 1), foldl_succ (s := t)]
    omega
termination_by wrap s

public theorem length_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : length s = length t + 1 := by
  rw [length, foldl_some h, foldl_succ]; rfl

/-- Sequence of values of a finite stream as a `List` in reverse order. -/
@[inline]
private def toListRev [HasNextRelation σ α] (s : σ) [Stream.Finite s] : List α :=
  foldl s (fun r x => x :: r) []

private theorem toListRev_none [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toListRev s = [] := foldl_none h

private theorem foldl_cons [HasNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s (fun r x => x :: r) l = foldl s (fun r x => x :: r) [] ++ l := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_cons (l := [x]), foldl_cons (s := t)]
    simp
termination_by wrap s

private theorem toListRev_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s]
    [Stream.Finite t] (h : next? s = some (x, t)) : toListRev s = toListRev t ++ [x] := by
  rw [toListRev, foldl_some h, foldl_cons]; rfl

/-- Sequence of values of a finite stream as a `List`. -/
@[inline]
public def toList [HasNextRelation σ α] (s : σ) [Stream.Finite s] : List α :=
  toListRev s |>.reverse

public theorem toList_none [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toList s = [] := by
  simp [toList, toListRev_none h]

public theorem toList_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : toList s = x :: toList t := by
  simp [toList, toListRev_some h]

/-- Sequence of values of a finite stream as an `Array`. -/
@[inline]
public def toArray [HasNextRelation σ α] (s : σ) [Stream.Finite s] : Array α :=
  foldl s Array.push #[]

public theorem toArray_none [HasNextRelation σ α] {s : σ} [Stream.Finite s]
    (h : next? s = none) : toArray s = #[] := foldl_none h

private theorem foldl_push [HasNextRelation σ α] {s : σ} [Stream.Finite s] :
    foldl s Array.push l = l ++ foldl s Array.push #[] := by
  match h : next? s with
  | none => simp [foldl_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [foldl_some h, foldl_some h, foldl_push (l := #[].push x), foldl_push (s := t)]
    simp
termination_by wrap s

public theorem toArray_some [HasNextRelation σ α] {s t : σ} [Stream.Finite s] [Stream.Finite t]
    (h : next? s = some (x, t)) : toArray s = #[x] ++ toArray t := by
  rw [toArray, foldl_some h, foldl_push]; rfl

@[simp] public theorem toArray_toList [HasNextRelation σ α] {s : σ}
    [Stream.Finite s] : (toList s).toArray = toArray s := by
  match h : next? s with
  | none => simp [toList_none h, toArray_none h]
  | some (x, t) =>
    have : Stream.Finite t := .ofSome h
    rw [toList_some h, toArray_some h, List.toArray_cons, toArray_toList]
termination_by wrap s

@[simp] public theorem toList_list (l : List α) : toList l = l := by
  induction l with
  | nil => rw [toList_none rfl]
  | cons x l ih => rw [toList_some rfl, ih]

@[simp] public theorem toArray_list (l : List α) : toArray l = l.toArray := by
  rw [← toArray_toList, toList_list]

@[simp] public theorem length_list (l : List α) : length l = l.length := by
  induction l with
  | nil => rw [length_none rfl, List.length_nil]
  | cons x l ih => rw [length_some rfl, ih, List.length_cons]

end Finite

end Std.Stream
