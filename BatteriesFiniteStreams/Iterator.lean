/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesFiniteStreams.Finite

/-! # Streams and Iterators

The standard library provides iterators that behave much like streams but include many additional
features to support monadic effects, among other things. This added functionality makes the
iterator interface more complex. By comparison, the stream interface is quite simple and easy to
use.

The standard library already provides `Std.Stream` instances for productive pure iterators that
support random access (`IteratorAccess`). This module adds the reverse translation: `Std.Stream.iter` converts a stream into a productive pure
iterator. It also connects the finiteness properties of both interfaces:

- iterators of streams from a well-founded stream type are finite;
- finite pure iterators form a well-founded stream type.

This is also useful for existing stream-based libraries that want to gradually transition to
iterators.

Stream iterators also support `IteratorAccess`, so `Std.Stream.iter s` is itself a stream, and a
well-founded one when `σ` is a well-founded stream type.
-/

namespace Std.Iterators.Types

/-- The internal state of a stream iterator. -/
public structure StreamIterator (σ α) [Stream σ α] where
  /-- Underlying stream of a stream iterator. -/
  stream : σ

end Std.Iterators.Types

namespace Std.Stream
open Std.Iterators Std.Iterators.Types

/--
Returns a productive pure iterator for the given stream.

**Termination properties:**

* `Finite` instance: when `σ` is a well-founded stream type
* `Productive` instance: always
-/
@[expose, always_inline, inline]
public def iter [Stream σ α] (s : σ) : Iter (α := StreamIterator σ α) α :=
  ⟨{ stream := s }⟩

/-- The plausible steps of a stream iterator: it yields exactly what `next?` returns. -/
@[expose] public def _root_.Std.Iterators.Types.StreamIterator.IsPlausibleStep [Stream σ α]
    (it : IterM (α := StreamIterator σ α) Id α) :
    IterStep (IterM (α := StreamIterator σ α) Id α) α → Prop
  | .yield it' out => next? it.internalState.stream = some (out, it'.internalState.stream)
  | .skip _ => False
  | .done => next? it.internalState.stream = none

/-- The step of a stream iterator, given the result `o` of `next?`. -/
@[always_inline, inline]
public def _root_.Std.Iterators.Types.StreamIterator.stepOf [Stream σ α]
    (it : IterM (α := StreamIterator σ α) Id α) :
    (o : Option (α × σ)) → next? it.internalState.stream = o →
      PlausibleIterStep (StreamIterator.IsPlausibleStep it)
  | some (out, s), h => ⟨.yield ⟨{ stream := s }⟩ out, h⟩
  | none, h => ⟨.done, h⟩

@[always_inline, inline]
public instance (σ α) [Stream σ α] : Iterator (StreamIterator σ α) Id α where
  IsPlausibleStep := StreamIterator.IsPlausibleStep
  step it := pure <| .deflate <| StreamIterator.stepOf it _ rfl

public theorem step_iter_of_next?_eq_some [Stream σ α] {s t : σ}
    (h : next? s = some (x, t)) : (iter s).step = ⟨.yield (iter t) x, h⟩ := by
  have : ∀ o (ho : next? s = o), o = some (x, t) →
      (StreamIterator.stepOf (iter s).toIterM o ho).val.mapIterator IterM.toIter =
        .yield (iter t) x := by
    rintro _ _ rfl; rfl
  apply Subtype.ext
  simp only [Iter.step, IterM.step, Iterator.step, Id.run_pure, Shrink.inflate_deflate,
    IterM.Step.toPure]
  exact this _ rfl h

public theorem step_iter_of_next?_eq_none [Stream σ α] {s : σ}
    (h : next? s = none) : (iter s).step = ⟨.done, h⟩ := by
  have : ∀ o (ho : next? s = o), o = none →
      (StreamIterator.stepOf (iter s).toIterM o ho).val.mapIterator IterM.toIter =
        .done := by
    rintro _ _ rfl; rfl
  apply Subtype.ext
  simp only [Iter.step, IterM.step, Iterator.step, Id.run_pure, Shrink.inflate_deflate,
    IterM.Step.toPure]
  exact this _ rfl h

public instance [Stream σ α] : Productive (StreamIterator σ α) Id where
  wf := ⟨fun _ => ⟨_, fun _ h => nomatch h⟩⟩

@[always_inline, inline]
public instance [Stream σ α] [Monad n] : IteratorLoop (StreamIterator σ α) Id n :=
  .defaultImplementation

/-- Returns the step in which a stream iterator emits its `n`-th value, or `.done`. -/
public def _root_.Std.Iterators.Types.StreamIterator.nextAtIdx? [Stream σ α]
    (it : IterM (α := StreamIterator σ α) Id α) :
    (n : Nat) → PlausibleIterStep (it.IsPlausibleNthOutputStep n)
  | 0 =>
    match h : next? it.internalState.stream with
    | none => ⟨.done, .done h⟩
    | some (x, s) =>
      ⟨.yield ⟨{ stream := s }⟩ x, .zero_yield (it' := ⟨(⟨s⟩ : StreamIterator σ α)⟩) h⟩
  | n + 1 =>
    match h : next? it.internalState.stream with
    | none => ⟨.done, .done h⟩
    | some (_, s) =>
      let ⟨step, hs⟩ := nextAtIdx? ⟨{ stream := s }⟩ n
      ⟨step, .yield (it' := ⟨(⟨s⟩ : StreamIterator σ α)⟩) h hs⟩

public instance [Stream σ α] : IteratorAccess (StreamIterator σ α) Id where
  nextAtIdx? it n := pure (StreamIterator.nextAtIdx? it n)

public instance (σ α) [wf : Stream.WellFounded σ α] :
    Iterators.Finite (StreamIterator σ α) Id where
  wf := by
    refine Subrelation.wf ?_ (InvImage.wf (·.internalState.stream) wf.wf)
    intro _ _ ⟨step, heq, h⟩
    match step, heq, h with
    | .yield _ _, rfl, h => exact next_of_next?_eq_some h

private theorem finite_rel_of_isPlausibleNthOutputStep_zero [Iterator α m β] [Productive α m]
    {s t : IterM (α := α) m β}
    (h : ∃ v, IterM.IsPlausibleNthOutputStep 0 s (IterStep.yield t v)) :
    IterM.TerminationMeasures.Finite.Rel ⟨t⟩ ⟨s⟩ := by
  match h with
  | ⟨_, .zero_yield h⟩ => exact IterM.TerminationMeasures.Finite.rel_of_yield h
  | ⟨v, .skip hs h⟩ =>
    exact .trans (finite_rel_of_isPlausibleNthOutputStep_zero ⟨v, h⟩)
      (IterM.TerminationMeasures.Finite.rel_of_skip hs)
termination_by s.finitelyManySkips

public instance [Iterator α Id β] [Iterators.Finite α Id] [IteratorAccess α Id] :
    Stream.WellFounded (Iter (α := α) β) β where
  rel t s := ∃ v, IterM.IsPlausibleNthOutputStep 0 s.toIterM (IterStep.yield t.toIterM v)
  wf := by
    exact Subrelation.wf finite_rel_of_isPlausibleNthOutputStep_zero <|
      InvImage.wf _ WellFoundedRelation.wf
  rel_of_next?_eq_some {s _ _} h := by
    simp only [next?] at h
    split at h
    · cases h; exact ⟨_, ‹_›⟩
    · next h' _ => exact absurd h' IterM.not_isPlausibleNthOutputStep_yield
    · cases h

@[simp] public theorem toList_iter [Stream.WellFounded σ α] (s : σ) :
    (iter s).toList = Finite.toList s := by
  rw [Iter.toList_eq_match_step]
  match h : next? s with
  | none => simp [step_iter_of_next?_eq_none h, Finite.toList_none h]
  | some (x, t) =>
    simp only [step_iter_of_next?_eq_some h, toList_iter t, Finite.toList_some h]
termination_by Finite.wrap s

@[simp] public theorem toListRev_iter [Stream.WellFounded σ α] (s : σ) :
    (iter s).toListRev = Finite.toListRev s := by
  rw [Iter.toListRev_eq_match_step]
  match h : next? s with
  | none => simp [step_iter_of_next?_eq_none h, Finite.toListRev_none h]
  | some (x, t) =>
    simp only [step_iter_of_next?_eq_some h, toListRev_iter t, Finite.toListRev_some h]
termination_by Finite.wrap s

@[simp] public theorem toArray_iter [Stream.WellFounded σ α] (s : σ) :
    (iter s).toArray = Finite.toArray s := by
  rw [← Iter.toArray_toList, toList_iter, Finite.toArray_toList]

@[simp] public theorem length_iter [Stream.WellFounded σ α] (s : σ) :
    (iter s).length = Finite.length s := by
  rw [Iter.length_eq_match_step]
  match h : next? s with
  | none => simp [step_iter_of_next?_eq_none h, Finite.length_none h]
  | some (x, t) =>
    simp only [step_iter_of_next?_eq_some h, length_iter t, Finite.length_some h]
termination_by Finite.wrap s

end Std.Stream
