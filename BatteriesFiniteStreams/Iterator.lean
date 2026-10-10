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
@[always_inline, inline]
public def iter [Stream σ α] (s : σ) : Iter (α := StreamIterator σ α) α :=
  ⟨{ stream := s }⟩

@[always_inline, inline]
public instance (σ α) [Stream σ α] : Iterator (StreamIterator σ α) Id α where
  IsPlausibleStep it
    | .yield it' out => next? it.internalState.stream = some (out, it'.internalState.stream)
    | .skip _ => False
    | .done => next? it.internalState.stream = none
  step it := pure <| .deflate <|
    match next? it.internalState.stream with
    | some (out, s) => ⟨.yield ⟨{ stream := s }⟩ out, rfl⟩
    | none => ⟨.done, rfl⟩

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

end Std.Stream
