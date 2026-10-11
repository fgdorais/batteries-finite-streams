/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/
module

public import BatteriesFiniteStreams.Finite

/-! # Stream Combinators -/

namespace Std.Stream

/-! ## TakeUpTo -/

/-- Restricts a given stream to a maximum number of values.

```
Finite.toList (takeUpTo 3 [1,2,3,4,5,6]) = [1,2,3]
Finite.toList (takeUpTo 3 [1,2]) = [1,2]
```
-/
public structure TakeUpTo (σ α) [Stream σ α] where
  takeUpTo ::
  /-- Maximum number of values. -/
  fuel : Nat
  /-- Underlying stream. -/
  stream : σ

export TakeUpTo (takeUpTo)

attribute [inherit_doc TakeUpTo] takeUpTo

public instance [Stream σ α] : Stream.WellFounded (TakeUpTo σ α) α := {
  measure TakeUpTo.fuel with
  next?
  | ⟨0, _⟩ => none
  | ⟨f+1, s⟩ => match next? s with
    | none => none
    | some (x, t) => some (x, ⟨f, t⟩)
  rel_of_next?_eq_some h := by
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h; simp_wf
}

@[simp] public theorem next?_takeUpTo_zero [Stream σ α] (s : σ) :
    next? (takeUpTo 0 s) = none := rfl

@[simp] public theorem next?_takeUpTo_succ [Stream σ α] (s : σ) :
    next? (takeUpTo (n+1) s) = match next? s with
      | none => none
      | some (x, s') => some (x, takeUpTo n s') := rfl

/-! ## Map -/

/-- Applies a function to each element of a stream.

```
Finite.toList (map (· ^ 2) [1,2,3,4,5]) = [1,4,9,16,25]
```

The function `f` is a parameter of the type `Map f σ` rather than a field, so the stream state does
not store a closure.
-/
public structure Map {β : Type _} (f : α → β) (σ) [Stream σ α] where
  /-- Underlying stream. -/
  stream : σ

@[inherit_doc Map]
public abbrev map (f : α → β) [Stream σ α] (s : σ) : Map f σ := ⟨s⟩

public instance [Stream σ α] (f : α → β) : Stream (Map f σ) β where
  next?
  | ⟨s⟩ => match next? s with
    | some (x, s) => some (f x, ⟨s⟩)
    | none => none

public theorem next?_map_eq_some_of_next?_eq_some [Stream σ α] {s : σ} {f : α → β}
    (h : next? s = some (x, s')) : next? (map f s) = some (f x, map f s') := by
  simp [next?, h]

public theorem next?_map_eq_none_of_next?_eq_none [Stream σ α] {s : σ} {f : α → β}
    (h : next? s = none) : next? (map f s) = none := by
  simp [next?, h]

public instance (f : α → β) [HasNextRelation σ α] : HasNextRelation (Map f σ) β where
  rel | ⟨s⟩, ⟨s'⟩ => Next s s'
  rel_of_next?_eq_some {s _ s'} h := by
    simp only [next?] at h
    match s, s' with
    | ⟨s⟩, ⟨s'⟩ =>
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · contradiction

public instance [HasNextRelation σ α] (f : α → β) (s : σ) [Stream.Finite s] :
    Stream.Finite (map f s) where
  acc := InvImage.accessible Map.stream Finite.acc

public instance [Stream.WellFounded σ α] (f : α → β) : Stream.WellFounded (Map f σ) β where
  wf := InvImage.wf Map.stream WellFounded.wf

/-! ## Concat -/

/-- Concatenates two streams one after the other.

```
Finite.toList (concat [1,2,3] [4,5]) = [1,2,3,4,5]
```

The first stream is dropped once it is exhausted (`Concat.snd`), so it is not polled again.
-/
public inductive Concat (σ τ α) [Stream σ α] [Stream τ α] where
  /-- Concatenation of two streams. -/
  | concat (s : σ) (t : τ)
  /-- Concatenation where the first stream is exhausted. -/
  | snd (t : τ)

export Concat (concat)

public instance [Stream σ α] [Stream τ α] : Stream (Concat σ τ α) α where
  next?
  | concat s t =>
    match next? s with
    | some (x, s) => some (x, concat s t)
    | none =>
      match next? t with
      | some (x, t) => some (x, .snd t)
      | none => none
  | .snd t =>
    match next? t with
    | some (x, t) => some (x, .snd t)
    | none => none

public instance [HasNextRelation σ α] [HasNextRelation τ α] :
    HasNextRelation (Concat σ τ α) α where
  rel
  | concat s₁ t₁, concat s₂ t₂ => Next s₁ s₂ ∧ t₁ = t₂
  | .snd t₁, concat _ t₂ | .snd t₁, .snd t₂ => Next t₁ t₂
  | concat _ _, .snd _ => False
  rel_of_next?_eq_some {c₁ _ c₂} h := by
    match c₁, c₂ with
    | concat s₁ t₁, _ =>
      simp only [next?] at h
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · split at h
        · cases h; simp [next_of_next?_eq_some, *]
        · contradiction
    | .snd t₁, _ =>
      simp only [next?] at h
      split at h
      · cases h; simp [next_of_next?_eq_some, *]
      · contradiction

@[instance]
public protected theorem Concat.finite_snd [HasNextRelation σ α] [HasNextRelation τ α]
    (t : τ) [Stream.Finite t] : Stream.Finite (.snd t : Concat σ τ α) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | concat _ _, hn => simp [Next, HasNextRelation.rel] at hn
  | .snd t', hn =>
    simp only [Next, HasNextRelation.rel] at hn
    have : Stream.Finite t' := .ofNext hn
    have := Concat.finite_snd (σ := σ) (α := α) t'
    exact Finite.acc
termination_by Finite.wrap t
decreasing_by exact hn

@[instance]
public protected theorem Concat.finite [HasNextRelation σ α] [HasNextRelation τ α]
    (s : σ) (t : τ) [Stream.Finite s] [Stream.Finite t] : Stream.Finite (concat s t) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | concat s' t', hn =>
    simp only [Next, HasNextRelation.rel] at hn
    have : Stream.Finite s' := .ofNext hn.1
    have := Concat.finite s' t
    rw [hn.2]
    exact Finite.acc
  | .snd t', hn =>
    simp only [Next, HasNextRelation.rel] at hn
    have : Stream.Finite t' := .ofNext hn
    exact Finite.acc (s := (.snd t' : Concat σ τ α))
termination_by Finite.wrap s
decreasing_by exact hn.1

public instance [Stream.WellFounded σ α] [Stream.WellFounded τ α] :
    Stream.WellFounded (Concat σ τ α) α where
  wf := .intro fun
    | concat _ _ => Finite.acc
    | .snd _ => Finite.acc

/-! ## Join -/

/-- Joins a list of streams one after the other.

```
Finite.toList (join [[1,2],[3,4,5],[6]]) = [1,2,3,4,5,6]
```
-/
public structure Join (σ α) [Stream σ α] where
  join ::
  /-- List of streams. -/
  streams : List σ

export Join (join)

attribute [inherit_doc Join] join

/-- Next step of a joined stream. -/
public protected def Join.next? [Stream σ α] : Join σ α → Option (α × Join σ α)
  | ⟨[]⟩ => none
  | ⟨s :: l⟩ =>
    match Stream.next? s with
    | some (x, s) => some (x, ⟨s :: l⟩)
    | none => Join.next? ⟨l⟩

public instance [Stream σ α] : Stream (Join σ α) α where
  next? := Join.next?

@[simp] public theorem next?_join_nil_eq_none [Stream σ α] :
    next? (join [] : Join σ α) = none := by
  simp [next?, Join.next?]

public theorem next?_join_cons_eq_some_of_next?_eq_some [Stream σ α] {s : σ}
    (h : next? s = some (x, s')) : next? (join (s :: l)) = some (x, join (s' :: l)) := by
  simp [next?, Join.next?, h]

public theorem next?_join_cons_eq_of_next?_eq_none [Stream σ α] {s : σ}
    (h : next? s = none) : next? (join (s :: l)) = next? (join l) := by
  simp [next?, Join.next?, h]

/-- Next relation for joined streams. -/
public protected def Join.Next [HasNextRelation σ α] : Join σ α → Join σ α → Prop
  | _, join [] => False
  | join l₁, join (s₂ :: l₂) =>
    match Stream.next? s₂ with
    | none => Join.Next (join l₁) (join l₂)
    | some _ =>
      match l₁ with
      | [] => False
      | s₁ :: l₁ => l₁ = l₂ ∧ Stream.Next s₁ s₂

private theorem Join.next_of_next?_eq_some [HasNextRelation σ α]
    {j₁ j₂ : Join σ α} (h : Stream.next? j₁ = some (x, j₂)) : Join.Next j₂ j₁ := by
  match j₁, j₂ with
  | join [], _ => simp [Stream.next?, Join.next?] at h
  | join (s₁ :: l₁), join l₂ =>
    simp [Stream.next?, Join.next?] at h
    split at h
    · next hs =>
      cases h
      rw [Join.Next.eq_def]
      simp [hs, Stream.next_of_next?_eq_some]
    · next hs =>
      rw [Join.Next.eq_def]
      simp [hs, Join.next_of_next?_eq_some h]

public instance [HasNextRelation σ α] : HasNextRelation (Join σ α) α where
  rel := Join.Next
  rel_of_next?_eq_some h := by exact Join.next_of_next?_eq_some h

public instance [HasNextRelation σ α] : Stream.Finite (join (σ := σ) (α := α) []) where
  acc := by
    apply Acc.intro
    intro _ h
    simp [Next, HasNextRelation.rel, Join.Next] at h

@[instance]
public protected theorem Join.finite_cons [HasNextRelation σ α] (s : σ) (l : List σ)
    [Stream.Finite s] [Stream.Finite (join l)] : Stream.Finite (join (s :: l)) := by
  apply Finite.mk
  apply Acc.intro
  intro
  | join l', h =>
    simp only [Stream.Next, HasNextRelation.rel] at h
    rw [Join.Next.eq_def] at h
    simp only at h
    split at h
    · next hs =>
      have : Stream.Finite (join l') := .ofNext h
      exact Finite.acc
    · next hs =>
      split at h
      · contradiction
      · next s' l' =>
        simp only [h.1, true_and] at h ⊢
        have : Stream.Finite s' := .ofNext h
        have : Stream.Finite (join (s' :: l)) := Join.finite_cons s' l
        exact Finite.acc
termination_by Finite.wrap s
decreasing_by exact h.2

public instance [Stream.WellFounded σ α] : Stream.WellFounded (Join σ α) α where
  wf := .intro fun
    | join l => by
      induction l with
      | nil => exact Finite.acc
      | cons s l ih =>
        have : Stream.Finite (join l) := ⟨ih⟩
        exact Finite.acc

/-! ## Zip

The standard library zips two streams using the product type: the stream `(s, t)` yields pairs of
values from `s` and `t` until either stream is exhausted.

```
Finite.toList ([1,2,3], ['a','b','c','d','e']) = [(1, 'a'), (2, 'b'), (3, 'c')]
```
-/

public instance [HasNextRelation σ α] [HasNextRelation τ β] :
    HasNextRelation (σ × τ) (α × β) where
  rel | (s₁, t₁), (s₂, t₂) => Next s₁ s₂ ∧ Next t₁ t₂
  rel_of_next?_eq_some {p₁ _ p₂} h := by
    simp only [next?] at h
    match p₁, p₂ with
    | (s₁, t₁), (s₂, t₂) =>
      split at h
      · contradiction
      · split at h
        · contradiction
        · cases h; simp [next_of_next?_eq_some, *]

public instance [HasNextRelation σ α] [HasNextRelation τ β] {s : σ} {t : τ}
    [Stream.Finite s] : Stream.Finite (s, t) where
  acc := Subrelation.accessible (fun h => h.1) (InvImage.accessible Prod.fst Finite.acc)

public instance [HasNextRelation σ α] [HasNextRelation τ β] {s : σ} {t : τ}
    [Stream.Finite t] : Stream.Finite (s, t) where
  acc := Subrelation.accessible (fun h => h.2) (InvImage.accessible Prod.snd Finite.acc)

public instance [Stream.WellFounded σ α] [HasNextRelation τ β] :
    Stream.WellFounded (σ × τ) (α × β) where
  wf := .intro fun (_, _) => Finite.acc

public instance [HasNextRelation σ α] [Stream.WellFounded τ β] :
    Stream.WellFounded (σ × τ) (α × β) where
  wf := .intro fun (_, _) => Finite.acc

end Std.Stream
