/-
  Recognition Science: List Lemmas
  ================================
  
  General-purpose lemmas about list operations, particularly
  foldl-based minimum finding which appears throughout the
  ethics layer.
  
  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax

namespace List

variable {α : Type*} [LinearOrder α]

/-- The foldl minimum operation finds an element from the list and it's minimal -/
lemma foldl_min (x : α) (xs : List α) :
  let m := xs.foldl (fun a b => if b ≤ a then b else a) x
  m ∈ x :: xs ∧ ∀ y ∈ x :: xs, m ≤ y := by
  induction xs generalizing x with
  | nil =>
    simp [foldl]
  | cons h t ih =>
    simp [foldl]
    by_cases hc : h ≤ x
    · -- We choose h as new accumulator
      have ih_h := ih h
      obtain ⟨h_mem, h_min⟩ := ih_h
      constructor
      · -- Membership: m is in h :: t, so in x :: h :: t
        cases h_mem with
        | head => right; left; rfl
        | tail h' => right; right; exact h'
      · -- Minimality
        intro y hy
        cases hy with
        | head => -- y = x
          subst y
          apply le_trans (h_min h (mem_cons_self h t)) hc
        | tail hy' =>
          cases hy' with
          | head => -- y = h
            subst y
            exact h_min h (mem_cons_self h t)
          | tail ht => -- y ∈ t
            exact h_min y (mem_cons_of_mem h ht)
    · -- We keep x as accumulator
      push_neg at hc
      have ih_x := ih x
      obtain ⟨h_mem, h_min⟩ := ih_x
      constructor
      · -- Membership: m is in x :: t
        cases h_mem with
        | head => left; rfl
        | tail h' => right; right; exact h'
      · -- Minimality
        intro y hy
        cases hy with
        | head => -- y = x
          subst y
          exact h_min x (mem_cons_self x t)
        | tail hy' =>
          cases hy' with
          | head => -- y = h
            subst y
            exact le_of_lt hc
          | tail ht => -- y ∈ t
            exact h_min y (mem_cons_of_mem x ht)

/-- Specialized version for non-empty lists -/
lemma foldl_min_cons (h : α) (t : List α) :
  let m := t.foldl (fun a b => if b ≤ a then b else a) h
  m ∈ h :: t ∧ ∀ y ∈ h :: t, m ≤ y := by
  have := foldl_min h t
  simp at this
  exact this

/-- Specialized version for finding minimum by a function value -/
lemma foldl_min_by {β : Type*} [LinearOrder β] (f : α → β) (x : α) (xs : List α) :
  let m := xs.foldl (fun a b => if f b ≤ f a then b else a) x
  m ∈ x :: xs ∧ ∀ y ∈ x :: xs, f m ≤ f y := by
  induction xs generalizing x with
  | nil =>
    simp [foldl]
  | cons h t ih =>
    simp [foldl]
    by_cases hc : f h ≤ f x
    · -- We choose h as new accumulator
      have ih_h := ih h
      obtain ⟨h_mem, h_min⟩ := ih_h
      constructor
      · -- Membership
        cases h_mem with
        | head => right; left; rfl
        | tail h' => right; right; exact h'
      · -- Minimality
        intro y hy
        cases hy with
        | head => -- y = x
          subst y
          apply le_trans (h_min h (mem_cons_self h t)) hc
        | tail hy' =>
          cases hy' with
          | head => -- y = h
            subst y
            exact h_min h (mem_cons_self h t)
          | tail ht => -- y ∈ t
            exact h_min y (mem_cons_of_mem h ht)
    · -- We keep x as accumulator
      push_neg at hc
      have ih_x := ih x
      obtain ⟨h_mem, h_min⟩ := ih_x
      constructor
      · -- Membership
        cases h_mem with
        | head => left; rfl
        | tail h' => right; right; exact h'
      · -- Minimality
        intro y hy
        cases hy with
        | head => -- y = x
          subst y
          exact h_min x (mem_cons_self x t)
        | tail hy' =>
          cases hy' with
          | head => -- y = h
            subst y
            exact le_of_lt hc
          | tail ht => -- y ∈ t
            exact h_min y (mem_cons_of_mem x ht)

end List
