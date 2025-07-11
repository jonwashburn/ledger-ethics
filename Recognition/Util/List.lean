/-
Recognition Utility List Functions
==================================

Stub module providing list utility functions needed by Ethics.Helpers.
-/

import Mathlib.Data.List.BigOperators.Basic

namespace Recognition.Util.List

variable {α β : Type*} [OrderedAddCommMonoid β]

/-- Sum of a list is less than another if there exists a strict inequality and all others are ≤ -/
lemma sum_lt_sum_of_exists_lt_of_all_le
  (l₁ l₂ : List β)
  (h_len : l₁.length = l₂.length)
  (h_exists : ∃ i, i < l₁.length ∧ l₁.get ⟨i, by simp; exact i.2⟩ < l₂.get ⟨i, by simp [h_len]; exact i.2⟩)
  (h_all : ∀ i, i < l₁.length → l₁.get ⟨i, by simp; exact i.2⟩ ≤ l₂.get ⟨i, by simp [h_len]; exact i.2⟩) :
  l₁.sum < l₂.sum := by
  -- Convert to the mapped version using List.zipWith
  have h_zip : l₁.sum = (List.range l₁.length).map (fun i => l₁.get ⟨i, Nat.lt_of_mem_range (List.mem_range.mp i.2)⟩) |>.sum := by
    rw [List.sum_range_get]
  have h_zip2 : l₂.sum = (List.range l₁.length).map (fun i => l₂.get ⟨i, by rw [h_len]; exact Nat.lt_of_mem_range (List.mem_range.mp i.2)⟩) |>.sum := by
    rw [←h_len, List.sum_range_get]
  rw [h_zip, h_zip2]

  apply sum_lt_sum_of_exists_lt_of_all_le'
  · -- Exists case: convert index to element
    obtain ⟨i, h_i_lt, h_i_strict⟩ := h_exists
    use i
    constructor
    · exact List.mem_range.mpr h_i_lt
    · simp
      convert h_i_strict
      · simp
      · simp [h_len]
  · -- All case: convert index bound to element bound
    intro j h_j_in
    simp
    have h_j_lt : j < l₁.length := List.mem_range.mp h_j_in
    exact h_all j h_j_lt

/-- Alternative version for mapped lists -/
lemma sum_lt_sum_of_exists_lt_of_all_le'
  (l : List α) (f g : α → β)
  (h_exists : ∃ x ∈ l, f x < g x)
  (h_all : ∀ x ∈ l, f x ≤ g x) :
  (l.map f).sum < (l.map g).sum := by
  -- Use induction on the list
  induction l with
  | nil =>
    simp at h_exists
    contradiction
  | cons head tail ih =>
    simp [List.map_cons, List.sum_cons]
    cases h_exists with
    | intro x h_x =>
      cases h_x with
      | intro h_x_in h_x_lt =>
        cases h_x_in with
        | inl h_x_head =>
          -- x = head, so f(head) < g(head)
          rw [←h_x_head] at h_x_lt
          apply add_lt_add_of_lt_of_le h_x_lt
          apply List.sum_le_sum
          intro y h_y_in
          exact h_all y (List.mem_cons_of_mem head h_y_in)
        | inr h_x_tail =>
          -- x ∈ tail, so we can use induction hypothesis
          apply add_lt_add_of_le_of_lt
          · exact h_all head (List.mem_cons_self head tail)
          · apply ih
            · use x
              exact ⟨h_x_tail, h_x_lt⟩
            · intro y h_y_in
              exact h_all y (List.mem_cons_of_mem head h_y_in)

end Recognition.Util.List
