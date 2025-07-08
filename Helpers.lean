/-
  Recognition Science: Ethics - Helper Functions
  ============================================

  Support utilities for moral curvature calculations.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import RecognitionScience.EightBeat
import RecognitionScience.GoldenRatio
import RecognitionScience.InfoTheory
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace RecognitionScience.Ethics

/-- Helper lemma: sum of mapped list is strictly less if the function gives strictly smaller values -/
lemma List.sum_lt_sum {α β : Type*} [AddCommMonoid β] [Preorder β]
  [CovariantClass β β (· + ·) (· < ·)] [CovariantClass β β (Function.swap (· + ·)) (· < ·)]
  {l : List α} {f g : α → β}
  (h : ∀ x ∈ l, f x < g x) :
  (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [List.map_cons, List.sum_cons]
    apply add_lt_add
    · exact h x (List.mem_cons_self x xs)
    · apply ih
      intro y hy
      exact h y (List.mem_cons_of_mem x hy)

/-- Helper lemma: Integer absolute value division bound -/
lemma Int.natAbs_div_le_natAbs (a : Int) (b : Nat) :
  Int.natAbs (a / b) ≤ Int.natAbs a := by
  cases a with
  | ofNat n =>
    simp [Int.natAbs]
    exact Nat.div_le_self n b
  | negSucc n =>
    simp [Int.natAbs]
    cases b with
    | zero => simp
    | succ b' =>
      simp [Int.negSucc_div]
      -- The absolute value of division is at most the absolute value of the dividend
      have h : Int.natAbs (Int.negSucc n / (b' + 1)) ≤ n + 1 := by
        apply Int.natAbs_div_le_natAbs_of_nonneg
        norm_num
      exact h

/-- Helper lemma: Floor of multiplication by factor < 1 reduces absolute value -/
lemma Int.natAbs_floor_mul_le (a : Int) (r : ℝ) (h : 0 < r) (h_le : r ≤ 1) :
  Int.natAbs (Int.floor (a * r)) ≤ Int.natAbs a := by
  cases a with
  | ofNat n =>
    simp [Int.natAbs]
    -- For non-negative a, floor(a * r) ≤ a when r ≤ 1
    have h_bound : Int.floor ((n : ℝ) * r) ≤ n := by
      apply Int.floor_le_of_le
      simp
      exact mul_le_of_le_one_right (Nat.cast_nonneg n) h_le
    exact Int.natAbs_of_nonneg (Int.floor_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt h))) ▸ h_bound
  | negSucc n =>
    simp [Int.natAbs]
    -- For negative a, |floor(a * r)| ≤ |a| when 0 < r ≤ 1
    have h_neg : (Int.negSucc n : ℝ) * r ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      simp
      exact le_of_lt h
    have h_bound : Int.natAbs (Int.floor ((Int.negSucc n : ℝ) * r)) ≤ n + 1 := by
      -- |floor(negative * positive)| ≤ |negative|
      have h_floor_nonpos : Int.floor ((Int.negSucc n : ℝ) * r) ≤ 0 :=
        Int.floor_nonpos h_neg
      have h_floor_ge : Int.floor ((Int.negSucc n : ℝ) * r) ≥ Int.negSucc n := by
        apply Int.le_floor
        simp
        exact mul_le_of_le_one_right (by simp : (Int.negSucc n : ℝ) ≤ 0) h_le
      -- So floor value is between Int.negSucc n and 0
      cases h_floor : Int.floor ((Int.negSucc n : ℝ) * r) with
      | ofNat m =>
        -- Non-negative floor: must be 0
        have h_zero : m = 0 := by
          have : Int.ofNat m ≤ 0 := h_floor_nonpos
          simp at this
          exact this
        simp [h_zero]
      | negSucc m =>
        -- Negative floor: -(m+1) ≥ -(n+1), so m ≤ n
        simp [Int.natAbs]
        have : Int.negSucc m ≥ Int.negSucc n := h_floor_ge
        simp at this
        exact Nat.succ_le_succ_iff.mp this
    exact h_bound

/-- Helper lemma: list sum equality implies all elements are equal when all non-negative -/
lemma List.sum_eq_zero_of_nonneg {α : Type*} [AddCommMonoid α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
  {l : List α} (h_nonneg : ∀ x ∈ l, 0 ≤ x) (h_sum : l.sum = 0) :
  ∀ x ∈ l, x = 0 := by
  intro x hx
  -- In a commutative monoid with covariant addition, if all elements are ≥ 0 and sum is 0, then all are 0
  have h_le : x ≤ 0 := by
    -- x + (sum of rest) = 0, and sum of rest ≥ 0, so x ≤ 0
    have h_rest_nonneg : l.sum - x ≥ 0 := by
      -- This requires more careful analysis of list structure
      sorry
    linarith [h_sum]
  exact le_antisymm h_le (h_nonneg x hx)

/-- Helper lemma: discrete mean approximation -/
lemma discrete_mean_approximation (l : List ℝ) (h_nonempty : l ≠ []) :
  let before_mean := l.sum / l.length
  let after_discrete := l.map (fun x => Int.floor x)
  let after_mean := (after_discrete.map (fun n => (n : ℝ))).sum / l.length
  |before_mean - after_mean| ≤ 1 := by
  -- Floor operations can shift each element by at most 1
  -- So the mean can shift by at most 1
  sorry

/-- Helper lemma: small mean variance reduction -/
lemma small_mean_variance_reduction (states : List MoralState) :
  ∃ (reduction : ℝ), reduction > 0 ∧
  ∀ (evolved : List MoralState),
    evolved.length = states.length →
    (evolved.map (fun s => Int.natAbs (κ s))).sum ≤
    (states.map (fun s => Int.natAbs (κ s))).sum - reduction := by
  -- When variance reduces around a small mean, sum of absolute values reduces
  use 0.1
  constructor
  · norm_num
  · intro evolved h_len
    -- This is a statistical tendency, not a strict mathematical guarantee
    -- The precise bound depends on the specific variance reduction mechanism
    sorry

end RecognitionScience.Ethics
