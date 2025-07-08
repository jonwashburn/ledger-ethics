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
import Recognition.Util.List
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
  simp [before_mean, after_mean, after_discrete]
  have h_bound : ∀ x : ℝ, |x - Int.floor x| ≤ 1 := by
    intro x
    have h_floor_le : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have h_lt_floor_add_one : x < Int.floor x + 1 := Int.lt_floor_add_one x
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  -- The difference in means is bounded by the maximum difference in elements
  have h_length_pos : (0 : ℝ) < l.length := by
    simp [Nat.cast_pos]
    exact List.length_pos_of_ne_nil h_nonempty
  -- Each element's contribution to the mean difference is bounded by 1/length
  have h_mean_bound : |before_mean - after_mean| ≤ l.length / l.length := by
    -- Sum of individual differences ≤ n * 1, so mean difference ≤ n/n = 1
    have h_sum_bound : |(l.map (fun x => x - Int.floor x)).sum| ≤ l.length := by
      calc |(l.map (fun x => x - Int.floor x)).sum|
        ≤ (l.map (fun x => |x - Int.floor x|)).sum := by exact abs_sum_le_sum_abs _
        _ ≤ (l.map (fun _ => (1 : ℝ))).sum := by
          apply List.sum_le_sum
          intro x h_in
          simp at h_in
          obtain ⟨y, h_y_in, h_eq⟩ := h_in
          rw [←h_eq]
          exact h_bound y
        _ = l.length := by simp
    rw [div_sub_div_eq_sub_div]
    exact div_le_iff_le_mul_right h_length_pos |>.mpr h_sum_bound
  rw [div_self (ne_of_gt h_length_pos)] at h_mean_bound
  exact h_mean_bound

/-- Virtue training strictly reduces curvature for non-zero states -/
lemma virtue_training_reduces_curvature_nonzero (v : Virtue) (s : MoralState)
  (h_nonzero : κ s ≠ 0) :
  Int.natAbs (κ (TrainVirtue v s)) < Int.natAbs (κ s) := by
  -- For non-zero curvature, virtue training creates strict reduction
  have h_general := virtue_training_reduces_curvature v s
  cases h_eq : κ s with
  | ofNat n =>
    cases n with
    | zero =>
      simp [h_eq] at h_nonzero
      contradiction
    | succ k =>
      -- Positive curvature case
      simp [TrainVirtue, curvature] at h_general ⊢
      cases v with
      | love =>
        -- Love divides by φ > 1, so strict reduction
        simp [TrainVirtue]
        have h_phi_gt_one : Real.goldenRatio > 1 := by
          simp [Real.goldenRatio]
          norm_num
        -- |floor(x/φ)| < |x| for x ≠ 0 and φ > 1
        have h_floor_div_lt : Int.natAbs (Int.floor ((k + 1 : ℝ) / Real.goldenRatio)) < k + 1 := by
          have h_div_lt : (k + 1 : ℝ) / Real.goldenRatio < k + 1 := by
            rw [div_lt_iff_lt_mul (by simp [Real.goldenRatio] : Real.goldenRatio > 0)]
            rw [one_mul]
            exact Nat.cast_lt.mpr (Nat.lt_mul_of_one_lt_right (Nat.succ_pos k) (by norm_num : 1 < Real.goldenRatio))
          have h_floor_le : (Int.floor ((k + 1 : ℝ) / Real.goldenRatio) : ℝ) ≤ (k + 1 : ℝ) / Real.goldenRatio := by
            exact Int.floor_le _
          have h_floor_lt : (Int.floor ((k + 1 : ℝ) / Real.goldenRatio) : ℝ) < k + 1 := by
            exact lt_of_le_of_lt h_floor_le h_div_lt
          have h_floor_nonneg : Int.floor ((k + 1 : ℝ) / Real.goldenRatio) ≥ 0 := by
            apply Int.floor_nonneg
            apply div_nonneg
            · exact Nat.cast_nonneg _
            · exact le_of_lt (by simp [Real.goldenRatio] : Real.goldenRatio > 0)
          rw [Int.natAbs_of_nonneg h_floor_nonneg]
          exact Int.coe_nat_lt_coe_nat_iff.mp h_floor_lt
        exact h_floor_div_lt
      | justice =>
        -- Justice zeros small values, reduces large ones
        simp [TrainVirtue]
        by_cases h_small : Int.natAbs (k + 1) < 5
        · simp [h_small]
          exact Nat.succ_pos k
        · simp [h_small]
          exact le_refl _
      | _ =>
        -- Other virtues use 0.9 factor, so strict reduction for positive values
        simp [TrainVirtue]
        have h_factor_lt_one : (0.9 : ℝ) < 1 := by norm_num
        have h_floor_lt : Int.natAbs (Int.floor ((k + 1 : ℝ) * 0.9)) < k + 1 := by
          have h_mult_lt : (k + 1 : ℝ) * 0.9 < k + 1 := by
            rw [← one_mul (k + 1 : ℝ)]
            exact mul_lt_mul_of_pos_right h_factor_lt_one (Nat.cast_pos.mpr (Nat.succ_pos k))
          have h_floor_le : (Int.floor ((k + 1 : ℝ) * 0.9) : ℝ) ≤ (k + 1 : ℝ) * 0.9 := by
            exact Int.floor_le _
          have h_floor_lt_real : (Int.floor ((k + 1 : ℝ) * 0.9) : ℝ) < k + 1 := by
            exact lt_of_le_of_lt h_floor_le h_mult_lt
          have h_floor_nonneg : Int.floor ((k + 1 : ℝ) * 0.9) ≥ 0 := by
            apply Int.floor_nonneg
            apply mul_nonneg
            · exact Nat.cast_nonneg _
            · norm_num
          rw [Int.natAbs_of_nonneg h_floor_nonneg]
          exact Int.coe_nat_lt_coe_nat_iff.mp h_floor_lt_real
        exact h_floor_lt
  | negSucc n =>
    -- Negative curvature case
    simp [TrainVirtue, curvature] at h_general ⊢
    -- Similar analysis for negative values
    cases v with
    | love =>
      simp [TrainVirtue]
      -- For negative values, division by φ brings closer to 0
      have h_abs_reduce : Int.natAbs (Int.floor ((Int.negSucc n : ℝ) / Real.goldenRatio)) < n + 1 := by
        -- -(n+1)/φ is closer to 0 than -(n+1)
        have h_div_closer : |(Int.negSucc n : ℝ) / Real.goldenRatio| < |Int.negSucc n| := by
          simp [abs_div, abs_neg]
          rw [div_lt_iff (by simp [Real.goldenRatio] : Real.goldenRatio > 0)]
          rw [one_mul]
          exact Nat.cast_lt.mpr (Nat.lt_mul_of_one_lt_right (Nat.succ_pos n) (by norm_num : 1 < Real.goldenRatio))
        -- Convert to natAbs bound
        have h_floor_bound : Int.natAbs (Int.floor ((Int.negSucc n : ℝ) / Real.goldenRatio)) ≤ Int.natAbs ((Int.negSucc n : ℝ) / Real.goldenRatio) := by
          exact Int.natAbs_floor_div_le_natAbs_of_nonneg (le_of_lt (by simp [Real.goldenRatio] : Real.goldenRatio > 0))
        simp at h_div_closer
        rw [Int.natAbs_neg] at h_div_closer
        exact Nat.lt_of_le_of_lt h_floor_bound (Int.natAbs_lt_natAbs_iff.mpr (Or.inr h_div_closer))
      exact h_abs_reduce
    | _ =>
      -- Similar for other virtues
      simp [TrainVirtue]
      -- Reduction factor < 1 brings negative values closer to 0
      have h_factor_reduces : Int.natAbs (Int.floor ((Int.negSucc n : ℝ) * 0.9)) < n + 1 := by
        -- 0.9 * -(n+1) is closer to 0 than -(n+1)
        have h_mult_closer : |(Int.negSucc n : ℝ) * 0.9| < |Int.negSucc n| := by
          simp [abs_mul, abs_neg]
          rw [← one_mul (n + 1 : ℝ)]
          exact mul_lt_mul_of_pos_right (by norm_num : (0.9 : ℝ) < 1) (Nat.cast_pos.mpr (Nat.succ_pos n))
        -- Convert to natAbs bound
        simp at h_mult_closer
        rw [Int.natAbs_neg] at h_mult_closer
        have h_floor_bound : Int.natAbs (Int.floor ((Int.negSucc n : ℝ) * 0.9)) ≤ Int.natAbs ((Int.negSucc n : ℝ) * 0.9) := by
          exact Int.natAbs_floor_mul_le (Int.negSucc n) 0.9 (by norm_num) (by norm_num)
        exact Nat.lt_of_le_of_lt h_floor_bound (Int.natAbs_lt_natAbs_iff.mpr (Or.inr h_mult_closer))
      exact h_factor_reduces

/-- Helper lemma: small mean variance reduction under virtue training -/
lemma small_mean_variance_reduction (states : List MoralState)
  (h_mean_small : |(states.map (fun s => (κ s : ℝ))).sum / states.length| < 1) :
  ∃ (reduction : ℝ), reduction > 0 ∧
  ∀ (virtue : Virtue) (h_nonzero : ∃ s ∈ states, κ s ≠ 0),
    let evolved := states.map (TrainVirtue virtue)
    (evolved.map (fun s => Int.natAbs (κ s))).sum ≤
    (states.map (fun s => Int.natAbs (κ s))).sum - reduction := by
  -- Under virtue training with small mean, at least one outlier gets reduced
  use 0.1  -- Small but positive reduction
  constructor
  · norm_num
  · intro virtue h_nonzero
    simp only [List.map_map]
    -- We know at least one state has non-zero curvature
    obtain ⟨s_nonzero, h_s_in, h_s_nonzero⟩ := h_nonzero

    -- Virtue training reduces curvature for non-zero states
    have h_strict : ∃ s ∈ states,
      Int.natAbs (κ (TrainVirtue virtue s)) < Int.natAbs (κ s) := by
      use s_nonzero, h_s_in
      exact virtue_training_reduces_curvature_nonzero virtue s_nonzero h_s_nonzero

    -- All states have non-increasing curvature
    have h_all : ∀ s ∈ states,
      Int.natAbs (κ (TrainVirtue virtue s)) ≤ Int.natAbs (κ s) := by
      intro s h_in
      exact virtue_training_reduces_curvature virtue s

    -- Apply the utility lemma
    have h_sum_lt : (states.map (fun s => Int.natAbs (κ (TrainVirtue virtue s)))).sum <
                    (states.map (fun s => Int.natAbs (κ s))).sum := by
      exact List.sum_lt_sum_of_exists_lt_of_all_le' h_strict h_all

    linarith [h_sum_lt]

end RecognitionScience.Ethics
