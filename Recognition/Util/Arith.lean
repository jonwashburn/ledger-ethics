/-
Recognition Arithmetic Utilities
================================

Common arithmetic lemmas to replace omega tactics with explicit proofs.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace Recognition.Util.Arith

variable {a b c : ℤ} {m n k : ℕ}

/-! ## Natural number inequalities -/

lemma nat_le_add_right (n k : ℕ) : n ≤ n + k :=
  Nat.le_add_right n k

lemma nat_le_add_left (n k : ℕ) : n ≤ k + n :=
  Nat.le_add_left n k

lemma nat_div_le_self (n k : ℕ) : n / k ≤ n :=
  Nat.div_le_self n k

lemma nat_succ_pos (n : ℕ) : 0 < n + 1 :=
  Nat.succ_pos n

lemma nat_one_le_succ (n : ℕ) : 1 ≤ n + 1 :=
  Nat.succ_le_succ (Nat.zero_le n)

lemma nat_lt_succ_self (n : ℕ) : n < n + 1 :=
  Nat.lt_succ_self n

/-! ## Integer inequalities -/

lemma int_add_le_add_left (a b c : ℤ) : a ≤ b → c + a ≤ c + b :=
  Int.add_le_add_left

lemma int_add_le_add_right (a b c : ℤ) : a ≤ b → a + c ≤ b + c :=
  Int.add_le_add_right

lemma int_neg_le_neg (a b : ℤ) : a ≤ b → -b ≤ -a :=
  Int.neg_le_neg

lemma int_div_le_self_of_pos (a : ℤ) (h_pos : 0 < a) : a / 2 ≤ a := by
  have h_two_pos : (0 : ℤ) < 2 := by norm_num
  exact Int.div_le_self_of_pos h_pos h_two_pos

lemma int_div_le_self_of_neg (a : ℤ) (h_neg : a < 0) : a ≤ a / 2 := by
  have h_two_pos : (0 : ℤ) < 2 := by norm_num
  have h_div_nonpos : a / 2 ≤ 0 := Int.div_nonpos_of_neg_of_pos h_neg h_two_pos
  have h_div_ge_a : a ≤ a / 2 := by
    rw [Int.le_div_iff_mul_le h_two_pos]
    linarith
  exact h_div_ge_a

/-! ## Absolute value inequalities -/

lemma int_natAbs_le_of_le_of_neg_le (a b : ℤ) (h1 : a ≤ b) (h2 : -b ≤ a) :
  Int.natAbs a ≤ Int.natAbs b := by
  rw [Int.natAbs_le_natAbs_iff]
  exact ⟨h2, h1⟩

lemma int_natAbs_div_le (a : ℤ) : Int.natAbs (a / 2) ≤ Int.natAbs a := by
  cases Int.le_total 0 a with
  | inl h_nonneg =>
    rw [Int.natAbs_of_nonneg h_nonneg]
    rw [Int.natAbs_of_nonneg (Int.div_nonneg h_nonneg (by norm_num : (0 : ℤ) ≤ 2))]
    exact Int.coe_nat_div_le_coe_nat_of_le_mul_right (by norm_num : (1 : ℤ) ≤ 2) h_nonneg
  | inr h_neg =>
    have h_div_le : a ≤ a / 2 := int_div_le_self_of_neg a h_neg
         have h_div_ge : a / 2 ≥ a := by
       -- For negative a, a/2 is "less negative" so ≥ a
       exact int_div_le_self_of_neg a h_neg
    rw [Int.natAbs_le_natAbs_iff]
    constructor
    · exact h_div_le
    · linarith [h_div_ge]

/-! ## Comparison lemmas -/

lemma int_lt_of_natAbs_lt (a b : ℤ) (h : Int.natAbs a < Int.natAbs b) :
  a < b ∨ a > -b := by
  by_cases h_sign_a : 0 ≤ a
  · by_cases h_sign_b : 0 ≤ b
    · -- Both non-negative
      left
      rwa [Int.natAbs_of_nonneg h_sign_a, Int.natAbs_of_nonneg h_sign_b, Int.coe_nat_lt_coe_nat_iff] at h
    · -- a ≥ 0, b < 0
      right
      rw [Int.natAbs_of_nonneg h_sign_a, Int.natAbs_neg, Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos (le_of_lt h_sign_b))] at h
      rw [← Int.neg_neg b]
      rwa [Int.coe_nat_lt_coe_nat_iff] at h
  · by_cases h_sign_b : 0 ≤ b
    · -- a < 0, b ≥ 0
      left
      exact Int.lt_of_neg_of_pos h_sign_a h_sign_b
    · -- Both negative
      left
      have h_neg_a : a < 0 := not_le.mp h_sign_a
      have h_neg_b : b < 0 := not_le.mp h_sign_b
      rw [Int.natAbs_neg, Int.natAbs_neg] at h
      rw [Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos (le_of_lt h_neg_a))] at h
      rw [Int.natAbs_of_nonneg (Int.neg_nonneg_of_nonpos (le_of_lt h_neg_b))] at h
      rw [Int.coe_nat_lt_coe_nat_iff] at h
      linarith

/-! ## Specialized lemmas for moral curvature -/

lemma moral_balance_bound (balance : ℤ) (h_lower : -20 ≤ balance) (h_upper : balance ≤ 20) :
  balance / 2 ≥ -10 ∧ balance / 2 ≤ 10 := by
  constructor
  · -- Lower bound
    have h_div_mono : balance / 2 ≥ (-20) / 2 := Int.div_le_div_of_le_of_nonneg h_lower (by norm_num)
    simp at h_div_mono
    exact h_div_mono
  · -- Upper bound
    have h_div_mono : balance / 2 ≤ 20 / 2 := Int.div_le_div_of_le_of_nonneg h_upper (by norm_num)
    simp at h_div_mono
    exact h_div_mono

lemma educational_balance_bound (balance : ℤ) (h_edu_lower : -5 ≤ balance) (h_edu_upper : balance ≤ 25) :
  -5 ≤ balance ∧ balance ≤ 25 := by
  exact ⟨h_edu_lower, h_edu_upper⟩

end Recognition.Util.Arith
