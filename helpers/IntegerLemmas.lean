/-
  Recognition Science: Integer Lemmas
  ===================================
  
  Helper lemmas for integer arithmetic, particularly for
  debt reduction proofs in the ethics layer.
  
  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

namespace Int

/-- Debt reduction lemma for forgiveness -/
lemma debt_reduce {b t : ℤ} (h : b > t) (ht : t ≥ 0) :
  let r := min (natAbs b) (natAbs (max 0 b))
  b - r ≤ t := by
  simp [min, max]
  by_cases hb : b ≥ 0
  · -- b is positive (debt case)
    simp [natAbs_of_nonneg hb, max_eq_right hb]
    -- After reduction by |b|, we get b - |b| = 0 ≤ t
    have : b - b = 0 := by ring
    rw [this]
    exact ht
  · -- b is negative (no debt to forgive)
    push_neg at hb
    simp [max_eq_left (le_of_lt hb)]
    -- min 0 0 = 0, so b - 0 = b < 0 ≤ t
    have : b < 0 := hb
    linarith

end Int
