/-
  Finite Extensions
  [Derivation §8.1 – Core Finite Scaffolding]
  
  Extensions to replace arithmetic axioms in RecognitionScience.Core.Finite.
  These will be proved with native_decide in PR-A per the derivation roadmap.
-/

import RecognitionScience

namespace RecognitionScience.Core

/-- Positive naturals are non-zero. -/ 
@[simp] theorem nat_pos_of_ne_zero_proof (n : Nat) (h : n ≠ 0) : 0 < n := by
  exact Nat.pos_of_ne_zero h

/-- All `Fin 3` cases of `<` and `≤` are decidable by `native_decide`. -/
@[simp] theorem fin3_lt_cases (a b : Fin 3) : Decidable (a < b) := by
  native_decide

/-- All `Fin 3` cases of `≤` are decidable. -/
@[simp] theorem fin3_le_cases (a b : Fin 3) : Decidable (a ≤ b) := by
  native_decide

end RecognitionScience.Core
