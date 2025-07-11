/-
Recognition Science: Ethics - Hello World
=========================================

Simple test module to verify that the dependency structure works.
-/

import RecognitionScience

namespace RecognitionScience.Ethics

open RecognitionScience

-- Test that we can access foundation definitions
#check φ
#check E_coh
#check Foundation1_DiscreteTime

-- Simple ethics definition
noncomputable def ethicalConstant : Float := φ

-- Simple theorem using foundation
theorem ethics_uses_phi : ethicalConstant > 1 := by
  simp [ethicalConstant]
  exact RecognitionScience.Minimal.φ_positive

end RecognitionScience.Ethics
