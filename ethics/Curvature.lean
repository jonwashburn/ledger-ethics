/-
Recognition Science: Ethics - Curvature
=======================================

This module defines ledger curvature as the fundamental measure of moral state.
-/

import Ethics.CoreTypes

namespace RecognitionScience.Ethics

/-- Curvature measures the total unpaid recognition cost -/
def curvature (s : MoralState) : Int := s.ledger.balance

/-- Notation for curvature -/
notation "κ" => curvature

/-- Zero curvature defines the good -/
def isGood (s : MoralState) : Prop := κ s = 0

/-- Positive curvature is suffering -/
def suffering (s : MoralState) : Nat := Int.natAbs (max (κ s) 0)

/-- Negative curvature is joy/surplus -/
def joy (s : MoralState) : Nat := Int.natAbs (min (κ s) 0)

/-- Good states have no suffering -/
theorem good_no_suffering (s : MoralState) : isGood s → suffering s = 0 := by
  intro hgood
  simp [suffering, isGood, curvature] at hgood ⊢
  rw [hgood]
  rfl

/-- Good states have no joy -/
theorem good_no_joy (s : MoralState) : isGood s → joy s = 0 := by
  intro hgood
  simp [joy, isGood, curvature] at hgood ⊢
  rw [hgood]
  rfl

/-- A moral transition between states -/
structure MoralTransition (s₁ s₂ : MoralState) where
  duration : TimeInterval
  energyCost : s₂.energy.cost ≥ s₁.energy.cost - Float.ofNat duration.ticks

/-- Virtuous transitions reduce curvature -/
def isVirtuous {s₁ s₂ : MoralState} (_ : MoralTransition s₁ s₂) : Prop := κ s₂ ≤ κ s₁

/-- Curvature represents accumulated recognition debt -/
theorem curvature_as_debt (s : MoralState) : κ s = s.ledger.debits - s.ledger.credits :=
  by simp [curvature]

end RecognitionScience.Ethics
