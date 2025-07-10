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
  -- If κ s = 0, then max (κ s) 0 = 0, so Int.natAbs 0 = 0
  simp [suffering, isGood] at hgood ⊢; rw [hgood]; simp

/-- Good states have no joy -/
theorem good_no_joy (s : MoralState) : isGood s → joy s = 0 := by
  intro hgood
  -- If κ s = 0, then min (κ s) 0 = 0, so Int.natAbs 0 = 0
  simp [joy, isGood] at hgood ⊢; rw [hgood]; simp

/-- A moral transition between states -/
structure MoralTransition (s₁ s₂ : MoralState) where
  duration : TimeInterval
  energyCost : s₂.energy.cost ≥ s₁.energy.cost - Float.ofNat duration.ticks

/-- Virtuous transitions reduce curvature -/
def isVirtuous {s₁ s₂ : MoralState} (t : MoralTransition s₁ s₂) : Prop := κ s₂ ≤ κ s₁

/-- Curvature represents accumulated recognition debt -/
theorem curvature_as_debt (s : MoralState) : κ s = s.ledger.debits - s.ledger.credits := by
  -- This follows from proper ledger maintenance
  simp [curvature]; rfl

end RecognitionScience.Ethics
