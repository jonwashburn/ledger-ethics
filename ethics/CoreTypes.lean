/-
Ethics Core Types (Simplified)
===============================

Minimal type definitions for ethics.
-/

import RecognitionScience

namespace RecognitionScience.Ethics

/-- Energy value in arbitrary units -/
structure Energy where
  cost : Float

/-- Ledger entry representing a debit or credit -/
structure Entry where
  debit : Int
  credit : Int
  debit_bounded : Int.natAbs debit ≤ 100  -- Individual entries have bounded magnitude
  credit_bounded : Int.natAbs credit ≤ 100  -- Individual entries have bounded magnitude

/-- Minimal ledger state -/
structure LedgerState where
  entries : List Entry := []
  debits  : Int := 0
  credits : Int := 0
  balance : Int := debits - credits

namespace LedgerState

/-- Empty ledger is balanced -/
def empty : LedgerState := { entries := [], debits := 0, credits := 0, balance := 0 }

end LedgerState

/-- Time interval measured in ticks -/
structure TimeInterval where
  ticks : Nat

/-- Primary moral-state record -/
structure MoralState where
  ledger : LedgerState
  energy : Energy
  valid  : energy.cost > 0
  energy_sufficient : energy.cost > 300  -- Energy must be much larger than entry bounds (200)

/-- Positive energy constant -/
private def positive_energy : Energy := { cost := 500.0 }

/-- Proof that our energy is positive -/
private theorem positive_energy_valid : positive_energy.cost > 0 := by
  simp [positive_energy]; native_decide

/-- Proof that our energy is sufficient -/
private theorem positive_energy_sufficient : positive_energy.cost > 300 := by
  simp [positive_energy]; native_decide

/-- Convenience zero state -/
def MoralState.zero : MoralState :=
  { ledger := LedgerState.empty,
    energy := positive_energy,
    valid := positive_energy_valid,
    energy_sufficient := positive_energy_sufficient }

end RecognitionScience.Ethics
