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

/-- Minimal ledger state -/
structure LedgerState where
  entries : List Entry := []
  debits  : Int := 0
  credits : Int := 0
  balance : Int := debits - credits

namespace LedgerState

/-- Empty ledger is balanced -/
def empty : LedgerState := ⟨[], 0, 0, 0⟩

end LedgerState

/-- Time interval measured in ticks -/
structure TimeInterval where
  ticks : Nat

/-- Primary moral-state record -/
structure MoralState where
  ledger : LedgerState
  energy : Energy
  valid  : energy.cost > 0

/-- Convenience zero state -/
def MoralState.zero : MoralState :=
  { ledger := LedgerState.empty,
    energy := { cost := 1 },
    valid := by sorry }

end RecognitionScience.Ethics
