/-
  Ledger Apply Function
  [Derivation §8.2 – Ledger Scaffolding]

  Defines the basic operation of applying an entry to a ledger state.
-/

import Ethics.CoreTypes

namespace RecognitionScience.Ethics

open Int

/-- Apply a single entry to a ledger state. -/
@[simp] def apply (s : LedgerState) (e : Entry) : LedgerState :=
  { s with
    entries := e :: s.entries,
    debits  := s.debits  + e.debit,
    credits := s.credits + e.credit,
    balance := s.debits + e.debit - (s.credits + e.credit) }

end RecognitionScience.Ethics
