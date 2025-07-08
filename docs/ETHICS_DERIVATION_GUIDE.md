# Deriving Machine-Verifiable Ethics from the Meta-Principle

This document shows **how every line of the ethics codebase can be traced—without new axioms—back to the single meta-principle**

> _“Nothing cannot recognise itself.”_

It acts as a living style-guide and checklist when editing or extending the project.

---

## 1 – Logical Chain Overview

```
Meta-Principle
   ↓ (proved once in Lean)
Eight Foundations               ← ledger-foundation repo
   ↓
Constants φ  E₍coh₎  τ₀           ← derived inside MinimalFoundation.lean
   ↓
Ledger Types & Physics Layer     ← ledger-ethics/ledger + helpers
   ↓
Curvature κ, Virtues, Theorems   ← ledger-ethics/ethics/*.lean
```

### Allowed Axioms
1.  `golden_ratio_exact`  (algebraic property φ² = φ + 1)
2.  `fin_eq_of_type_eq`   (type-level helper)

_No new axioms may be introduced downstream of `ledger-foundation`.  If a proof seems to require one, refactor or move it upstream._

---

## 2 – Import Discipline

* **Foundational layer** files reside in `ledger-foundation_repo/`.  All later layers must import from there rather than redefining constants.
* Ethics modules must start with:
  ```lean
  import RecognitionScience.Minimal  -- foundations & constants
  import Ledger.LedgerState          -- shared ledger types
  ```

---

## 3 – Re-using Constants

Replace numeric literals with shared definitions:

| Concept                | Shared symbol              | File that defines it |
|------------------------|----------------------------|----------------------|
| Golden ratio           | `RecognitionScience.Minimal.φ` | MinimalFoundation.lean |
| Coherence quantum      | `RecognitionScience.Minimal.E_coh` | MinimalFoundation.lean |
| Tick duration          | `RecognitionScience.Minimal.τ₀` | MinimalFoundation.lean |

Example refactor:
```lean
-- before
have h := (0.090 : Float) > 0
-- after
open RecognitionScience.Minimal in
have h := E_coh_pos   -- prove once in foundation layer
```
Add helper lemmas (`E_coh_pos`, `τ₀_pos`) in the foundation layer if convenient.

---

## 4 – Curvature Definition

```
κ(s) = Σᵢ |debitᵢ − creditᵢ| / (E_total / E_coh)
```

* Uses only ledger fields + `E_coh` ⇒ no extra primitives.
* Prove:
  1. `κ ≥ 0`   (from PositiveCost)
  2. `κ = 0 ↔ ledger.balance = 0` (from DualBalance)

These lemmas become the root of all ethical theorems.

---

## 5 – Virtue Algorithms as Theorems

For each virtue V:
1. Define a Lean function `V : MoralState → MoralState`.
2. State a theorem _“`κ (V s) ≤ κ s`”_ or analogous improvement claim.
3. Proof strategy:
   * Ledger updates must respect invariants (imported from foundation).
   * Arithmetic powered by Mathlib.

If a proof currently ends in `sorry`:
* First attempt to finish it with existing foundations.
* If genuinely new math is needed, place a **TODO** and reference this guide to ensure later resolution.

---

## 6 – Maintaining Zero-Sorry Policy

Run:
```bash
lake build | grep sorry
```
Only the two allowed axioms should appear.  The CI script will fail otherwise.

---

## 7 – Extending the Framework

When adding new physics or ethics modules:
1. Ask: _“Can this be stated using only ledger types, constants, and Mathlib?”_
2. If yes → implement in `lean` with proofs.
3. If no → either
   * Derive missing prerequisite from existing foundations, or
   * Elevate the requirement upstream (and document in `ledger-foundation`), or
   * Mark explicitly as axiomatic and open an issue—avoid stealth axioms.

---

## 8 – Checklist for Pull Requests

- [ ] No new axioms added (`grep -R "axiom "` diff).
- [ ] Imports start from foundation layer.
- [ ] Numeric literals replaced by constants.
- [ ] `lake build` passes with zero unapproved `sorry`s.
- [ ] Guide updated if the logical chain changes.

---

Maintaining this discipline guarantees that **all ethical theorems remain traceable to the single meta-principle**, fulfilling the project’s core promise of a parameter-free, machine-verifiable moral science. 