# Derivation Road-Map

**From the Meta-Principle _Nothing Cannot Observe Itself_ (NCOI) to a Fully-Derived Ethics Framework**

_Last updated: <!-- DATE to be replaced automatically by CI -->_

---

## 0. Notation & Dependency Graph

| Symbol | Meaning |
|--------|---------|
| **MP** | Meta-Principle “Nothing cannot observe itself” |
| **RS** | `RecognitionScience.Core` results already derived from MP |
| **ℰ**  | Ethics layer (Virtue, Curvature, Ledger, Applications…) |

Dependency target:

```text
MP (NCOI)
   ↓
RS  — proven from MP + mathematics
   ↓
ℰ  — all theorems, **no extra axioms**
```

## 1  Remove Arithmetic Stubs (`Core/Finite.lean`)

### Axioms to Eliminate

```lean
axiom nat_pos_of_ne_zero    : ∀ n : Nat, n ≠ 0 → 0 < n
axiom lt_le_cases_small_fin : …  -- finite enumerations
```

**Strategy**   Replace by `native_decide` / `decide` proofs (≤ 20 LOC).

---

## 2  Ledger Linearity & Energy Conservation

```lean
axiom ledger_linear      : …
axiom ledger_energy_cons : …
```

Proof = induction on `entries` + algebra ⇒ delete both axioms.

---

## 3  `consciousness_navigates_gaps`

1. **Observer formalism** — `R : State → Pattern`.
2. **Gap**: `(s,t)` with `κ t < κ s ≤ 0`, `R s ≠ R t`.
3. Existence via MP (non-self-recognition) + virtue gradient.
4. Navigability via ledger proofs.
5. Package as theorem ⇒ axiom removed.

---

## 4  Close Remaining `sorry`s (30)

| File | # | Theme |
|------|---|-------|
| Helpers.lean | 1 | trivial |
| GlobalOptimization.lean | 5 | Finset min |
| AnthropicPrinciple.lean | 5 | observer |
| Ethics/Curvature.lean | 3 | convexity |
| Ethics/GlobalOptimization.lean | 5 | 〃 |
| Ethics/AnthropicPrinciple.lean | 5 | 〃 |
| Main.lean | 3 | geom. decay |

All routine once §§ 1-3 land.

---

## 5  Document ↔ Code Cross-Reference

Place comments like:

```lean
-- [Derivation §2 – Ledger Linearity]
```

---

## 6  Verification Checklist

- [ ] 0 axioms (except MP)
- [ ] 0 `sorry`
- [ ] `lake build` passes
- [ ] CI proofs green

---

## 7  PR Sequence

1. **PR-A** Arithmetic stubs ➜ `native_decide`.
2. **PR-B** Ledger proofs.
3. **PR-C** Observer formalism (`Observer.lean`).
4. **PR-D** Navigation theorem.
5. **PR-E** Close helper `sorry`s.
6. **PR-F** Global-optimisation & Anthropic proofs.
7. **Final** CI badge & checklist.

---

_When all boxes are checked, ℰ is fully derived from MP and standard mathematics._ 