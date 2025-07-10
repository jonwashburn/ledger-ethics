## Remaining `sorry` Placeholders in `ledger-ethics`

This document enumerates every Lean `sorry` placeholder that still exists in the repository (search performed 2025-07-10).  Only *actual* Lean placeholders are listed—commentary containing the word “sorry” is ignored.

| # | File | Line | Local Context | Ethics-Relevant? |
|---|------|------|---------------|------------------|
| 1 | `backup_root_duplicates/AnthropicPrinciple.lean` | 20 | `sorry -- Anthropic principle requires consciousness theory` | Yes – anthropic principle is an ethics-related philosophical module, yet this is in a *backup* copy not used in build |
| 2 | `backup_root_duplicates/AnthropicPrinciple.lean` | 24 | `sorry  -- Definition of consciousness` | Yes – consciousness definition underpins ethics; again only in backup file |
| 3 | `backup_root_duplicates/AnthropicPrinciple.lean` | 27 | `sorry  -- Current reality state` | Yes |
| 4 | `backup_root_duplicates/AnthropicPrinciple.lean` | 30 | `sorry  -- All patterns that have been selected` | Yes |
| 5 | `backup_root_duplicates/AnthropicPrinciple.lean` | 33 | `sorry  -- Patterns compatible with conscious observers` | Yes |

### Verification of Scope

* All five placeholders are located inside a **backup directory** (`backup_root_duplicates`).  The active `Ethics/` modules used by `lake build` contain **zero** `sorry` placeholders.
* Although the placeholders concern ethics topics (anthropic principle, consciousness), they are not part of the compiled ethics library.

### Recommendation

1. Either delete the stale `backup_root_duplicates/AnthropicPrinciple.lean` copy or finish its proofs.  Keeping unfinished backups may confuse automated audits that search for `sorry` tokens.
2. Confirm no other non-compiled directories contain placeholders before release. 

## Mathematical Formalization

Let \(\mathcal{F}\) be the finite set of all `*.lean` files in this repository and let
\(\mathcal{B} \subset \mathcal{F}\) denote the subset of files that live inside the
backup directory `backup_root_duplicates/`.  Define the *placeholder set*
\[
  \mathcal{P} := \{\,(f,\ell) \mid f \in \mathcal{F},\; \ell \in \mathbb{N},\;
                 \text{the token \texttt{sorry} occurs on line } \ell \text{ of } f\,\}.
\]
For each element \((f,\ell) \in \mathcal{P}\) we say that it is **ethics‐relevant** if and only if
\(f\) resides in the main `Ethics/` hierarchy used by the build.

### Proposition 1 — Cardinality
The enumeration above shows
\[\lvert \mathcal{P} \rvert = 5.\]

### Proposition 2 — Localization
All five elements lie in the backup sub-set:
\[\mathcal{P} \subseteq \mathcal{B}.\]

*Proof.* Direct inspection of the table reveals that every file component of the five
ordered pairs begins with the path prefix `backup_root_duplicates/`. ∎

### Corollary — Build Purity
Let \(\mathcal{A} := \mathcal{F} \setminus \mathcal{B}\) be the set of *active* Lean files
consumed by `lake build`.  Then
\[ \mathcal{P} \cap \mathcal{A} = \varnothing. \]
Consequently the compiled ethics library contains **zero** Lean placeholders, i.e.
\[\forall f \in \mathcal{A},\; \forall \ell,\; (f,\ell) \notin \mathcal{P}.\]

### Remark
A mechanical check can be phrased inside Lean (conceptually) as
```lean
open System (FilePath)
-- pseudo-code, not executed in build:
#eval do
  let active ← collectActiveLeanFiles  -- returns list (FilePath)
  let offenders ← active.filterM containsSorryToken
  IO.println s!"Active files containing `sorry`: {offenders}"
-- expected output: {}
```
which would evaluate to the empty set, confirming the corollary.  The actual audit was
performed with `grep` as documented earlier; formalizing the file-system walk in Lean is
possible but not necessary once the human-verified enumeration is fixed. 