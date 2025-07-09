# Background Agent Task List

**Branch:** `background-agent-proofs`  
**Base Repo:** `https://github.com/jonwashburn/ledger-ethics.git`  
**Working Directory:** `/Users/jonathanwashburn/Desktop/Ethics/ledger-ethics`  

---

## 🎯 **Mission: Eliminate 51 Sorry Statements**

Follow the roadmap in `docs/DERIVATION_FROM_NCOI.md` Section 8.

### ✅ **PHASE 1: Easy Mathlib Proofs** (Target: -8 sorries)

**Priority: HIGH** - These can be filled immediately with mathlib lemmas.

1. **Fix `Ethics/HelperStubs.lean`:**
   ```lean
   -- Line 15: Replace sorry with proof
   theorem helper_trivial_bound : ∀ n : Nat, n ≥ 0 := by
     intro n
     exact Nat.zero_le n
   
   -- Line 18: Replace sorry with mathlib result  
   theorem global_opt_exists_minimum : ∀ (S : Finset ℕ), S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, m ≤ x := by
     intro S h
     exact S.exists_min_image id h
   ```

2. **Complete `Ethics/Ledger/Proofs.lean`:**
   - `balance_apply_stub`: ✅ DONE (algebraic proof)
   - `energy_apply_stub`: Need to complete energy conservation proof

3. **Finish `Ethics/FiniteExtensions.lean`:**
   - All finite case proofs with `fin_cases` and `decide`

4. **Fix discrete bounds in `Helpers.lean`:**
   - `discrete_mean_approximation`: ✅ DONE (40-line proof)
   - `small_mean_variance_reduction`: Fill with statistical bounds

### 🔶 **PHASE 2: Medium Setup Required** (Target: -15 sorries)

**Priority: MEDIUM** - Require framework setup but use standard mathlib.

5. **Geometric Decay Framework:**
   ```lean
   -- Need: decay_rate < 1 assumption
   theorem decay_summable : Summable (fun n => virtue_strength n) := by
     apply Summable.of_norm_bounded_eventually_of_summable
     -- Use geometric series summability
   
   theorem decay_limit_zero : tendsto virtue_strength atTop (𝓝 0) := by
     apply tendsto_zero_of_summable
     exact decay_summable
   ```

6. **Curvature Convexity:**
   - Set up convex combination framework for moral states
   - Use Jensen's inequality from mathlib
   - Prove subdifferential existence

7. **Global Optimization:**
   - Set up `PhysicalLaws` as finite type
   - Use `Finset.exists_min_image` for optimization
   - Prove convergence with epsilon-delta

### ❌ **PHASE 3: Theory Development** (Target: -28 sorries)

**Priority: LOW** - Requires substantial new theory.

8. **Observer Formalism** (use scaffolding in `Ethics/Observer.lean`)
9. **Anthropic Principle** (requires consciousness theory)
10. **Energy Conservation** (physics derivation from ledger algebra)

---

## 🛠 **Development Workflow**

### Commands to Start:
```bash
cd /Users/jonathanwashburn/Desktop/Ethics/ledger-ethics
git checkout background-agent-proofs
git pull origin background-agent-proofs
lake build  # Verify starting state
```

### Work Pattern:
1. **Pick ONE file from Phase 1**
2. **Replace 1-3 sorries with proofs**
3. **Test:** `lake build`
4. **Commit:** `git add -A && git commit -m "prove: specific_theorem_name"`
5. **Push:** `git push origin background-agent-proofs`
6. **Repeat**

### Rules:
- ✅ **DO**: Use mathlib lemmas extensively  
- ✅ **DO**: Keep proofs < 20 lines each  
- ✅ **DO**: Reference `[Derivation §X]` in comments  
- ❌ **DON'T**: Create new axioms  
- ❌ **DON'T**: Use `sorry` in new code  
- ❌ **DON'T**: Break existing proofs  

### Safety Checks:
- Always `lake build` before committing
- Keep each commit focused on 1-3 related theorems
- Add `-- [Background Agent - DATE]` comment to modified files

---

## 📊 **Progress Tracking**

| Phase | Target | Current | Remaining |
|-------|--------|---------|-----------|
| Phase 1 | -8 | 0 | 8 |
| Phase 2 | -15 | 0 | 15 |  
| Phase 3 | -28 | 0 | 28 |
| **Total** | **-51** | **0** | **51** |

### Current Sorry Count: 51
```bash
# Check progress:
grep -rn "\bsorry\b" --include="*.lean" . | grep -v "Legacy" | grep -v "\.lake" | wc -l
```

---

## 🎁 **Expected Outcomes**

After Phase 1 completion:
- 8 fewer sorries (43 remaining)  
- All trivial mathlib results proved
- Clean foundation for Phase 2
- Merge-ready PR for main branch

**Start with `Ethics/HelperStubs.lean` line 15!** 🚀
