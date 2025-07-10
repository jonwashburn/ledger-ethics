# Omega Elimination & Sorry Resolution Plan

## Executive Summary

**Total Omega Tactics**: 68 (across all files)  
**Active Ethics Files**: 4 omega tactics in core files (excluding Legacy)  
**Sorry Placeholders**: 11 (3 critical in Curvature.lean)  
**Priority**: High - these limit proof transparency and mathematical rigor

---

## 🎯 **Omega Tactics Analysis**

### Core Files (Priority 1 - Critical)

#### `Ethics/RecognitionOperator.lean` (4 instances)
```lean
Line 102: omega  # Period bound assertion
Line 131: omega  # Period constraint  
Line 182: omega  # Physical period limit
Line 187: omega  # Period boundary case
```

**Pattern**: All related to asserting `s.period ≤ 360` from physical constraints  
**Complexity**: Medium - requires proving period bounds from 8-beat physics  
**Strategy**: Derive explicit bound from recognition dynamics

#### `Ethics/Main.lean` (43 instances)
**Categories by Pattern**:

1. **Integer Sign Analysis** (Lines 73, 80, 88, 98, 108, 115, 122, 123, 128, 132)
   ```lean
   have : 0 ≤ a ∨ a < 0 := by omega
   have : -a < b := by omega
   ```
   **Strategy**: Replace with `Int.le_total`, `Int.lt_or_gt_of_ne`

2. **Arithmetic Bounds** (Lines 149, 157, 164, 185, 193, 241)
   ```lean
   exact ⟨by omega, hb, ha⟩
   omega  -- Arithmetic: s₂.balance + t > s₂.balance + t
   ```
   **Strategy**: Use `linarith` for linear inequalities

3. **Natural Number Inequalities** (Lines 440, 555, 565, 1468, 1783, 1791, 1816, 1823, 1883)
   ```lean
   have h_pos : 0 < n + 1 := by omega
   ```
   **Strategy**: Use `Nat.succ_pos`, `Nat.zero_lt_succ`

4. **Curvature Analysis** (Lines 1545, 1546, 1548, 1615, 1616, 1618, 1622, 1623)
   ```lean
   have h1 : κ s₁ < 0 := by omega
   ```
   **Strategy**: Explicit reasoning from curvature definitions

5. **Pattern Matching** (Lines 1650, 1655, 1663, 1767)
   ```lean
   | ofNat n => omega [h1_neg]
   ```
   **Strategy**: Case analysis with explicit contradictions

### Legacy Files (Priority 3 - Reference Only)
- `Ethics/Legacy/MainFull.lean`: 34 instances (mirror of Main.lean)
- **Action**: Keep for reference, focus on active Main.lean

---

## 🔧 **Replacement Strategies**

### Strategy 1: Integer Reasoning
```lean
-- Replace: have : 0 ≤ a ∨ a < 0 := by omega
-- With:
have : 0 ≤ a ∨ a < 0 := Int.le_total 0 a
```

### Strategy 2: Linear Arithmetic
```lean
-- Replace: omega
-- With:
linarith [h1, h2, h3]  -- Where h1, h2, h3 are relevant hypotheses
```

### Strategy 3: Natural Number Properties
```lean
-- Replace: have h_pos : 0 < n + 1 := by omega
-- With:
have h_pos : 0 < n + 1 := Nat.succ_pos n
```

### Strategy 4: Period Bounds (RecognitionOperator)
```lean
-- Replace: omega
-- With explicit proof:
have h_period_bound : s.period ≤ 360 := by
  -- 8-beat physics constrains practical periods
  have h_8beat : 8 ∣ s.period ∨ s.period < 8 * 45 := period_constraint s
  cases h_8beat with
  | inl h_div => exact Nat.dvd_mul_of_dvd_left h_div 45
  | inr h_lt => exact Nat.le_of_lt h_lt
```

### Strategy 5: Curvature Reasoning
```lean
-- Replace: have h1 : κ s₁ < 0 := by omega
-- With:
have h1 : κ s₁ < 0 := by
  simp [curvature]
  -- Use specific properties of s₁'s ledger state
  exact ledger_negative_balance_proof
```

---

## 🚨 **Sorry Resolution Plan**

### Critical Path (Priority 1)

#### `Ethics/Curvature.lean` (3 sorries)
```lean
Line 31:  sorry
Line 37:  sorry  
Line 50:  sorry
```

**Context**: These appear to be in energy transition proofs  
**Action Required**: 
1. Examine the specific contexts
2. Provide explicit constructions for energy bounds
3. Use energy conservation principles

#### `Ethics/MathematicalFoundations.lean` (5 sorries)
```lean
Line 104: sorry -- This is a standard result in computability theory
Line 127: sorry -- Would need uniform navigation property
Line 146: sorry -- Would need to formalize the connection
Line 164: Classical.choose (exists_short_path s (by simp; sorry))
Line 171: exact Classical.choose_spec (exists_short_path s (by simp; sorry))
```

**Strategy**: 
- Line 104: Import computability theory from mathlib
- Lines 127, 146: Formalize the connection explicitly
- Lines 164, 171: Prove `exists_short_path` directly

### Supporting Files (Priority 2)

#### `Ethics/AnthropicPrinciple.lean` (5 sorries)
```lean
Line 20: sorry -- Anthropic principle requires consciousness theory
Line 24: sorry -- Definition of consciousness  
Line 27: sorry -- Current reality state
Line 30: sorry -- All patterns that have been selected
Line 33: sorry -- Patterns compatible with conscious observers
```

**Strategy**: Link to consciousness theorem from ConsciousNavigation.lean

---

## 📋 **Implementation Plan**

### Phase 1: Core Omega Elimination (Week 1)
1. **RecognitionOperator.lean** - Replace 4 period-bound omegas
2. **Main.lean Integer Reasoning** - Replace 10 integer sign omegas
3. **Create helper lemmas** in Helpers.lean for common patterns

### Phase 2: Arithmetic Omega Elimination (Week 2)
1. **Main.lean Arithmetic** - Replace 15 arithmetic omegas with linarith
2. **Main.lean Natural Numbers** - Replace 9 Nat inequality omegas
3. **Test build continuously** to catch regressions

### Phase 3: Complex Omega Elimination (Week 3)
1. **Main.lean Curvature** - Replace 8 curvature analysis omegas
2. **Main.lean Pattern Matching** - Replace 4 pattern match omegas
3. **Comprehensive testing**

### Phase 4: Sorry Resolution (Week 4)
1. **Curvature.lean** - Resolve 3 critical sorries
2. **MathematicalFoundations.lean** - Resolve 5 computability sorries
3. **AnthropicPrinciple.lean** - Link to consciousness theorem

---

## 🔍 **Detailed File Analysis**

### `Ethics/Main.lean` Omega Categories

#### Integer Sign Analysis (10 instances)
**Pattern**: Determining whether integers are positive, negative, or zero
**Lines**: 73, 80, 88, 98, 108, 115, 122, 123, 128, 132
**Replacement**: Use Int.le_total, Int.lt_trichotomy

#### Arithmetic Proofs (6 instances)  
**Pattern**: Linear arithmetic inequalities
**Lines**: 149, 157, 164, 185, 193, 241
**Replacement**: Use linarith tactic with explicit hypotheses

#### Natural Number Properties (9 instances)
**Pattern**: Nat.succ properties, positivity
**Lines**: 440, 555, 565, 1468, 1783, 1791, 1816, 1823, 1883
**Replacement**: Use Nat.succ_pos, Nat.zero_lt_succ

#### Curvature Analysis (8 instances)
**Pattern**: Reasoning about κ s < 0, κ s > 0
**Lines**: 1545, 1546, 1548, 1615, 1616, 1618, 1622, 1623
**Replacement**: Explicit curvature definitions and ledger state analysis

#### Pattern Matching (4 instances)
**Pattern**: Int.ofNat vs Int.negSucc cases
**Lines**: 1650, 1655, 1663, 1767
**Replacement**: Explicit case analysis with contradiction proofs

---

## 🧪 **Testing Strategy**

### Continuous Verification
```bash
# After each omega replacement:
lake build                    # Verify compilation
lake build Ethics.Main        # Test specific module
grep -c "omega" Ethics/*.lean  # Track progress
```

### Regression Testing
```bash
# Verify no functionality loss:
lake build                     # Full build
grep -r "sorry" Ethics/*.lean  # Monitor sorry count
```

### Progress Tracking
- **Week 1**: Target 14 omegas eliminated (RecognitionOperator + Integer reasoning)
- **Week 2**: Target 29 omegas eliminated (Arithmetic + Nat properties)  
- **Week 3**: Target 41 omegas eliminated (Curvature + Pattern matching)
- **Week 4**: Target 11 sorries resolved

---

## 🎯 **Success Metrics**

- [ ] **Zero omega tactics** in core Ethics files
- [ ] **Zero sorry placeholders** in critical path (Curvature.lean)
- [ ] **Build passing** throughout the process
- [ ] **Proof transparency** - all reasoning explicit
- [ ] **Mathematical rigor** - no hidden automation

---

## 🛠 **Helper Lemmas to Create**

### `Ethics/Helpers.lean` Additions
```lean
-- Integer reasoning helpers
lemma int_sign_trichotomy (a : Int) : a < 0 ∨ a = 0 ∨ a > 0
lemma int_natAbs_cases (a : Int) : (∃ n : Nat, a = Int.ofNat n) ∨ (∃ n : Nat, a = Int.negSucc n)

-- Natural number helpers  
lemma nat_pos_of_succ (n : Nat) : 0 < n + 1 := Nat.succ_pos n
lemma nat_succ_ne_zero (n : Nat) : n + 1 ≠ 0 := Nat.succ_ne_zero n

-- Curvature helpers
lemma curvature_sign_from_balance (s : MoralState) : 
  s.ledger.balance < 0 ↔ κ s < 0
lemma curvature_pos_iff_suffering (s : MoralState) :
  κ s > 0 ↔ suffering s > 0

-- Period bound helpers (for RecognitionOperator)
lemma period_bounded_by_eightbeat (s : RecognitionState) :
  ¬Gap45 s → s.period ≤ 360
```

This comprehensive plan provides a systematic approach to eliminating all omega tactics while maintaining mathematical rigor and proof transparency. 