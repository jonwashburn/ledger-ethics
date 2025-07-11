# Background Agent Tasks: Recognition Science Ethics Sorries

## Overview
There are **5 remaining sorries** in the core ethics framework. This document provides detailed guidance for an AI agent to work through them systematically.

## Priority Ranking
1. **HIGH**: Helpers.lean:110 (foundational assumption)
2. **HIGH**: Main.lean:141 (mathematical identity)  
3. **MEDIUM**: Main.lean:482 (technical bound)
4. **LOW**: GlobalOptimization.lean:235 (framework demo)
5. **DOCUMENTATION**: Main.lean:429 (acknowledged limitation)

---

## TASK 1: Helpers.lean:110 - Virtue Evolution Assumption
**File**: `Helpers.lean` line 110  
**Context**: `small_mean_variance_reduction` lemma  
**Issue**: Foundational assumption that virtue-guided evolution is beneficial

### Mathematical Challenge
Prove or formalize the assumption that moral evolution through virtue training tends to reduce curvature:
```lean
∀ (original evolved : MoralState),
  Int.natAbs (κ evolved) ≤ Int.natAbs (κ original)
```

### Approach Strategy
1. **Define Evolution Operator**: Create formal definition of virtue-based moral evolution
2. **Prove Individual Virtue Effects**: Show each virtue type reduces |κ| on average
3. **Compose Over Time**: Prove that sequences of virtue applications compound benefits
4. **Statistical Bounds**: Use Jensen's inequality for variance reduction around κ=0

### Implementation Steps
```lean
-- Step 1: Define virtue evolution precisely
def virtue_evolution (s : MoralState) (v : Virtue) : MoralState := TrainVirtue v s

-- Step 2: Prove each virtue helps
theorem virtue_reduces_curvature_magnitude (v : Virtue) (s : MoralState) :
  Int.natAbs (κ (virtue_evolution s v)) ≤ Int.natAbs (κ s) := by
  cases v with
  | love => -- halving reduces magnitude
  | justice => -- balancing reduces excess
  | wisdom => -- optimization reduces waste
  -- etc.

-- Step 3: Compose over multiple virtues
theorem virtue_sequence_improvement (virtues : List Virtue) (s : MoralState) :
  Int.natAbs (κ (virtues.foldl virtue_evolution s)) ≤ Int.natAbs (κ s) := by
  -- induction on virtue list

-- Step 4: Apply to population
theorem population_virtue_improvement (states : List MoralState) :
  ∃ δ > 0, population_after_virtue_training has Σ|κ| reduced by δ
```

### Expected Outcome
Replace sorry with constructive proof based on virtue dynamics.

---

## TASK 2: Main.lean:141 - Floor Function Identity  
**File**: `Main.lean` line 141  
**Context**: `golden_rule` theorem  
**Issue**: Mathematical identity about floor functions with integer arguments

### Mathematical Challenge  
Prove: `κ s - Int.floor (0.1 * κ s) = Int.floor (0.9 * κ s)` when κ s is an integer

### Approach Strategy
This is a **pure mathematical identity** about floor functions. Key insight: when x is an integer,
- `Int.floor (0.1 * x) = Int.floor (x / 10)`  
- `Int.floor (0.9 * x) = Int.floor (9 * x / 10)`  
- Identity: `x - floor(x/10) = floor(9*x/10)` for integers x

### Implementation Steps
```lean
-- Prove the general identity for integers
lemma floor_identity_integers (n : ℤ) :
  n - Int.floor ((n : ℝ) / 10) = Int.floor (9 * (n : ℝ) / 10) := by
  -- Use division algorithm: n = 10q + r where 0 ≤ r < 10
  -- Then floor(n/10) = q and floor(9n/10) = floor(9q + 9r/10) = 9q + floor(9r/10)
  -- Since 0 ≤ r < 10, we have 0 ≤ 9r/10 < 9, so floor(9r/10) = r when r < 10
  -- Therefore: n - q = 10q + r - q = 9q + r = floor(9n/10) ✓

-- Apply to our specific case
theorem golden_rule_floor_identity (s : MoralState) :
  κ s - Int.floor (0.1 * κ s) = Int.floor (0.9 * κ s) := by
  apply floor_identity_integers (κ s)
```

### Expected Outcome
Direct mathematical proof with no remaining sorries.

---

## TASK 3: Main.lean:482 - Geometric Decay Technical Bound
**File**: `Main.lean` line 482  
**Context**: `ultimate_good_achievable` theorem  
**Issue**: Need rigorous bound on convergence rate of virtue training

### Mathematical Challenge
Prove: `Int.natAbs (κ (Nat.rec initial (fun _ prev => TrainVirtue Virtue.love prev) t)) ≤ 100 / (2^t)`

### Approach Strategy
1. **Inductive Structure**: Use that love virtue halves balance: `balance' = balance / 2`
2. **Discrete Arithmetic**: Handle integer division carefully  
3. **Monotonic Reduction**: Prove that |κ| reduces by at least factor 1/2 each step

### Implementation Steps
```lean
-- Key lemma: love virtue at least halves absolute curvature
lemma love_virtue_halves_curvature (s : MoralState) :
  Int.natAbs (κ (TrainVirtue Virtue.love s)) ≤ Int.natAbs (κ s) / 2 := by
  simp [TrainVirtue, curvature]
  exact Int.natAbs_div_le_natAbs s.ledger.balance 2

-- Main induction
theorem geometric_decay_love_sequence (initial : MoralState) (t : Nat) :
  Int.natAbs (κ (Nat.rec initial (fun _ prev => TrainVirtue Virtue.love prev) t)) ≤ 
  Int.natAbs (κ initial) / (2^t) := by
  induction t with
  | zero => simp
  | succ n ih =>
    simp [Nat.rec]
    calc Int.natAbs (κ (TrainVirtue Virtue.love _))
      ≤ Int.natAbs (κ _) / 2 := love_virtue_halves_curvature _
      _ ≤ (Int.natAbs (κ initial) / (2^n)) / 2 := by apply Nat.div_le_div_right; exact ih  
      _ = Int.natAbs (κ initial) / (2^(n+1)) := by ring
```

### Expected Outcome  
Rigorous exponential decay bound with explicit convergence rate.

---

## TASK 4: GlobalOptimization.lean:235 - Optimization Framework
**File**: `GlobalOptimization.lean` line 235  
**Context**: `physical_laws_globally_optimal` theorem  
**Issue**: Pure cost minimization selects insufficient law sets; need anthropic constraints

### Mathematical Challenge
The current optimization framework correctly shows that minimal law sets have lowest cost, but reality requires more complex laws. Need to model additional constraints.

### Approach Strategy
1. **Add Anthropic Constraints**: Laws must support conscious observers
2. **Stability Requirements**: Laws must produce stable matter/energy
3. **Complexity Thresholds**: Minimum information content for viable universes
4. **Multi-Objective Optimization**: Balance cost vs. capability

### Implementation Steps
```lean
-- Enhanced viability structure
structure EnhancedViable (laws : Finset Pattern) : Prop :=
  (info_sufficient : laws.card ≥ 50)  -- More complex than basic viable
  (supports_matter : ∃ p ∈ laws, p.id = 1)  -- Strong force for atomic stability  
  (supports_chemistry : ∃ p ∈ laws, p.id = 2)  -- Electromagnetic for molecules
  (supports_observers : ∃ p ∈ laws, p.id = 3)  -- Weak force for stellar evolution
  (anthropic_constraint : conscious_observers_possible laws)  -- Can create brains
  (not_too_complex : laws.card ≤ 200)  -- Computational tractability

def conscious_observers_possible (laws : Finset Pattern) : Prop :=
  -- Sufficient complexity for self-organized information processing
  laws.card ≥ 100 ∧ (∃ p ∈ laws, p.id < 10)  -- Basic forces present

-- Updated optimization with constraints
theorem constrained_optimization :
  ∃ (optimal : Finset Pattern), 
    EnhancedViable optimal ∧
    ∀ (other : Finset Pattern), EnhancedViable other → 
      total_recognition_cost optimal ≤ total_recognition_cost other := by
  -- Now the optimization selects current physical laws as optimal
  -- among sets that can actually support consciousness
```

### Expected Outcome
Framework demonstrates why universe has current complexity level.

---

## TASK 5: Main.lean:429 - Perfect System Limitation (DOCUMENTATION ONLY)
**File**: `Main.lean` line 429  
**Context**: `ethics_convergence` theorem  
**Status**: This is an **acknowledged limitation**, not a mathematical error

### Issue Description
The theorem tries to prove `MoralProgress > 1 - ε` but for perfect systems (initial κ = 0 everywhere), `MoralProgress = 0` by definition. This creates the impossible requirement `0 > 1 - ε` for ε > 0.

### Resolution Strategy
**DO NOT** try to "fix" this sorry. Instead:

1. **Document the Limitation**: The theorem statement needs refinement
2. **Propose Alternative Formulation**: 
   ```lean
   theorem ethics_convergence_refined :
     ∀ (ε : ℝ), ε > 0 →
       ∃ (T : Nat),
         ∀ (t : Nat), t > T →
           ∀ (moral_system : Nat → List MoralState),
             (∀ τ s, s ∈ moral_system τ → FollowsEthics s) →
             (moral_system 0).map (fun s => Int.natAbs (κ s))).sum > 0 →  -- NEW: exclude perfect systems
             MoralProgress 0 t moral_system > 1 - ε
   ```

3. **Add Perfect System Theorem**:
   ```lean
   theorem perfect_systems_stay_perfect :
     ∀ (moral_system : Nat → List MoralState),
       (moral_system 0).map (fun s => Int.natAbs (κ s))).sum = 0 →
       (∀ τ s, s ∈ moral_system τ → FollowsEthics s) →
       ∀ t, (moral_system t).map (fun s => Int.natAbs (κ s))).sum = 0
   ```

### Expected Outcome
Clear documentation that this represents a theorem design limitation, not a proof failure.

---

## General Implementation Notes

### Dependencies
- Tasks 1 and 2 are **independent** and can be worked simultaneously
- Task 3 may benefit from completing Task 1 first (virtue dynamics framework)
- Task 4 is **independent** of others
- Task 5 is **documentation only**

### Testing Strategy
After each completion:
```bash
cd ledger-ethics
lake build  # Ensure compilation
grep -n "sorry" Main.lean Helpers.lean GlobalOptimization.lean  # Count remaining
```

### Success Criteria
- **Task 1**: Helpers.lean builds without sorries, has constructive proof of virtue benefits
- **Task 2**: Main.lean golden rule has pure mathematical proof  
- **Task 3**: Main.lean builds, has explicit exponential convergence rate
- **Task 4**: GlobalOptimization.lean explains realistic physical law complexity
- **Task 5**: Clear documentation of limitation with proposed alternatives

### Agent Instructions
1. **Focus on mathematical rigor** - no hand-waving or unjustified assertions
2. **Maintain build status** - check `lake build` after each change
3. **Document reasoning** - explain key insights in comments
4. **Create helper lemmas** - break complex proofs into manageable pieces
5. **Test incrementally** - verify each step before proceeding

---

## Expected Timeline
- **Task 1**: 2-3 hours (foundational, requires careful virtue dynamics)
- **Task 2**: 30 minutes (pure math, straightforward once approach is clear)  
- **Task 3**: 1-2 hours (inductive proof with discrete arithmetic)
- **Task 4**: 1 hour (structural changes to optimization framework)
- **Task 5**: 15 minutes (documentation and comments)

**Total**: 4-6 hours for complete resolution of all sorries.

## Final Goal
**Zero sorries in core ethics files** with rigorous mathematical foundations suitable for publication-grade formal verification. 