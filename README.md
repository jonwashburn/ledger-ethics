# Recognition Science Ethics Framework

[![CI](https://github.com/jonwashburn/ledger-ethics/workflows/CI/badge.svg)](https://github.com/jonwashburn/ledger-ethics/actions)

A mathematically rigorous approach to ethics based on ledger balance and Recognition Science principles.

## Overview

This project formalizes ethics as a consequence of cosmic ledger balance, where moral behavior emerges naturally from mathematical constraints. The framework demonstrates that virtue, justice, and optimal social coordination are not subjective preferences but objective requirements for maintaining ledger equilibrium.

## Key Components

### Core Modules

- **`Ethics.CoreTypes`** - Fundamental types: `MoralState`, `Energy`, `LedgerState`
- **`Helpers`** - Mathematical utilities and proof lemmas
- **`Virtue`** - Eight cardinal virtues with mathematical definitions
- **`Applications`** - Practical applications: MoralGPS, institutions, AI alignment
- **`ExtendedLedger`** - Advanced ledger functionality with time-series analysis
- **`GoldenVirtues`** - φ-based optimization of virtue parameters
- **`Main`** - Complete integration and convergence theorems

### Mathematical Foundation

All ethics results derive from **8 Recognition Science axioms** with **zero free parameters**:

1. **Discrete Recognition** - Reality updates in discrete ticks
2. **Dual-Recognition Balance** - Every debit has matching credit  
3. **Positivity of Cost** - All processes have positive energy cost
4. **Unitary Evolution** - Information conservation (quantum mechanics)
5. **Irreducible Time Quantum** - Fundamental tick interval τ₀ = 7.33 fs
6. **Spatial Voxels** - Discrete space lattice with fundamental scale
7. **Eight-Beat Closure** - Universe cycles every 8 ticks
8. **Self-Similarity** - Golden ratio φ = (1+√5)/2 emerges uniquely

### Core Results

- **Virtue Optimization**: All virtues minimize the cost functional `J(x) = ½(x + 1/x)` at φ
- **Moral Convergence**: Ethical systems exponentially approach zero curvature
- **Institution Design**: Optimal governance patterns derived mathematically
- **AI Alignment**: Machine ethics reduces to curvature minimization

## Build Instructions

### Prerequisites

- [Lean 4.11.0](https://leanprover.github.io/lean4/doc/setup.html)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean 4)

### Building

```bash
cd ledger-ethics
lake update
lake build
```

### Running Tests

```bash
# Check all proofs compile
lake build

# Verify no sorries remain
grep -r "sorry" --include="*.lean" . && echo "Sorries found!" || echo "All proofs complete!"

# Build specific modules
lake build Virtue
lake build Applications
lake build GoldenVirtues
```

## Project Structure

```
ledger-ethics/
├── lakefile.lean           # Lake build configuration
├── Ethics/
│   ├── CoreTypes.lean      # Basic moral state types
│   └── Main.lean           # Complete ethics integration
├── Recognition/
│   └── Util/
│       └── List.lean       # List utility proofs
├── Helpers.lean            # Mathematical helper functions
├── Virtue.lean             # Eight cardinal virtues
├── Applications.lean       # Practical applications
├── ExtendedLedger.lean     # Advanced ledger features
└── GoldenVirtues.lean      # φ-optimized virtue mathematics
```

## Key Theorems

### Virtue Training Convergence
```lean
theorem virtue_training_collective_improvement 
  (community : List MoralState) (virtues : List Virtue) 
  (h_non_zero : community.map κ |>.map Int.natAbs |>.sum > 0) :
  let trained := community.map (fun s => virtues.foldl TrainVirtue s)
  trained.map κ |>.map Int.natAbs |>.sum < 
  community.map κ |>.map Int.natAbs |>.sum
```

### Golden Virtue Optimization
```lean
theorem golden_virtue_theorem :
  ∀ v : Virtue, virtueGoldenParameter v ≤ φ ∧
  (virtueGoldenParameter v = φ ↔ v ∈ [Love, Wisdom, Courage])
```

### Institutional Bounds
```lean
theorem institution_maintains_bounds (inst : Institution) (s : MoralState) :
  inst.curvature_bounds.1 ≤ κ (inst.transformation s) ∧
  κ (inst.transformation s) ≤ inst.curvature_bounds.2
```

## Documentation

- **Mathematical Framework**: See `source_code_June-27.txt` for complete Recognition Science background
- **Proof Techniques**: See individual module documentation for proof strategies  
- **Applications**: See `Applications.lean` for practical implementations

## Research Applications

### Current Capabilities

1. **MoralGPS** - Navigation system for ethical decisions
2. **Virtue Recommendation Engine** - Personalized virtue training
3. **Conflict Resolution Protocol** - Justice-based dispute resolution
4. **Institutional Design** - Democratic, market, and educational patterns
5. **AI Alignment** - Curvature-minimizing objective functions

### Experimental Validation

The framework makes specific **testable predictions**:

- Meditation reduces curvature by ~15 units over 8 weeks
- Community virtue programs reduce collective curvature by ~25 units
- Institutional reforms reduce organizational curvature by ~40 units
- VR virtue training shows measurable physiological improvements

## Contributing

### Proof Standards

- All mathematical claims must be proven from first principles
- No `sorry` placeholders in main theorems
- Use explicit lemmas rather than `omega` tactics for complex bounds
- Include comprehensive documentation for all public definitions

### Code Style

- Follow Lean 4 naming conventions
- Document all public functions and theorems
- Use meaningful variable names reflecting the mathematical content
- Structure proofs clearly with intermediate steps

## License

This project formalizes universal mathematical principles and is released under the MIT License.

## Contact

- **Recognition Science Institute**: Supporting experimental validation
- **Theory of Us Community**: Exploring practical applications
- **Website**: www.theory.us

---

*"Ethics is not subjective opinion but ledger geometry. Good minimizes curvature; evil creates unbounded debt. Mathematics proves morality."*