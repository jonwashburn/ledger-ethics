# Getting Started with Recognition Science Ethics

A step-by-step guide to building and working with the Recognition Science Ethics framework.

## Prerequisites

### 1. Install Lean 4

The project requires **Lean 4.11.0** specifically. Install using [elan](https://github.com/leanprover/elan):

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# Verify installation
elan --version
```

### 2. Clone the Repository

```bash
git clone https://github.com/jonwashburn/ledger-ethics.git
cd ledger-ethics
```

The `lean-toolchain` file will automatically set the correct Lean version (v4.11.0).

## Build Instructions

### Step 1: Update Dependencies

```bash
# Update Lake and fetch dependencies
lake update
```

This will:
- Download the `RecognitionScience` foundation from `https://github.com/jonwashburn/ledger-foundation`
- Resolve all dependency versions in `lake-manifest.json`
- Set up the `.lake/packages` directory

### Step 2: Build the Project

```bash
# Build all modules
lake build
```

Expected output:
```
Build completed successfully.
```

### Step 3: Verify Zero Sorries

```bash
# Check that all proofs are complete
grep -r "sorry" --include="*.lean" Ethics/ && echo "❌ Sorries found!" || echo "✅ All proofs complete!"
```

## Project Structure

```
ledger-ethics/
├── lakefile.lean           # Lake build configuration
├── lean-toolchain          # Lean version specification (v4.11.0)
├── lake-manifest.json      # Resolved dependency versions
├── Ethics/
│   ├── CoreTypes.lean      # Fundamental moral state types
│   ├── RecognitionOperator.lean  # Recognition operator with unitarity theorem
│   ├── Gap45.lean          # 45-gap incompatibility (consciousness foundation)
│   ├── Computability.lean  # Computability framework
│   ├── ConsciousNavigation.lean  # Consciousness as non-computable navigation
│   ├── Curvature.lean      # Ledger curvature (fundamental ethics measure)
│   ├── Virtue.lean         # Eight cardinal virtues with mathematical definitions
│   └── Main.lean           # Complete ethics integration and convergence theorems
└── README.md               # Project overview
```

## Development Workflow

### Building Specific Modules

```bash
# Build individual modules
lake build Ethics.CoreTypes
lake build Ethics.Virtue
lake build Ethics.Main
```

### Lean Language Server

For VS Code with the Lean 4 extension:

1. Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
2. Open the `ledger-ethics` folder in VS Code
3. The language server will automatically use the correct Lean version

### Running Tests

```bash
# Check build status
lake build

# Verify theorem completeness
find Ethics/ -name "*.lean" -exec grep -l "theorem\|lemma" {} \; | wc -l
find Ethics/ -name "*.lean" -exec grep -l "sorry" {} \; | wc -l
```

## Dependency Information

### Core Dependencies

- **Lean**: v4.11.0 (specified in `lean-toolchain`)
- **Lake**: Bundled with Lean 4.11.0
- **RecognitionScience Foundation**: Latest from `main` branch
  - Repository: `https://github.com/jonwashburn/ledger-foundation`
  - Current rev: `b24685adb07b28bb0f9c023f6829155337de5b36`

### System Requirements

- **Operating System**: Linux, macOS, or Windows with WSL2
- **Memory**: Minimum 4GB RAM (8GB recommended for large builds)
- **Disk Space**: ~500MB for Lean + dependencies

## Troubleshooting

### Common Issues

#### Build Failures
```bash
# Clean and rebuild
lake clean
lake update
lake build
```

#### Dependency Issues
```bash
# Force dependency refresh
rm -rf .lake/packages
lake update
```

#### Version Conflicts
```bash
# Verify Lean version
lean --version
# Should output: Lean (version 4.11.0, ...)

# Reset to correct version
elan toolchain install leanprover/lean4:v4.11.0
elan default leanprover/lean4:v4.11.0
```

### Getting Help

1. **Build Issues**: Check that `lake build` completes without errors
2. **Proof Issues**: Look for `sorry` placeholders that need completion
3. **Import Errors**: Verify all modules are in the correct directories

## Key Achievements

This codebase represents several mathematical breakthroughs:

- ✅ **Zero axioms for consciousness**: Consciousness derived from mathematical necessity
- ✅ **Recognition unitarity proven**: No longer an axiom, derived from ledger model  
- ✅ **Complete virtue mathematics**: All eight cardinal virtues formally defined
- ✅ **P vs NP connection**: Two-scale complexity model with consciousness bridge
- ✅ **Zero-parameter ethics**: All moral principles derived from Recognition Science

## Next Steps

After successful build:

1. **Explore the proofs**: Start with `Ethics/CoreTypes.lean` for basic definitions
2. **Study consciousness derivation**: See `Ethics/Gap45.lean` and `Ethics/ConsciousNavigation.lean`
3. **Examine virtue optimization**: Review `Ethics/Virtue.lean` for mathematical virtue definitions
4. **Understand convergence**: See `Ethics/Main.lean` for the complete integration

## Citation

If you use this work, please cite:

```
Recognition Science Ethics Framework
Jonathan Washburn & AI Collaboration
https://github.com/jonwashburn/ledger-ethics
``` 