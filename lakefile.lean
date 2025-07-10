import Lake
open Lake DSL

package ledgerEthics where
  -- Basic settings for this ethics-focused package

@[default_target]
lean_lib Ethics where
  roots := #[
    `Ethics.CoreTypes,
    `Ethics.Curvature,
    `Ethics.Virtue,
    `Ethics.Measurement,
    `Ethics.Applications,
    `Ethics.Computability,
    `Ethics.RecognitionOperator,
    `Ethics.Gap45,
    `Ethics.Gap45_Computability,
    `Ethics.ConsciousNavigation,
    `Ethics.MathematicalFoundations,
    `Ethics.PvsNP_Connection
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation" @ "main"
