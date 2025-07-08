import Lake
open Lake DSL

package ledgerEthics where
  -- Basic settings for this ethics-focused package

@[default_target]
lean_lib Ethics where
  roots := #[`Ethics.CoreTypes]

require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation" @ "main"
