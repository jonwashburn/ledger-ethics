/-
Minimal Curvature Test
======================
-/

import Ethics.CoreTypes

namespace RecognitionScience.Ethics

/-- Curvature measures ledger balance -/
def curvature (s : MoralState) : Int := s.ledger.balance

end RecognitionScience.Ethics
