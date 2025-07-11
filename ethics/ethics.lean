/-
  Recognition Science: Ethics Module
  =================================

  Main entry point for the ethics module.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

-- Import all ethics submodules
import Ethics.Curvature
import Ethics.Virtue
import Ethics.Measurement
import Ethics.EmpiricalData
import Ethics.Applications
import Ethics.Main

namespace RecognitionScience.Ethics

-- Re-export key definitions
export Curvature (MoralState curvature κ isGood suffering joy)
export Virtue (Virtue TrainVirtue VirtueEffectiveness)
export Measurement (CurvatureSignature CurvatureMetric)
export Applications (Institution AIAlignment)

end RecognitionScience.Ethics
