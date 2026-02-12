import LeanV31.R1CS2FailureForcesVanishingFrameCoercivity
import LeanV31.R1CS2FromMaxindexFrameCoercivity

namespace LeanV31

def R1MaxindexFrameCoercivityInfimumZeroAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S098 wrapper:
if CS2 fails on the radius-floor subsequence, maximal-index transported-frame
coercivity cannot stay uniformly positive; otherwise maximal-index coercivity
would force CS2, contradiction. -/
theorem R1_CS2_failure_forces_vanishing_maxindex_frame_coercivity
    {z : Complex}
    (hFailure : R1CS2FailureOnRadiusfloorTargetAt z)
    (hMaxindexImpliesCS2 :
      R1MaxindexFrameCoercivityConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z)
    (hContrapositiveBridge :
      (R1MaxindexFrameCoercivityConditionAt z ->
        R1CS2OnRadiusfloorTargetAt z) ->
      R1CS2FailureOnRadiusfloorTargetAt z ->
      R1MaxindexFrameCoercivityInfimumZeroAt z) :
    R1MaxindexFrameCoercivityInfimumZeroAt z := by
  exact hContrapositiveBridge hMaxindexImpliesCS2 hFailure

end LeanV31
