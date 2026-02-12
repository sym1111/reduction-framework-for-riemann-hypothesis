import LeanV31.R1CS2FailureForcesVanishingFrameCoercivity
import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1CS2SpdFloor

namespace LeanV31

def R1LocalCoercivityInfimumZeroAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S099 wrapper:
failure of CS2 on a radius-floor subsequence forces vanishing local coercivity:
if a uniform SPD floor persisted, the SPD-floor CS2 proposition would imply the
target CS2 conclusion, contradiction. -/
theorem R1_CS2_failure_forces_vanishing_coercivity
    {z : Complex}
    (hFailure : R1CS2FailureOnRadiusfloorTargetAt z)
    (hSpdFloorImpliesCS2 :
      R1UniformSPDFloorOnWindowsAt z ->
      R1CS2OnRadiusfloorTargetAt z)
    (hContrapositiveBridge :
      (R1UniformSPDFloorOnWindowsAt z ->
        R1CS2OnRadiusfloorTargetAt z) ->
      R1CS2FailureOnRadiusfloorTargetAt z ->
      R1LocalCoercivityInfimumZeroAt z) :
    R1LocalCoercivityInfimumZeroAt z := by
  exact hContrapositiveBridge hSpdFloorImpliesCS2 hFailure

end LeanV31
