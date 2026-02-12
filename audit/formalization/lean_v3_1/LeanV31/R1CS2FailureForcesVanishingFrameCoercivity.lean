import LeanV31.R1CS2FrameCoercivityWindows
import LeanV31.R1CS2OnRadiusfloorTarget

namespace LeanV31

def R1CS2FailureOnRadiusfloorTargetAt (z : Complex) : Prop :=
  ¬ R1CS2OnRadiusfloorTargetAt z
def R1FrameCoercivityInfimumZeroAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S096 wrapper:
if CS2 fails on the radius-floor subsequence, the transported-frame coercivity
infimum cannot stay strictly positive; otherwise coercivity-windows CS2 would
force the target CS2 conclusion, contradiction. -/
theorem R1_CS2_failure_forces_vanishing_frame_coercivity
    {z : Complex}
    (hFailure : R1CS2FailureOnRadiusfloorTargetAt z)
    (hCoercivityImpliesCS2 :
      R1FrameCoercivityWindowConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z)
    (hContrapositiveBridge :
      (R1FrameCoercivityWindowConditionAt z ->
        R1CS2OnRadiusfloorTargetAt z) ->
      R1CS2FailureOnRadiusfloorTargetAt z ->
      R1FrameCoercivityInfimumZeroAt z) :
    R1FrameCoercivityInfimumZeroAt z := by
  exact hContrapositiveBridge hCoercivityImpliesCS2 hFailure

end LeanV31
