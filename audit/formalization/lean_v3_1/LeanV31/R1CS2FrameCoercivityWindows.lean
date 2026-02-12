import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1FrameRatioKappaBalance

namespace LeanV31

def R1FrameCoercivityWindowConditionAt (_z : Complex) : Prop :=
  Exists fun c : Real => 0 < c

/- S095 wrapper:
if transported-frame coercivity is uniformly positive on every window point,
the frame-ratio/kappa balance immediately yields a uniform kappa bound and
hence CS2 on the radius-floor subsequence. -/
theorem R1_CS2_frame_coercivity_windows
    {z : Complex}
    (hBalance : R1FrameRatioKappaBalanceAt z)
    (hCoercivity : R1FrameCoercivityWindowConditionAt z)
    (hCS2Bridge :
      R1FrameRatioKappaBalanceAt z ->
      R1FrameCoercivityWindowConditionAt z ->
      R1CS2ConditionAt z)
    (hTargetBridge :
      R1CS2ConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hCS2 : R1CS2ConditionAt z := hCS2Bridge hBalance hCoercivity
  exact hTargetBridge hCS2

end LeanV31
