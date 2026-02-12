import LeanV31.R1CS2EquivKj
import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1FrameRatioKappaBalance

namespace LeanV31

def R1MaxindexFrameCoercivityConditionAt (_z : Complex) : Prop :=
  Exists fun c : Real => 0 < c

/- S097 wrapper:
coercivity at maximal-frame indices, combined with frame-ratio/kappa balance,
gives uniform boundedness of `K_j`; via CS2-`K_j` equivalence this yields the
target CS2 conclusion on the radius-floor subsequence. -/
theorem R1_CS2_from_maxindex_frame_coercivity
    {z : Complex}
    (hBalance : R1FrameRatioKappaBalanceAt z)
    (hMaxindexCoercivity : R1MaxindexFrameCoercivityConditionAt z)
    (hKjBridge :
      R1FrameRatioKappaBalanceAt z ->
      R1MaxindexFrameCoercivityConditionAt z ->
      R1KjUniformBoundAt z)
    (hCS2EquivKj :
      R1CS2ConditionAt z <-> R1KjUniformBoundAt z)
    (hTargetBridge :
      R1CS2ConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hKj : R1KjUniformBoundAt z := hKjBridge hBalance hMaxindexCoercivity
  have hCS2 : R1CS2ConditionAt z := hCS2EquivKj.mpr hKj
  exact hTargetBridge hCS2

end LeanV31
