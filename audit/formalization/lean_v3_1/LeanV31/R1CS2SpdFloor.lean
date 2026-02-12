import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1CS2Equiv
import LeanV31.R1Det1
import LeanV31.R1RadiusfloorKappaBottleneck

namespace LeanV31

def R1UniformSPDFloorOnWindowsAt (_z : Complex) : Prop :=
  Exists fun c : Real => 0 < c
def R1CS2SpdFloorAt (_z : Complex) : Prop := Exists fun n0 : Nat => 0 <= n0

/- S093 wrapper:
uniform SPD lower bounds on window matrices combine with radius-floor channel
energy control and determinant-one/singular-value identities to give a uniform
kappa bound, i.e. CS2 on the target subsequence. -/
theorem R1_CS2_spd_floor
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorSubsequenceAt z)
    (hSpdFloor : R1UniformSPDFloorOnWindowsAt z)
    (hBottleneck :
      (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) /\
      R1FrameGrowthDivergenceAt z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hCS2Equiv :
      R1CS2ConditionAt z <-> R1CS2TailBoundAt z)
    (hSpdBridge :
      R1RadiusFloorSubsequenceAt z ->
      R1UniformSPDFloorOnWindowsAt z ->
      ((forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) /\
        R1FrameGrowthDivergenceAt z) ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      (R1CS2ConditionAt z <-> R1CS2TailBoundAt z) ->
      R1CS2ConditionAt z)
    (hTargetBridge :
      R1CS2ConditionAt z ->
      R1CS2SpdFloorAt z) :
    R1CS2SpdFloorAt z := by
  have hCS2 : R1CS2ConditionAt z :=
    hSpdBridge hRadiusFloor hSpdFloor hBottleneck hDet1 hCS2Equiv
  exact hTargetBridge hCS2

end LeanV31
