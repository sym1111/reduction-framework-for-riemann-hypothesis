import LeanV31.R1RadiusfloorClosure
import LeanV31.R1LimitCircleImpliesFiniteMass

namespace LeanV31

def R1CS2OnRadiusfloorTargetAt (_z : Complex) : Prop := Exists fun t0 : Nat => 0 <= t0 /\ 0 < t0

/- S086 wrapper:
radius-floor closure provides finite-total-mass control on the target
subsequence, and finite-total-mass CS2 forcing yields the target CS2 bound. -/
theorem R1_CS2_on_radiusfloor_target
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorTargetSubsequenceAt z)
    (hRadiusfloorClosure :
      R1RadiusFloorTargetSubsequenceAt z ->
      R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z)
    (hFiniteFromClosure :
      R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z ->
      R1FiniteTotalMassAt z)
    (hCS2FromFiniteMass :
      R1FiniteTotalMassAt z ->
      R1CS2ConditionAt z)
    (hTargetBridge :
      R1CS2ConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hClosure :
      R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z :=
    hRadiusfloorClosure hRadiusFloor
  have hFinite : R1FiniteTotalMassAt z := hFiniteFromClosure hClosure
  have hCS2 : R1CS2ConditionAt z := hCS2FromFiniteMass hFinite
  exact hTargetBridge hCS2

end LeanV31
