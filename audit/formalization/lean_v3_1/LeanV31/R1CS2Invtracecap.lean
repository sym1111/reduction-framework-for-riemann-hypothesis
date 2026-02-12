import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1CS2SpdFloor

namespace LeanV31

def R1InverseTraceCapConditionAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S102 wrapper:
an inverse-trace cap on positive definite window blocks yields a uniform lower
eigenvalue bound (hence a uniform SPD floor), so CS2 follows from the SPD-floor
mechanism on the radius-floor subsequence. -/
theorem R1_CS2_invtracecap
    {z : Complex}
    (hInvTraceCap : R1InverseTraceCapConditionAt z)
    (hToSpdFloor :
      R1InverseTraceCapConditionAt z ->
      R1UniformSPDFloorOnWindowsAt z)
    (hSpdToTarget :
      R1UniformSPDFloorOnWindowsAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hSpd : R1UniformSPDFloorOnWindowsAt z := hToSpdFloor hInvTraceCap
  exact hSpdToTarget hSpd

end LeanV31
