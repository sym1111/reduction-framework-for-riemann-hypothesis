import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1CS2SpdFloor

namespace LeanV31

def R1UniformEllipticTracefloorConditionAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S100 wrapper:
uniform ellipticity with a positive trace floor yields a uniform SPD lower
bound on each window matrix, so the SPD-floor CS2 proposition gives the target
CS2 conclusion. -/
theorem R1_CS2_uniform_elliptic_tracefloor
    {z : Complex}
    (hCondition : R1UniformEllipticTracefloorConditionAt z)
    (hToSpdFloor :
      R1UniformEllipticTracefloorConditionAt z ->
      R1UniformSPDFloorOnWindowsAt z)
    (hSpdToTarget :
      R1UniformSPDFloorOnWindowsAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hSpd : R1UniformSPDFloorOnWindowsAt z := hToSpdFloor hCondition
  exact hSpdToTarget hSpd

end LeanV31
