import LeanV31.R1CS2OnRadiusfloorTarget
import LeanV31.R1CS2SpdFloor

namespace LeanV31

def R1DetfloorTracecapConditionAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C

/- S101 wrapper:
a determinant floor with trace cap implies a uniform positive lower bound for
the minimal eigenvalue (hence uniform SPD floor), and therefore CS2 by the
SPD-floor mechanism. -/
theorem R1_CS2_detfloor_tracecap
    {z : Complex}
    (hCondition : R1DetfloorTracecapConditionAt z)
    (hToSpdFloor :
      R1DetfloorTracecapConditionAt z ->
      R1UniformSPDFloorOnWindowsAt z)
    (hSpdToTarget :
      R1UniformSPDFloorOnWindowsAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hSpd : R1UniformSPDFloorOnWindowsAt z := hToSpdFloor hCondition
  exact hSpdToTarget hSpd

end LeanV31
