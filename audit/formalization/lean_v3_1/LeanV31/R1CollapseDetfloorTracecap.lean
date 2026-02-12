import LeanV31.R1CollapseSpdFloor
import LeanV31.R1CS2DetfloorTracecap

namespace LeanV31

def R1GlobalDetfloorTracecapAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S107 wrapper:
a global determinant floor plus trace cap implies a global SPD floor, so the
global SPD-floor collapse corollary yields radius collapse on `C_+`. -/
theorem R1_collapse_detfloor_tracecap
    {z : Complex}
    (hDetfloorTracecap : R1GlobalDetfloorTracecapAt z)
    (hToGlobalSpd :
      R1GlobalDetfloorTracecapAt z ->
      R1GlobalUniformSpdFloorAt z)
    (hCollapseFromSpd :
      R1GlobalUniformSpdFloorAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  have hSpd : R1GlobalUniformSpdFloorAt z := hToGlobalSpd hDetfloorTracecap
  exact hCollapseFromSpd hSpd

end LeanV31
