import LeanV31.R1CollapseSpdFloor
import LeanV31.R1CS2Invtracecap

namespace LeanV31

def R1GlobalInvtraceCapAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S106 wrapper:
a global inverse-trace cap yields a global SPD floor, and therefore global
radius collapse by the SPD-floor collapse route. -/
theorem R1_collapse_invtracecap
    {z : Complex}
    (hInvtraceCap : R1GlobalInvtraceCapAt z)
    (hToGlobalSpd :
      R1GlobalInvtraceCapAt z ->
      R1GlobalUniformSpdFloorAt z)
    (hCollapseFromSpd :
      R1GlobalUniformSpdFloorAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  have hSpd : R1GlobalUniformSpdFloorAt z := hToGlobalSpd hInvtraceCap
  exact hCollapseFromSpd hSpd

end LeanV31
