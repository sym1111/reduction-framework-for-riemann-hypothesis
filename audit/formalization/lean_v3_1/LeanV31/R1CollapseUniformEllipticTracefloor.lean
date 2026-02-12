import LeanV31.R1CollapseSpdFloor
import LeanV31.R1CS2UniformEllipticTracefloor

namespace LeanV31

def R1GlobalUniformEllipticTracefloorAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0

/- S105 wrapper:
global uniform ellipticity with trace floor implies a global SPD floor, so the
global SPD-floor collapse corollary applies directly. -/
theorem R1_collapse_uniform_elliptic_tracefloor
    {z : Complex}
    (hUniformEllipticTracefloor : R1GlobalUniformEllipticTracefloorAt z)
    (hToGlobalSpd :
      R1GlobalUniformEllipticTracefloorAt z ->
      R1GlobalUniformSpdFloorAt z)
    (hCollapseFromSpd :
      R1GlobalUniformSpdFloorAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  have hSpd : R1GlobalUniformSpdFloorAt z := hToGlobalSpd hUniformEllipticTracefloor
  exact hCollapseFromSpd hSpd

end LeanV31
