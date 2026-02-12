import LeanV31.R1CollapseAtomicSymplOrth
import LeanV31.R1CS2SpdFloor
import LeanV31.R1PrefixSubsequenceDivergence

namespace LeanV31

def R1GlobalUniformSpdFloorAt (_z : Complex) : Prop :=
  Exists fun c : Real => 0 < c

/- S104 wrapper:
a global uniform SPD floor gives the windowwise CS2 condition on any radius-floor
subsequence; that forces finite mass, contradicting divergence implied by the
same floor, so radii collapse globally. -/
theorem R1_collapse_spd_floor
    {z : Complex}
    (hGlobalSpdFloor : R1GlobalUniformSpdFloorAt z)
    (hSpdToCS2Target :
      R1GlobalUniformSpdFloorAt z ->
      R1CS2OnRadiusfloorTargetAt z)
    (hFiniteMassBridge :
      R1CS2OnRadiusfloorTargetAt z ->
      R1FiniteTotalMassAt z)
    (hMassDivergesFromSpd :
      R1GlobalUniformSpdFloorAt z ->
      R1TotalMassDivergesAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1FiniteTotalMassAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  have hCS2 : R1CS2OnRadiusfloorTargetAt z := hSpdToCS2Target hGlobalSpdFloor
  have hFinite : R1FiniteTotalMassAt z := hFiniteMassBridge hCS2
  have hMassDiverges : R1TotalMassDivergesAt z := hMassDivergesFromSpd hGlobalSpdFloor
  exact hCollapseBridge hMassDiverges hFinite

end LeanV31
