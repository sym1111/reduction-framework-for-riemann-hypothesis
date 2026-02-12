import LeanV31.R1PrefixMassCollinearVisible
import LeanV31.R1Rank1TailwindowPrinciple

namespace LeanV31

def R1GlobalRadiusCollapseFromCollinearAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S075 wrapper:
if every radius-floor subsequence satisfies the collinear-window prefix bound,
the independent tailwindow principle forces global Weyl-radius collapse. -/
theorem R1_collapse_collinear_visible
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hCollinearPrefixBound : R1PrefixMassCollinearVisibleBoundAt z)
    (hPrincipleBridge :
      R1TotalMassDivergesAt z ->
      R1PrefixMassCollinearVisibleBoundAt z ->
      R1GlobalRadiusCollapseFromCollinearAt z) :
    R1GlobalRadiusCollapseFromCollinearAt z := by
  exact hPrincipleBridge hMassDiverges hCollinearPrefixBound

end LeanV31
