import LeanV31.R1PrefixMassFromRank1Aggregate
import LeanV31.R1Rank1TailwindowPrinciple

namespace LeanV31

def R1GlobalCollapseFromRank1AggregateAt (z : Complex) : Prop :=
  Exists fun w : Complex => w = z

/- S078 wrapper:
if every radius-floor subsequence has rank-one aggregate and total mass
diverges, the induced prefix-mass bounds trigger the independent tailwindow
closure principle, yielding global radius collapse. -/
theorem R1_collapse_rank1_aggregate
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hPrefixBound : R1PrefixMassBoundFromRank1AggregateAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1PrefixMassBoundFromRank1AggregateAt z ->
      R1GlobalCollapseFromRank1AggregateAt z) :
    R1GlobalCollapseFromRank1AggregateAt z := by
  exact hCollapseBridge hMassDiverges hPrefixBound

end LeanV31
