import LeanV31.R1CS2CollinearWindows
import LeanV31.R1CollinearFromRank1Aggregate

namespace LeanV31

/- S089 wrapper:
rank-one aggregate windows yield a collinear representation windowwise; then
the collinear-window CS2 proposition applies directly. -/
theorem R1_CS2_rank1_aggregate
    {z : Complex}
    (hRankOneAggregate : R1Rank1AggregateWindowAt z)
    (hCollinearBridge :
      R1Rank1AggregateWindowAt z ->
      R1CollinearRepresentationFromAggregateAt z)
    (hModelBridge :
      R1CollinearRepresentationFromAggregateAt z ->
      R1CollinearWindowModelAt z)
    (hCollinearCS2 :
      R1CollinearWindowModelAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hCollinearRep : R1CollinearRepresentationFromAggregateAt z :=
    hCollinearBridge hRankOneAggregate
  have hModel : R1CollinearWindowModelAt z := hModelBridge hCollinearRep
  exact hCollinearCS2 hModel

end LeanV31
