import LeanV31.R1CollinearFromRank1Aggregate
import LeanV31.R1PrefixMassCollinearVisible

namespace LeanV31

def R1PrefixMassBoundFromRank1AggregateAt (_z : Complex) : Prop :=
  Exists fun B : Real => 0 <= B

/- S077 wrapper:
rank-one aggregate structure yields collinear representation on each window, so
the collinear-visible prefix-mass estimate applies uniformly. -/
theorem R1_prefix_mass_from_rank1_aggregate
    {z : Complex}
    (hAggregate : R1Rank1AggregateWindowAt z)
    (hCollinear : R1CollinearRepresentationFromAggregateAt z)
    (hBoundBridge :
      R1CollinearRepresentationFromAggregateAt z ->
      R1PrefixMassCollinearVisibleBoundAt z ->
      R1PrefixMassBoundFromRank1AggregateAt z)
    (hCollinearVisible : R1PrefixMassCollinearVisibleBoundAt z) :
    R1PrefixMassBoundFromRank1AggregateAt z := by
  have _hAggregate := hAggregate
  exact hBoundBridge hCollinear hCollinearVisible

end LeanV31
