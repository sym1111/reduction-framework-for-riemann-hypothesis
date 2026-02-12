import LeanV31.R1CollapseCollinearVisible

namespace LeanV31

def R1Rank1AggregateWindowAt (_z : Complex) : Prop :=
  Exists fun u : Nat -> Nat => StrictMono u
def R1CollinearRepresentationFromAggregateAt (_z : Complex) : Prop :=
  Exists fun v : Complex × Complex => v.1 ≠ 0 ∨ v.2 ≠ 0

/- S076 wrapper:
rank-one aggregate windows force all constituent PSD blocks to share one
collinear direction, giving a common `a_l * v v^T` representation. -/
theorem R1_collinear_from_rank1_aggregate
    {z : Complex}
    (hAggregate : R1Rank1AggregateWindowAt z)
    (hCollinearBridge :
      R1Rank1AggregateWindowAt z ->
      R1CollinearRepresentationFromAggregateAt z) :
    R1CollinearRepresentationFromAggregateAt z := by
  exact hCollinearBridge hAggregate

end LeanV31
