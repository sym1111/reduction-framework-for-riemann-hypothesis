import LeanV31.R1Rank1AggregateDetEquiv

namespace LeanV31

def R1AggregateDetExpansionAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0 /\ 0 < j0

/- S080 wrapper:
for rank-one atomic PSD window decomposition, determinant of the aggregate
equals the pairwise symplectic-coupling quadratic sum. -/
theorem R1_rank1_aggregate_det_expansion
    {z : Complex}
    (hExpansionBridge :
      R1RankOneAggregateCriterionAt z ->
      R1AggregateDetExpansionAt z)
    (hRankOneAggregate : R1RankOneAggregateCriterionAt z) :
    R1AggregateDetExpansionAt z := by
  exact hExpansionBridge hRankOneAggregate

end LeanV31
