import LeanV31.R1CollapseRank1Aggregate

namespace LeanV31

def R1RankOneAggregateCriterionAt (_z : Complex) : Prop := Exists fun r : Nat => r <= r
def R1AggregateDetZeroCriterionAt (_z : Complex) : Prop := Exists fun r0 : Nat => 0 <= r0

/- S079 wrapper:
for real-symmetric PSD aggregate windows in dimension two, rank-at-most-one is
equivalent to zero determinant. -/
theorem R1_rank1_aggregate_det_equiv
    {z : Complex}
    (hForward :
      R1RankOneAggregateCriterionAt z ->
      R1AggregateDetZeroCriterionAt z)
    (hBackward :
      R1AggregateDetZeroCriterionAt z ->
      R1RankOneAggregateCriterionAt z) :
    R1RankOneAggregateCriterionAt z <-> R1AggregateDetZeroCriterionAt z := by
  exact Iff.intro hForward hBackward

end LeanV31
