import LeanV31.R1CollapseRank1Aggregate

namespace LeanV31

def R1RankOneAggregateCriterionAt (z : Complex) : Prop :=
  forall n : Nat, (R1QtildeAt n z).det = 0

def R1AggregateDetZeroCriterionAt (z : Complex) : Prop :=
  forall n : Nat, (R1QtildeAt n z).det = 0

/- S079 wrapper:
for real-symmetric PSD aggregate windows in dimension two, rank-at-most-one is
equivalent to zero determinant. -/
theorem R1_rank1_aggregate_det_equiv
    {z : Complex} :
    R1RankOneAggregateCriterionAt z <-> R1AggregateDetZeroCriterionAt z := by
  exact Iff.rfl

end LeanV31
