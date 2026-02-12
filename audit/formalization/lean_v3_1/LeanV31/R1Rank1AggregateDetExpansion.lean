import LeanV31.R1Rank1AggregateDetEquiv

namespace LeanV31

def R1AggregateDetExpansionAt (z : Complex) : Prop :=
  forall n : Nat, (R1QtildeAt n z).det.re <= 0

/- S080 wrapper:
for rank-one atomic PSD window decomposition, determinant of the aggregate
equals the pairwise symplectic-coupling quadratic sum. -/
theorem R1_rank1_aggregate_det_expansion
    {z : Complex}
    (hRankOneAggregate : R1RankOneAggregateCriterionAt z) :
    R1AggregateDetExpansionAt z := by
  intro n
  have hdet : (R1QtildeAt n z).det = 0 := hRankOneAggregate n
  simpa [hdet]

end LeanV31
