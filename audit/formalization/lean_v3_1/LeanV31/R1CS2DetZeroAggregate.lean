import LeanV31.R1CS2Rank1Aggregate
import LeanV31.R1Rank1AggregateDetEquiv

namespace LeanV31

/- S090 wrapper:
for PSD aggregate windows in dimension two, zero determinant implies the
rank-one aggregate criterion, which then yields CS2 via the rank-one route. -/
theorem R1_CS2_det_zero_aggregate
    {z : Complex}
    (hDetZero : R1AggregateDetZeroCriterionAt z)
    (hCriterionToWindow :
      R1RankOneAggregateCriterionAt z ->
      R1Rank1AggregateWindowAt z)
    (hRankOneCS2 :
      R1Rank1AggregateWindowAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hCriterion : R1RankOneAggregateCriterionAt z :=
    (R1_rank1_aggregate_det_equiv (z := z)).mpr hDetZero
  have hWindow : R1Rank1AggregateWindowAt z := hCriterionToWindow hCriterion
  exact hRankOneCS2 hWindow

end LeanV31
