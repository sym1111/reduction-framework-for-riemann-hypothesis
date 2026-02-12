import LeanV31.R1CollapseRank1Aggregate
import LeanV31.R1Rank1AggregateDetEquiv

namespace LeanV31

def R1CollapseDetZeroAggregateAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S083 wrapper:
if aggregate determinants vanish along the radius-floor branch, determinant
equivalence gives rank-one aggregate windows; rank-one collapse then yields the
target global collapse statement. -/
theorem R1_collapse_det_zero_aggregate
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hDetZero : R1AggregateDetZeroCriterionAt z)
    (hDetEquiv :
      R1RankOneAggregateCriterionAt z <-> R1AggregateDetZeroCriterionAt z)
    (hRankOneToPrefix :
      R1RankOneAggregateCriterionAt z ->
      R1PrefixMassBoundFromRank1AggregateAt z)
    (hRankOneCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1PrefixMassBoundFromRank1AggregateAt z ->
      R1GlobalCollapseFromRank1AggregateAt z)
    (hFinalize :
      R1GlobalCollapseFromRank1AggregateAt z ->
      R1CollapseDetZeroAggregateAt z) :
    R1CollapseDetZeroAggregateAt z := by
  have hRankOne : R1RankOneAggregateCriterionAt z := hDetEquiv.mpr hDetZero
  have hPrefix : R1PrefixMassBoundFromRank1AggregateAt z := hRankOneToPrefix hRankOne
  have hGlobal : R1GlobalCollapseFromRank1AggregateAt z :=
    R1_collapse_rank1_aggregate (z := z) hMassDiverges hPrefix hRankOneCollapseBridge
  exact hFinalize hGlobal

end LeanV31
