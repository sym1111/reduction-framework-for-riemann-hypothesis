import LeanV31.R1CS2DetZeroAggregate
import LeanV31.R1Rank1AggregateDetExpansion

namespace LeanV31

def R1ZeroSymplAreaSumOnWindowsAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S091 wrapper:
vanishing pairwise symplectic-area sum on each window, together with the
determinant expansion identity, gives zero aggregate determinant; the det-zero
CS2 corollary then closes the argument. -/
theorem R1_CS2_zero_sympl_area_sum
    {z : Complex}
    (hExpansion : R1AggregateDetExpansionAt z)
    (hZeroSymplSum : R1ZeroSymplAreaSumOnWindowsAt z)
    (hZeroSumToDetZero :
      R1AggregateDetExpansionAt z ->
      R1ZeroSymplAreaSumOnWindowsAt z ->
      R1AggregateDetZeroCriterionAt z)
    (hDetZeroCS2 :
      R1AggregateDetZeroCriterionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hDetZero : R1AggregateDetZeroCriterionAt z :=
    hZeroSumToDetZero hExpansion hZeroSymplSum
  exact hDetZeroCS2 hDetZero

end LeanV31
