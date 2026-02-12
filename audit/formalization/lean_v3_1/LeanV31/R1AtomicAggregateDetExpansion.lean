import LeanV31.R1Rank1AggregateDetExpansion

namespace LeanV31

def R1AtomicAggregateDetExpansionAt (z : Complex) : Prop :=
  R1AggregateDetExpansionAt z

/- S081 wrapper:
atomic aggregate windows satisfy Cauchy-Binet determinant expansion into the
sum of pairwise squared symplectic couplings. -/
theorem R1_atomic_aggregate_det_expansion
    {z : Complex}
    (hExpansion : R1AggregateDetExpansionAt z) :
    R1AtomicAggregateDetExpansionAt z := by
  exact hExpansion

end LeanV31
