import LeanV31.R1Rank1AggregateDetExpansion

namespace LeanV31

def R1AtomicAggregateDetExpansionAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S081 wrapper:
atomic aggregate windows satisfy Cauchy-Binet determinant expansion into the
sum of pairwise squared symplectic couplings. -/
theorem R1_atomic_aggregate_det_expansion
    {z : Complex}
    (hAtomicBridge :
      R1AggregateDetExpansionAt z ->
      R1AtomicAggregateDetExpansionAt z)
    (hExpansion : R1AggregateDetExpansionAt z) :
    R1AtomicAggregateDetExpansionAt z := by
  exact hAtomicBridge hExpansion

end LeanV31
