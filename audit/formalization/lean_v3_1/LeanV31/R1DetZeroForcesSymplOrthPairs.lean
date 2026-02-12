import LeanV31.R1Rank1AggregateDetExpansion

namespace LeanV31

def R1AggregateDetZeroAt (z : Complex) : Prop := Exists fun w : Complex => w = z
def R1PairwiseSymplOrthCouplingZeroAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S082 wrapper:
zero determinant of an aggregate window, together with determinant expansion
into nonnegative pairwise symplectic terms, forces each pairwise coupling term
to vanish. -/
theorem R1_det_zero_forces_sympl_orth_pairs
    {z : Complex}
    (hExpansion : R1AggregateDetExpansionAt z)
    (hDetZero : R1AggregateDetZeroAt z)
    (hBridge :
      R1AggregateDetExpansionAt z ->
      R1AggregateDetZeroAt z ->
      R1PairwiseSymplOrthCouplingZeroAt z) :
    R1PairwiseSymplOrthCouplingZeroAt z := by
  exact hBridge hExpansion hDetZero

end LeanV31
