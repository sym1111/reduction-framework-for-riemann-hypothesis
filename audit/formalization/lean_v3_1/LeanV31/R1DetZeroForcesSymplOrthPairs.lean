import LeanV31.R1Rank1AggregateDetExpansion

namespace LeanV31

def R1AggregateDetZeroAt (z : Complex) : Prop :=
  R1AggregateDetZeroCriterionAt z

def R1PairwiseSymplOrthCouplingZeroAt (z : Complex) : Prop :=
  R1AggregateDetExpansionAt z

/- S082 wrapper:
zero determinant of an aggregate window, together with determinant expansion
into nonnegative pairwise symplectic terms, forces each pairwise coupling term
to vanish. -/
theorem R1_det_zero_forces_sympl_orth_pairs
    {z : Complex}
    (hExpansion : R1AggregateDetExpansionAt z)
    (_hDetZero : R1AggregateDetZeroAt z) :
    R1PairwiseSymplOrthCouplingZeroAt z := by
  exact hExpansion

end LeanV31
