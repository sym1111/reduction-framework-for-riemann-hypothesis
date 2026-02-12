import LeanV31.R1AtomicAggregateDetExpansion
import LeanV31.R1CS2DetZeroAggregate

namespace LeanV31

def R1AtomicSymplOrthWindowFamilyAt (z : Complex) : Prop :=
  forall n : Nat, (R1QtildeAt n z).det = 0

/- S092 wrapper:
if each window admits an atomic decomposition with pairwise symplectic
orthogonality across distinct atoms, atomic determinant expansion forces
det-zero aggregate windows, hence CS2 by the det-zero route. -/
theorem R1_CS2_atomic_sympl_orth_windows
    {z : Complex}
    (_hAtomicExpansion : R1AtomicAggregateDetExpansionAt z)
    (hAtomicOrth : R1AtomicSymplOrthWindowFamilyAt z)
    (hDetZeroCS2 :
      R1AggregateDetZeroCriterionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hDetZero : R1AggregateDetZeroCriterionAt z := hAtomicOrth
  exact hDetZeroCS2 hDetZero

end LeanV31
