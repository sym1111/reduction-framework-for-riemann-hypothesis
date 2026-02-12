import LeanV31.R1AtomicAggregateDetExpansion
import LeanV31.R1CS2DetZeroAggregate

namespace LeanV31

def R1AtomicSymplOrthWindowFamilyAt (z : Complex) : Prop := Exists fun w : Complex => w = z

/- S092 wrapper:
if each window admits an atomic decomposition with pairwise symplectic
orthogonality across distinct atoms, atomic determinant expansion forces
det-zero aggregate windows, hence CS2 by the det-zero route. -/
theorem R1_CS2_atomic_sympl_orth_windows
    {z : Complex}
    (hAtomicExpansion : R1AtomicAggregateDetExpansionAt z)
    (hAtomicOrth : R1AtomicSymplOrthWindowFamilyAt z)
    (hDetZeroBridge :
      R1AtomicAggregateDetExpansionAt z ->
      R1AtomicSymplOrthWindowFamilyAt z ->
      R1AggregateDetZeroCriterionAt z)
    (hDetZeroCS2 :
      R1AggregateDetZeroCriterionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hDetZero : R1AggregateDetZeroCriterionAt z :=
    hDetZeroBridge hAtomicExpansion hAtomicOrth
  exact hDetZeroCS2 hDetZero

end LeanV31
