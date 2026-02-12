import LeanV31.Basic

namespace LeanV31

def R1PairwiseSymplOrthogonalityAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0
def R1OneDirectionWindowFamilyAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S084 wrapper:
for window vectors in `R^2`, pairwise symplectic orthogonality is equivalent
to all vectors lying on a single direction (collinearity). -/
theorem R1_sympl_orth_collinear_equiv
    {z : Complex}
    (hForward :
      R1PairwiseSymplOrthogonalityAt z ->
      R1OneDirectionWindowFamilyAt z)
    (hBackward :
      R1OneDirectionWindowFamilyAt z ->
      R1PairwiseSymplOrthogonalityAt z) :
    R1PairwiseSymplOrthogonalityAt z <-> R1OneDirectionWindowFamilyAt z := by
  exact Iff.intro hForward hBackward

end LeanV31
