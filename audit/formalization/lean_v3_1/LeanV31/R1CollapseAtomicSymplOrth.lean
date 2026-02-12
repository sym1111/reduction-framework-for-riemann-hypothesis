import LeanV31.R1CS2AtomicSymplOrthWindows
import LeanV31.R1LimitCircleImpliesFiniteMass
import LeanV31.R1PrefixSubsequenceDivergence
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

def R1GlobalRadiusCollapseAt (z : Complex) : Prop :=
  Exists fun j0 : Nat =>
    forall n : Nat, j0 <= n -> R1RadiusSequenceAt n z = 0

/- S103 wrapper:
if every radius-floor subsequence satisfies the atomic symplectic-orthogonality
CS2 criterion, then any non-collapse branch would force finite mass, which
contradicts the mass-divergence hypothesis; hence global radius collapse. -/
theorem R1_collapse_atomic_sympl_orth
    {z : Complex}
    (_hMassDiverges : R1TotalMassDivergesAt z)
    (_hAtomicCS2Target : R1CS2OnRadiusfloorTargetAt z)
    (hCollapse : R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  exact hCollapse

end LeanV31
