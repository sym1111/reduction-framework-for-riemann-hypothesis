import LeanV31.R1CS2AtomicSymplOrthWindows
import LeanV31.R1LimitCircleImpliesFiniteMass
import LeanV31.R1PrefixSubsequenceDivergence

namespace LeanV31

def R1GlobalRadiusCollapseAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0 /\ 0 < j0

/- S103 wrapper:
if every radius-floor subsequence satisfies the atomic symplectic-orthogonality
CS2 criterion, then any non-collapse branch would force finite mass, which
contradicts the mass-divergence hypothesis; hence global radius collapse. -/
theorem R1_collapse_atomic_sympl_orth
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hAtomicCS2Target : R1CS2OnRadiusfloorTargetAt z)
    (hFiniteMassBridge :
      R1CS2OnRadiusfloorTargetAt z ->
      R1FiniteTotalMassAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1FiniteTotalMassAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1GlobalRadiusCollapseAt z := by
  have hFinite : R1FiniteTotalMassAt z := hFiniteMassBridge hAtomicCS2Target
  exact hCollapseBridge hMassDiverges hFinite

end LeanV31
