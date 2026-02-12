import LeanV31.R1TailwindowPrefixEquiv
import LeanV31.R1PrefixSubsequenceDivergence

namespace LeanV31

def R1SubseqPrefixWindowPrincipleAt (_z : Complex) : Prop :=
  forall u : Nat -> Nat, StrictMono u ->
    Exists fun C : Real =>
      0 <= C /\ forall N : Nat, R1PrefixTraceMassAt (u N) <= C

def R1RadiusCollapseFromPrefixPrincipleAt (z : Complex) : Prop :=
  Exists fun j0 : Nat =>
    forall n : Nat, j0 <= n -> R1RadiusSequenceAt n z = 0

/- S069 wrapper:
if total mass diverges but every radius-floor subsequence satisfies a
prefix-window bound, contradiction with direct finite-mass forcing gives global
radius collapse on the upper half-plane. -/
theorem R1_rank1_tailwindow_principle
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hPrefixPrinciple : R1SubseqPrefixWindowPrincipleAt z)
    (hFiniteMassBridge :
      R1SubseqPrefixWindowPrincipleAt z ->
      R1FiniteTotalMassFromPrefixWindowAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1FiniteTotalMassFromPrefixWindowAt z ->
      R1RadiusCollapseFromPrefixPrincipleAt z) :
    R1RadiusCollapseFromPrefixPrincipleAt z := by
  have hFinite : R1FiniteTotalMassFromPrefixWindowAt z :=
    hFiniteMassBridge hPrefixPrinciple
  exact hCollapseBridge hMassDiverges hFinite

end LeanV31
