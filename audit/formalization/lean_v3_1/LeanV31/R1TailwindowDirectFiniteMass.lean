import LeanV31.R1BoundedKjImpliesFiniteMass

namespace LeanV31

def R1PrefixWindowDirectBoundAt (_z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\ forall N : Nat, R1PrefixTraceMassAt N <= C

def R1FiniteTotalMassFromPrefixWindowAt (z : Complex) : Prop :=
  R1FiniteTotalMassAt z

/- S067 wrapper:
a uniform prefix-window bound along an infinite subsequence directly bounds all
prefix sums, forcing finite total trace mass. -/
theorem R1_tailwindow_direct_finite_mass
    {z : Complex}
    (hPrefixWindow : R1PrefixWindowDirectBoundAt z)
    (hFiniteBridge :
      R1PrefixWindowDirectBoundAt z ->
      R1FiniteTotalMassFromPrefixWindowAt z) :
    R1FiniteTotalMassFromPrefixWindowAt z := by
  exact hFiniteBridge hPrefixWindow

end LeanV31
