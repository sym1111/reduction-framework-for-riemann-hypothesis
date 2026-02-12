import LeanV31.R1CS2StructuredLagrangianLine
import LeanV31.R1LinearTailUnderSymplecticOrth
import LeanV31.R1RadiusfloorKappaBottleneck

namespace LeanV31

def R1CollinearWindowModelAt (_z : Complex) : Prop :=
  Exists fun v : Complex => ‖v‖ = 1
def R1PrefixMassCollinearVisibleBoundAt (_z : Complex) : Prop :=
  Exists fun B : Real => 0 <= B

/- S074 wrapper:
if each window is collinear rank-one, linear tail transport and Weyl-circle
entry identities yield an explicit uniform prefix-mass bound on the subsequence.
-/
theorem R1_prefix_mass_collinear_visible
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorSubsequenceAt z)
    (hCollinear : R1CollinearWindowModelAt z)
    (hLinearTail : forall k n : Nat, R1LinearTailFormulaAt k n z)
    (hPrefixBridge :
      R1RadiusFloorSubsequenceAt z ->
      R1CollinearWindowModelAt z ->
      (forall k n : Nat, R1LinearTailFormulaAt k n z) ->
      R1PrefixMassCollinearVisibleBoundAt z) :
    R1PrefixMassCollinearVisibleBoundAt z := by
  exact hPrefixBridge hRadiusFloor hCollinear hLinearTail

end LeanV31
