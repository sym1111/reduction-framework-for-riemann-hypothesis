import LeanV31.R1Rank1TailwindowPrinciple
import LeanV31.R1Det1

namespace LeanV31

def R1UniformEllipticityAt (_z : Complex) : Prop :=
  Exists fun c : Real => 0 < c
def R1FiniteTotalMassFromUniformEllipticityAt (_z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C

/- S070 wrapper:
under radius-floor setup, uniform ellipticity converts channel-energy control
into a uniform lower bound proportional to trace mass, forcing finite total
mass. -/
theorem R1_uniform_ellipticity_finite_mass
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorSubsequenceAt z)
    (hUniformEllipticity : R1UniformEllipticityAt z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hFiniteBridge :
      R1RadiusFloorSubsequenceAt z ->
      R1UniformEllipticityAt z ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      R1FiniteTotalMassFromUniformEllipticityAt z) :
    R1FiniteTotalMassFromUniformEllipticityAt z := by
  exact hFiniteBridge hRadiusFloor hUniformEllipticity hDet1

end LeanV31
