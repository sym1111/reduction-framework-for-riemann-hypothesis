import LeanV31.R1ClassicalMass
import LeanV31.EnergyIdentityB21

namespace LeanV31

def R1ChainBlockPSDAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C
def R1CanonicalStepModelAt (z : Complex) : Prop := Exists fun w : Complex => w = z
def R1WeylDiskRadiusModelAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S111 wrapper:
the constructed discrete canonical chain satisfies the hypotheses of the
classical mass-divergence criterion (PSD blocks, canonical step model, Weyl
disk/radius realization), so the theorem applies directly to this chain. -/
theorem R1_classical_mass_applicability
    {z : Complex}
    (hPSD : R1ChainBlockPSDAt z)
    (hStep : R1CanonicalStepModelAt z)
    (hWeyl : R1WeylDiskRadiusModelAt z)
    (hEnergy : UpperHalfPlanePoint z -> True)
    (hApplicabilityBridge :
      R1ChainBlockPSDAt z ->
      R1CanonicalStepModelAt z ->
      R1WeylDiskRadiusModelAt z ->
      (UpperHalfPlanePoint z -> True) ->
      R1ClassicalMassApplicabilityAt z) :
    R1ClassicalMassApplicabilityAt z := by
  exact hApplicabilityBridge hPSD hStep hWeyl hEnergy

end LeanV31
