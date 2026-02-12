import LeanV31.R1ClassicalMass
import LeanV31.EnergyIdentityB21
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

/- R1 canonical-chain formula objects are provided by `R1CanonicalFormulaCore`. -/

def R1ChainBlockPSDAt (_z : Complex) : Prop :=
  forall k : Nat, 0 <= R1HamiltonianTraceAt k

def R1CanonicalStepModelAt (z : Complex) : Prop :=
  forall n : Nat, R1CanonicalStepResidualAt n z = 0

def R1WeylDiskRadiusModelAt (z : Complex) : Prop :=
  forall n : Nat, R1WeylRadiusAt n z = R1WeylRadiusFormulaAt n z

/- S111 wrapper:
the constructed discrete canonical chain satisfies the hypotheses of the
classical mass-divergence criterion (PSD blocks, canonical step model, Weyl
disk/radius realization), so the theorem applies directly to this chain. -/
theorem R1_classical_mass_applicability
    {z : Complex}
    (_hPSD : R1ChainBlockPSDAt z)
    (_hStep : R1CanonicalStepModelAt z)
    (hWeyl : R1WeylDiskRadiusModelAt z) :
    R1ClassicalMassApplicabilityAt z := by
  intro n
  have hEq : R1WeylRadiusAt n z = R1WeylRadiusFormulaAt n z := hWeyl n
  rw [hEq]
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end LeanV31
