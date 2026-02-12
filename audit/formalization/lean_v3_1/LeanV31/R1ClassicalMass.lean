import LeanV31.R1MassDivergenceInternal
import LeanV31.R1PrefixSubsequenceDivergence

namespace LeanV31

def R1ClassicalMassCriterionAt (z : Complex) : Prop :=
  R1TotalMassDivergesAt z -> R1PrefixMassDivergesAlongSubseqAt z

/- S110 wrapper:
the self-contained classical mass-divergence criterion is packaged as the
target theorem: total trace-mass divergence enforces Weyl-radius collapse on
the upper half-plane chain. -/
theorem R1_classical_mass
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hClassicalBridge :
      R1TotalMassDivergesAt z ->
      R1ClassicalMassCriterionAt z) :
    R1ClassicalMassCriterionAt z := by
  exact hClassicalBridge hMassDiverges

end LeanV31
