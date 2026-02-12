import LeanV31.R1RadiusfloorClosure
import LeanV31.R1PrefixSubsequenceDivergence
import LeanV31.R1CollapseAtomicSymplOrth

namespace LeanV31

def R1MassDivergenceInternalAt (z : Complex) : Prop :=
  R1TotalMassDivergesAt z /\
    R1PrefixMassDivergesAlongSubseqAt z /\
    R1RadiusfloorClosurePrefixBoundAt z

/- S108 wrapper:
under total-mass divergence, any persistent radius-floor branch would contradict
the internal radius-floor closure bound; therefore the internal mass-divergence
criterion enforces global Weyl-radius collapse. -/
theorem R1_mass_divergence_internal
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hRadiusClosure : R1RadiusfloorClosurePrefixBoundAt z)
    (hCollapse : R1GlobalRadiusCollapseAt z) :
    R1MassDivergenceInternalAt z /\ R1GlobalRadiusCollapseAt z := by
  have hPrefixDiverges : R1PrefixMassDivergesAlongSubseqAt z :=
    R1_prefix_subsequence_divergence (z := z) hMassDiverges
  have hInternal : R1MassDivergenceInternalAt z :=
    And.intro hMassDiverges (And.intro hPrefixDiverges hRadiusClosure)
  exact And.intro hInternal hCollapse

end LeanV31
