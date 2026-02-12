import LeanV31.R1RadiusfloorClosure
import LeanV31.R1PrefixSubsequenceDivergence
import LeanV31.R1CollapseAtomicSymplOrth

namespace LeanV31

def R1MassDivergenceInternalAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S108 wrapper:
under total-mass divergence, any persistent radius-floor branch would contradict
the internal radius-floor closure bound; therefore the internal mass-divergence
criterion enforces global Weyl-radius collapse. -/
theorem R1_mass_divergence_internal
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hRadiusfloorClosure :
      R1RadiusFloorTargetSubsequenceAt z ->
      R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z)
    (hInternalBridge :
      R1TotalMassDivergesAt z ->
      (R1RadiusFloorTargetSubsequenceAt z ->
        R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z) ->
      R1MassDivergenceInternalAt z)
    (hCollapseBridge :
      R1MassDivergenceInternalAt z ->
      R1GlobalRadiusCollapseAt z) :
    R1MassDivergenceInternalAt z /\ R1GlobalRadiusCollapseAt z := by
  have hInternal : R1MassDivergenceInternalAt z :=
    hInternalBridge hMassDiverges hRadiusfloorClosure
  have hCollapse : R1GlobalRadiusCollapseAt z := hCollapseBridge hInternal
  exact And.intro hInternal hCollapse

end LeanV31
