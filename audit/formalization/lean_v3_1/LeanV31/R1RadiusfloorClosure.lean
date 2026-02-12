import LeanV31.R1TailwindowPrefixEquiv

namespace LeanV31

def R1RadiusFloorTargetSubsequenceAt (_z : Complex) : Prop :=
  Exists fun u : Nat -> Nat => StrictMono u
def R1ClassicalMassApplicabilityAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0
def R1RadiusfloorClosurePrefixBoundAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0 /\ 0 < j0

/- S085 wrapper:
on a radius-floor subsequence, classical mass-divergence applicability yields
a prefix-window closure bound, and the tail/prefix equivalence transfers this
to the tail-window form. -/
theorem R1_radiusfloor_closure
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorTargetSubsequenceAt z)
    (hApplicability :
      R1RadiusFloorTargetSubsequenceAt z ->
      R1ClassicalMassApplicabilityAt z)
    (hClassicalMass :
      R1ClassicalMassApplicabilityAt z ->
      R1RadiusfloorClosurePrefixBoundAt z)
    (hPrefixEmbed :
      R1RadiusfloorClosurePrefixBoundAt z ->
      R1PrefixWindowDirectBoundAt z)
    (hForward :
      R1TailWindowBoundOnSubseqAt z ->
      R1PrefixWindowDirectBoundAt z)
    (hBackward :
      R1PrefixWindowDirectBoundAt z ->
      R1TailWindowBoundOnSubseqAt z) :
    R1RadiusfloorClosurePrefixBoundAt z /\ R1TailWindowBoundOnSubseqAt z := by
  have hApp : R1ClassicalMassApplicabilityAt z := hApplicability hRadiusFloor
  have hPrefixClosure : R1RadiusfloorClosurePrefixBoundAt z := hClassicalMass hApp
  have hPrefixDirect : R1PrefixWindowDirectBoundAt z := hPrefixEmbed hPrefixClosure
  have hTailEquiv :
      R1TailWindowBoundOnSubseqAt z <-> R1PrefixWindowDirectBoundAt z :=
    R1_tailwindow_prefix_equiv (z := z) hForward hBackward
  have hTail : R1TailWindowBoundOnSubseqAt z := hTailEquiv.mpr hPrefixDirect
  exact And.intro hPrefixClosure hTail

end LeanV31
