import LeanV31.R1PrefixMassCollinearVisible
import LeanV31.R1TailwindowPrefixEquiv
import LeanV31.R1CS2StructuredLagrangianLine
import LeanV31.R1CS2OnRadiusfloorTarget

namespace LeanV31

/- S088 wrapper:
collinear rank-one windows give a prefix-mass cap; by tail/prefix equivalence
this yields a structured tail-window bound, and one-line Lagrangian structure
forces the target CS2 conclusion on the radius-floor subsequence. -/
theorem R1_CS2_collinear_windows
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorTargetSubsequenceAt z)
    (hCollinear : R1CollinearWindowModelAt z)
    (hPrefixBridge :
      R1RadiusFloorTargetSubsequenceAt z ->
      R1CollinearWindowModelAt z ->
      R1PrefixMassCollinearVisibleBoundAt z)
    (hPrefixToDirect :
      R1PrefixMassCollinearVisibleBoundAt z ->
      R1PrefixWindowDirectBoundAt z)
    (hForward :
      R1TailWindowBoundOnSubseqAt z ->
      R1PrefixWindowDirectBoundAt z)
    (hBackward :
      R1PrefixWindowDirectBoundAt z ->
      R1TailWindowBoundOnSubseqAt z)
    (hTailToStructured :
      R1TailWindowBoundOnSubseqAt z ->
      R1StructuredTailWindowBoundAt z)
    (hLineBridge :
      R1CollinearWindowModelAt z ->
      R1WindowLagrangianLineAt z)
    (hOrthBridge :
      R1WindowLagrangianLineAt z ->
      R1WindowSymplecticOrthAt z)
    (hStructuredBridge :
      R1StructuredTailWindowBoundAt z ->
      R1WindowSymplecticOrthAt z ->
      R1CS2StructuredBoundAt z)
    (hStructuredToCS2 :
      R1CS2StructuredBoundAt z ->
      R1CS2ConditionAt z)
    (hTargetBridge :
      R1CS2ConditionAt z ->
      R1CS2OnRadiusfloorTargetAt z) :
    R1CS2OnRadiusfloorTargetAt z := by
  have hPrefixVisible : R1PrefixMassCollinearVisibleBoundAt z :=
    hPrefixBridge hRadiusFloor hCollinear
  have hPrefixDirect : R1PrefixWindowDirectBoundAt z := hPrefixToDirect hPrefixVisible
  have hTailEquiv :
      R1TailWindowBoundOnSubseqAt z <-> R1PrefixWindowDirectBoundAt z :=
    R1_tailwindow_prefix_equiv (z := z) hForward hBackward
  have hTail : R1TailWindowBoundOnSubseqAt z := hTailEquiv.mpr hPrefixDirect
  have hTailStructured : R1StructuredTailWindowBoundAt z := hTailToStructured hTail
  have hLine : R1WindowLagrangianLineAt z := hLineBridge hCollinear
  have hStructured :
      R1WindowSymplecticOrthAt z /\ R1CS2StructuredBoundAt z :=
    R1_CS2_structured_lagrangian_line
      (z := z) hLine hOrthBridge hStructuredBridge hTailStructured
  have hCS2 : R1CS2ConditionAt z := hStructuredToCS2 hStructured.2
  exact hTargetBridge hCS2

end LeanV31
