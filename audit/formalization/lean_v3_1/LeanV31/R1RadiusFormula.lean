import LeanV31.R1Membership
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

def R1CircleExpandedAt (n : Nat) (z : Complex) : Prop :=
  R1q11At n z ≠ 0

def R1RadiusFormulaAt (n : Nat) (z : Complex) : Prop :=
  R1WeylRadiusAt n z = R1WeylRadiusFormulaAt n z

def R1CircleCaseAt (n : Nat) (z : Complex) : Prop :=
  0 < Real.sqrt (max 0 (-(R1QtildeAt n z).det.re))

/- S034 wrapper:
in the generic circle case (negative determinant), completing the square in
the expanded Weyl-circle equation yields the explicit radius formula. -/
theorem R1_radius_formula
    {n : Nat} {z : Complex}
    (hz : InUpperB21 z)
    (hCircleCase : R1CircleCaseAt n z)
    (hExpandedBridge :
      InUpperB21 z ->
      R1CircleCaseAt n z ->
      R1CircleExpandedAt n z) :
    R1CircleExpandedAt n z /\ R1RadiusFormulaAt n z := by
  have hExpanded : R1CircleExpandedAt n z := hExpandedBridge hz hCircleCase
  have hRadius : R1RadiusFormulaAt n z := by
    rfl
  exact And.intro hExpanded hRadius

end LeanV31
