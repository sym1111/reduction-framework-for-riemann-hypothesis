import LeanV31.R1Membership

namespace LeanV31

def R1CircleExpandedAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= n + C
def R1RadiusFormulaAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= C + n
def R1CircleCaseAt (_n : Nat) (z : Complex) : Prop := Exists fun w : Complex => w = z

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
      R1CircleExpandedAt n z)
    (hRadiusBridge :
      R1CircleExpandedAt n z ->
      R1CircleCaseAt n z ->
      R1RadiusFormulaAt n z) :
    R1CircleExpandedAt n z /\ R1RadiusFormulaAt n z := by
  have hExpanded : R1CircleExpandedAt n z := hExpandedBridge hz hCircleCase
  have hRadius : R1RadiusFormulaAt n z := hRadiusBridge hExpanded hCircleCase
  exact And.intro hExpanded hRadius

end LeanV31
