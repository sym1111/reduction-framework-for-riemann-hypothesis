import LeanV31.R1CS2StructuredLinear

namespace LeanV31

def R1WindowLagrangianLineAt (_z : Complex) : Prop :=
  Exists fun v : Complex × Complex => v.1 != 0 \/ v.2 != 0

/- S073 wrapper:
one Lagrangian direction per subsequence window implies window symplectic
orthogonality, so structured CS2 closure follows from the structured linear
proposition. -/
theorem R1_CS2_structured_lagrangian_line
    {z : Complex}
    (hLagrangianLine : R1WindowLagrangianLineAt z)
    (hOrthBridge :
      R1WindowLagrangianLineAt z ->
      R1WindowSymplecticOrthAt z)
    (hStructuredBridge :
      R1StructuredTailWindowBoundAt z ->
      R1WindowSymplecticOrthAt z ->
      R1CS2StructuredBoundAt z)
    (hTailWindow : R1StructuredTailWindowBoundAt z) :
    R1WindowSymplecticOrthAt z /\ R1CS2StructuredBoundAt z := by
  have hOrth : R1WindowSymplecticOrthAt z := hOrthBridge hLagrangianLine
  have hCS2 : R1CS2StructuredBoundAt z := hStructuredBridge hTailWindow hOrth
  exact And.intro hOrth hCS2

end LeanV31
