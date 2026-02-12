import LeanV31.R1LinearTailUnderSymplecticOrth
import LeanV31.R1CS2Equiv

namespace LeanV31

def R1StructuredTailWindowBoundAt (z : Complex) : Prop :=
  R1TailWindowBoundAt z

def R1WindowSymplecticOrthAt (z : Complex) : Prop :=
  forall p q : Nat, R1SymplecticOrthogonalityAt p q z

def R1CS2StructuredTailBoundAt (z : Complex) : Prop :=
  R1CS2TailBoundAt z

def R1CS2StructuredBoundAt (z : Complex) : Prop :=
  R1CS2ConditionAt z

/- S072 wrapper:
under structured tail-window and window-level symplectic orthogonality, linear
tail control yields a polynomial CS2-tail bound and thus CS2 closure. -/
theorem R1_CS2_structured_linear
    {z : Complex}
    (hTailWindow : R1StructuredTailWindowBoundAt z)
    (hWindowOrth : R1WindowSymplecticOrthAt z)
    (hLinearBridge :
      R1StructuredTailWindowBoundAt z ->
      R1WindowSymplecticOrthAt z ->
      R1CS2StructuredTailBoundAt z)
    (hCS2Bridge :
      R1CS2StructuredTailBoundAt z ->
      R1CS2StructuredBoundAt z) :
    R1CS2StructuredTailBoundAt z /\ R1CS2StructuredBoundAt z := by
  have hTail : R1CS2StructuredTailBoundAt z := hLinearBridge hTailWindow hWindowOrth
  have hCS2 : R1CS2StructuredBoundAt z := hCS2Bridge hTail
  exact And.intro hTail hCS2

end LeanV31
