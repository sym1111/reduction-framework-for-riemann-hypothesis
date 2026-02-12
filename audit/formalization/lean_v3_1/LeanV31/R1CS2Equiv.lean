import LeanV31.R1LimitCircleImpliesFiniteMass

namespace LeanV31

def R1CS2TailBoundAt (z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\ forall n : Nat, R1RadiusSequenceAt n z <= C

def R1CS2SingularValueCharacterAt (z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\
      forall n : Nat,
        Complex.normSq (R1QtildeAt n z 0 0) +
          Complex.normSq (R1QtildeAt n z 1 1) <= C

/- S046 wrapper:
using determinant-one cocycle structure, CS2 is equivalent to the tail-cocycle
inverse-norm bound; singular-value identities encode this equivalence. -/
theorem R1_CS2_equiv
    {z : Complex}
    (hCS2 : R1CS2ConditionAt z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hSingularBridge :
      R1CS2ConditionAt z ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      R1CS2SingularValueCharacterAt z)
    (hTailBridge :
      R1CS2SingularValueCharacterAt z ->
      (R1CS2ConditionAt z <-> R1CS2TailBoundAt z)) :
    R1CS2SingularValueCharacterAt z /\
      (R1CS2ConditionAt z <-> R1CS2TailBoundAt z) := by
  have hChar : R1CS2SingularValueCharacterAt z := hSingularBridge hCS2 hDet1
  have hEquiv : R1CS2ConditionAt z <-> R1CS2TailBoundAt z := hTailBridge hChar
  exact And.intro hChar hEquiv

end LeanV31
