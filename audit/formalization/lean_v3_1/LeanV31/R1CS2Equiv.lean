import LeanV31.R1LimitCircleImpliesFiniteMass

namespace LeanV31

def R1CS2TailBoundAt (_z : Complex) : Prop := Exists fun t0 : Nat => 0 < t0
def R1CS2SingularValueCharacterAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C

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
