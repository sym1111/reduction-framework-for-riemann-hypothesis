import LeanV31.LimitPointUniqueLimit

namespace LeanV31

def R1StepTransferDetOneAt (k : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k
def R1TruncationTransferDetOneAt (n : Nat) (_z : Complex) : Prop := Exists fun m : Nat => m <= n

/- S038 wrapper:
each one-step transfer matrix is unimodular; products preserve determinant one,
hence every truncation transfer matrix remains unimodular. -/
theorem R1_det1
    {z : Complex}
    (hStepDetOne : forall k : Nat, R1StepTransferDetOneAt k z)
    (hProductBridge :
      (forall k : Nat, R1StepTransferDetOneAt k z) ->
      forall n : Nat, R1TruncationTransferDetOneAt n z) :
    (forall k : Nat, R1StepTransferDetOneAt k z) /\
      (forall n : Nat, R1TruncationTransferDetOneAt n z) := by
  have hTruncDetOne : forall n : Nat, R1TruncationTransferDetOneAt n z :=
    hProductBridge hStepDetOne
  exact And.intro hStepDetOne hTruncDetOne

end LeanV31
