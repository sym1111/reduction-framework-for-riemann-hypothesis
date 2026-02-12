import LeanV31.R1Det1

namespace LeanV31

def R1CircleMatrixDetFixedAt (n : Nat) (z : Complex) : Prop :=
  -(R1QtildeAt n z).det = (1 / 4 : Complex)

/- S039 wrapper:
unimodularity of truncation transfer matrices implies fixed determinant for the
Weyl-circle matrix, equivalently `-det Q~_n = 1/4` on the upper half-plane. -/
theorem R1_detQ
    {z : Complex}
    (hz : InUpperB21 z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hDetBridge :
      InUpperB21 z ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      forall n : Nat, R1CircleMatrixDetFixedAt n z) :
    forall n : Nat, R1CircleMatrixDetFixedAt n z := by
  exact hDetBridge hz hDet1

end LeanV31
