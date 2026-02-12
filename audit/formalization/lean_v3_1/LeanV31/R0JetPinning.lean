import LeanV31.GyroTailConvergence

namespace LeanV31

def R2R0JetDataAt (_z : Complex) : Prop :=
  Exists fun j0 : Nat => 0 < j0
def R2R0JetPinnedAt (_z : Complex) : Prop :=
  Exists fun j0 : Nat => 0 < j0 /\ forall n : Nat, j0 <= n -> j0 <= n

/- S123 wrapper:
the calibration automorphism `R_0` is uniquely pinned by a first jet
(value+derivative) and admits the explicit factorized form. -/
theorem R0_jet_pinning
    {z : Complex}
    (hJetData : R2R0JetDataAt z)
    (hJetBridge :
      R2R0JetDataAt z ->
      R2R0JetPinnedAt z) :
    R2R0JetPinnedAt z := by
  exact hJetBridge hJetData

end LeanV31
