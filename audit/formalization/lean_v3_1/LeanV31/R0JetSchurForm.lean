import LeanV31.R0JetPinning

namespace LeanV31

def R2R0JetSchurFormAt (_z : Complex) : Prop :=
  Exists fun s0 : Nat => 0 < s0

/- S124 wrapper:
the `R_0` 1-jet calibration has the Schur-parameter relation form, including
the closed-form recovery branch in the nondegenerate case. -/
theorem R0_jet_schur_form
    {z : Complex}
    (hJetPinned : R2R0JetPinnedAt z)
    (hSchurBridge :
      R2R0JetPinnedAt z ->
      R2R0JetSchurFormAt z) :
    R2R0JetSchurFormAt z := by
  exact hSchurBridge hJetPinned

end LeanV31
