import LeanV31.WStripSchur

namespace LeanV31

def WGlobalSchurOnUpperHalfPlane (W : Complex -> Complex) : Prop :=
  SchurOnUpperHalfPlane W

/- S013 wrapper:
stripwise Schur control for all heights upgrades to global Schur control on
the full upper half-plane. -/
theorem W_global_schur
    {W : Complex -> Complex}
    (hStripSchur : WStripSchurOnUpperStrip W) :
    WGlobalSchurOnUpperHalfPlane W := by
  exact hStripSchur

end LeanV31
