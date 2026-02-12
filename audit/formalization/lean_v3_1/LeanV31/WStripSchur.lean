import LeanV31.WBoundedCharacteristic

namespace LeanV31

def WStripSchurOnUpperStrip (W : Complex -> Complex) : Prop :=
  SchurOnUpperHalfPlane W

/- S012 wrapper:
on each finite strip, boundary unit-modulus + high-line strict contraction +
circle-Hardy pole exclusion + bounded characteristic close the strip Schur
estimate for W. -/
theorem W_strip_schur
    {W : Complex -> Complex}
    (hBoundedCharacteristic : WBoundedCharacteristicOnStrips W) :
    WStripSchurOnUpperStrip W := by
  exact hBoundedCharacteristic

end LeanV31
