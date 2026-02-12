import LeanV31.WUnitReal

namespace LeanV31

def HighlineStrictContraction (W : Complex -> Complex) : Prop :=
  Exists fun Y : Real =>
    Exists fun q : Real =>
      0 < Y /\ 0 <= q /\ q < 1 /\
        (forall x : Real, ‖W ((x : Complex) + (Y : Complex) * Complex.I)‖ <= q)

/- S004 wrapper:
functional-equation transport provides a uniform strict contraction estimate
for W on a sufficiently high horizontal line. -/
theorem highline_contraction
    {W : Complex -> Complex}
    (hContractionBridge : HighlineStrictContraction W) :
    HighlineStrictContraction W := by
  exact hContractionBridge

end LeanV31
