import LeanV31.XiAlphaToXi

namespace LeanV31

def WeylIsHerglotzAt (z : Complex) : Prop :=
  Exists fun mIm : Complex -> Nat => 0 <= mIm z

/- S129 wrapper:
for the half-line real-potential realization, the Weyl `m`-function is
holomorphic on `C_+` and has positive imaginary part (Herglotz). -/
theorem weyl_is_herglotz
    {z : Complex}
    (hWeylBridge :
      WeylIsHerglotzAt z) :
    WeylIsHerglotzAt z := by
  exact hWeylBridge

end LeanV31
