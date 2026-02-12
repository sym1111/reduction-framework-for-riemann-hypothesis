import LeanV31.LocalGreenBridgeIdentity

namespace LeanV31

def CalibKernelMatchAt (z : Complex) : Prop :=
  Exists fun w : Complex => w = z

/- S135 wrapper:
the local Green bridge identity yields the local calibration kernel-matching
input used by the Weyl calibration block. -/
theorem calib_kernel_match
    {z : Complex}
    (hLocalGreen : LocalGreenBridgeIdentityAt z)
    (hBridge :
      LocalGreenBridgeIdentityAt z -> CalibKernelMatchAt z) :
    CalibKernelMatchAt z := by
  exact hBridge hLocalGreen

end LeanV31
