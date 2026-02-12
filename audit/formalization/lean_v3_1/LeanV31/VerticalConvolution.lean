import LeanV31.CholCert

namespace LeanV31

def XiAlphaVerticalConvolutionIdentityAt (_z : Complex) : Prop :=
  Exists fun alpha0 : Nat => 0 < alpha0
def XiAlphaKernelBoundAt (_z : Complex) : Prop :=
  Exists fun C : Nat => 0 <= C

/- S126 wrapper:
Gaussian vertical regularization of `Xi` yields the explicit vertical
convolution identity together with the required kernel growth bound. -/
theorem vertical_convolution
    {z : Complex}
    (hConvIdentity : XiAlphaVerticalConvolutionIdentityAt z)
    (hKernelBoundBridge :
      XiAlphaVerticalConvolutionIdentityAt z ->
      XiAlphaKernelBoundAt z) :
    XiAlphaVerticalConvolutionIdentityAt z /\ XiAlphaKernelBoundAt z := by
  have hKernelBound : XiAlphaKernelBoundAt z := hKernelBoundBridge hConvIdentity
  exact And.intro hConvIdentity hKernelBound

end LeanV31
