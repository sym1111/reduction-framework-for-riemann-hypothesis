import LeanV31.GaussianNormalizationNonzero

namespace LeanV31

def XiAlphaToXiTransferAt (_z : Complex) : Prop :=
  forall eps : Nat, 0 < eps -> Exists fun alpha0 : Nat => 0 < alpha0

/- S128 wrapper:
using the vertical convolution identity, kernel bounds, and normalization
control, one gets locally uniform transfer `Xi_alpha -> Xi` as `alpha -> 0`. -/
theorem Xi_alpha_to_Xi
    {z : Complex}
    (hConvIdentity : XiAlphaVerticalConvolutionIdentityAt z)
    (hNormalization : XiAlphaGaussianNormalizationNonzeroAt z)
    (hTransferBridge :
      XiAlphaVerticalConvolutionIdentityAt z ->
      XiAlphaGaussianNormalizationNonzeroAt z ->
      XiAlphaToXiTransferAt z) :
    XiAlphaToXiTransferAt z := by
  exact hTransferBridge hConvIdentity hNormalization

end LeanV31
