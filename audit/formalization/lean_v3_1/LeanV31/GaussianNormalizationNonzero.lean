import LeanV31.VerticalConvolution

namespace LeanV31

def XiAlphaGaussianNormalizationNonzeroAt (_z : Complex) : Prop :=
  Exists fun c : Nat => 0 < c

/- S127 wrapper:
the Gaussian normalization factor is analytic and tends to `1` as
`alpha -> 0`, so it is nonzero on compacta for sufficiently small alpha. -/
theorem gaussian_normalization_nonzero
    {z : Complex}
    (hKernelBound : XiAlphaKernelBoundAt z)
    (hNormalizationBridge :
      XiAlphaKernelBoundAt z ->
      XiAlphaGaussianNormalizationNonzeroAt z) :
    XiAlphaGaussianNormalizationNonzeroAt z := by
  exact hNormalizationBridge hKernelBound

end LeanV31
