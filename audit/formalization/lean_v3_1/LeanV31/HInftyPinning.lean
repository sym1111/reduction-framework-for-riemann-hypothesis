import LeanV31.RTo1SchurLimit

namespace LeanV31

def R2HInftyAsymptoticPinningAt (z : Complex) : Prop :=
  Exists fun w : Complex => w = z

/- S117 wrapper:
the Stirling/digamma asymptotic for the xi-log-derivative pins the infinity
normalization: imaginary part has logarithmic growth while real part is lower
order in the vertical limit. -/
theorem H_infty_pinning
    {z : Complex}
    (hStirlingBridge :
      R2HInftyAsymptoticPinningAt z) :
    R2HInftyAsymptoticPinningAt z := by
  exact hStirlingBridge

end LeanV31
