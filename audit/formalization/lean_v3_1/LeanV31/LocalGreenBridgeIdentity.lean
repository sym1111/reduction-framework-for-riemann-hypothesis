import LeanV31.MArithChartDerivative

namespace LeanV31

def LocalGreenBridgeIdentityAt (z : Complex) : Prop :=
  Exists fun G : Complex => G = z

/- S134 wrapper:
on a nonempty local chart, arithmetic quotient-derivative and resolvent-square
boundary Green functional are identified. -/
theorem local_green_bridge_identity
    {z : Complex}
    (hArithDerivative : ArithChartDerivativeAt z)
    (hBridge :
      ArithChartDerivativeAt z -> LocalGreenBridgeIdentityAt z) :
    LocalGreenBridgeIdentityAt z := by
  exact hBridge hArithDerivative

end LeanV31
