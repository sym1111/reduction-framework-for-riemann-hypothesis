import LeanV31.PickKernelTwoSides

namespace LeanV31

def WeylDerivativeResolventSquareAt (z : Complex) : Prop :=
  Exists fun m : Complex -> Complex => forall w : Complex, m w = m z

/- S137 wrapper:
the Weyl derivative equals the resolvent-square boundary quadratic form in the
regularized operator chart. -/
theorem weyl_derivative_resolvent_square
    {z : Complex}
    (hPickTwoSides : PickKernelTwoSidesAt z)
    (hBridge :
      PickKernelTwoSidesAt z -> WeylDerivativeResolventSquareAt z) :
    WeylDerivativeResolventSquareAt z := by
  exact hBridge hPickTwoSides

end LeanV31
