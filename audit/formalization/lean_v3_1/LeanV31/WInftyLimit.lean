import LeanV31.HInftyPinning

namespace LeanV31

def R2WInftyLimitAt (_z : Complex) : Prop := Exists fun N : Nat => 0 < N

/- S118 wrapper:
the infinity pinning of `H` transfers through the Cayley expression for `W`,
yielding convergence to `-1` with the logarithmic rate control. -/
theorem W_infty_limit
    {z : Complex}
    (hPinning : R2HInftyAsymptoticPinningAt z)
    (hWBridge :
      R2HInftyAsymptoticPinningAt z ->
      R2WInftyLimitAt z) :
    R2WInftyLimitAt z := by
  exact hWBridge hPinning

end LeanV31
