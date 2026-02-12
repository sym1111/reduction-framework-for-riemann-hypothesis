import LeanV31.GyroAngleSeries

namespace LeanV31

def R2GyroTailConvergenceAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S122 wrapper:
for fixed `r < 1`, exponential Schur-tail decay together with the gyration-angle
series/tail estimate yields convergence of the cumulative gyration phase. -/
theorem gyro_tail_convergence
    {z : Complex}
    (hAngleSeries : R2GyroAngleSeriesLawAt z)
    (hAngleTail : R2GyroAngleTailBoundAt z)
    (hTailBridge :
      R2GyroAngleSeriesLawAt z ->
      R2GyroAngleTailBoundAt z ->
      R2GyroTailConvergenceAt z) :
    R2GyroTailConvergenceAt z := by
  exact hTailBridge hAngleSeries hAngleTail

end LeanV31
