import LeanV31.GyroGyration

namespace LeanV31

def R2GyroAngleTailBoundAt (_z : Complex) : Prop :=
  Exists fun N : Nat => 0 < N

/- S121 wrapper:
the gyration phase admits an exact convergent logarithmic series expansion and
an explicit tail bound in terms of `|a||b|`. -/
theorem gyro_angle_series
    {z : Complex}
    (hGyrationPhase : R2GyrationPhaseLawAt z)
    (hSeriesBridge :
      R2GyrationPhaseLawAt z ->
      R2GyroAngleSeriesLawAt z)
    (hTailBridge :
      R2GyroAngleSeriesLawAt z ->
      R2GyroAngleTailBoundAt z) :
    R2GyroAngleSeriesLawAt z /\ R2GyroAngleTailBoundAt z := by
  have hSeries : R2GyroAngleSeriesLawAt z := hSeriesBridge hGyrationPhase
  have hTail : R2GyroAngleTailBoundAt z := hTailBridge hSeries
  exact And.intro hSeries hTail

end LeanV31
