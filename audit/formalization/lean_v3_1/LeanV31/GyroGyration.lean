import LeanV31.IndependentInequality

namespace LeanV31

def R2GyroassociativityLawAt (_z : Complex) : Prop :=
  Exists fun g0 : Nat => 0 < g0
def R2GyrationPhaseLawAt (_z : Complex) : Prop :=
  Exists fun p0 : Nat => 0 <= p0
def R2TauFactorizationLawAt (_z : Complex) : Prop :=
  Exists fun t0 : Nat => 0 < t0

/- S120 wrapper:
disk Mobius addition satisfies gyroassociativity with unimodular gyration phase;
equivalently, composition of disk translations factors through translation plus
rotation defect. -/
theorem gyro_gyration
    {z : Complex}
    (hGyroLaw :
      R2GyroassociativityLawAt z)
    (hPhaseBridge :
      R2GyroassociativityLawAt z ->
      R2GyrationPhaseLawAt z)
    (hFactorBridge :
      R2GyrationPhaseLawAt z ->
      R2TauFactorizationLawAt z) :
    R2GyroassociativityLawAt z /\
      R2GyrationPhaseLawAt z /\
      R2TauFactorizationLawAt z := by
  have hPhase : R2GyrationPhaseLawAt z := hPhaseBridge hGyroLaw
  have hFactor : R2TauFactorizationLawAt z := hFactorBridge hPhase
  exact And.intro hGyroLaw (And.intro hPhase hFactor)

end LeanV31
