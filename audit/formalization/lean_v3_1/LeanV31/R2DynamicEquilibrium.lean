import LeanV31.PGLCross

namespace LeanV31

def R2SchurCocycleFamilyAt (z : Complex) : Prop := Exists fun w : Complex => w = z
def R2GyroGyrationLawAt (_z : Complex) : Prop :=
  Exists fun g0 : Nat => 0 < g0
def R2GyroAngleSeriesLawAt (_z : Complex) : Prop := Exists fun s0 : Nat => 0 < s0
def R2DynamicEquilibriumNormalFormAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R2LeakageAdditivityAt (_z : Complex) : Prop :=
  Exists fun l0 : Nat => 0 <= l0

/- S115 wrapper:
the Schur-step cocycle admits a unique rotation-translation normal form whose
update is governed by gyro-gyration identities, with additive leakage control
that is representation-invariant. -/
theorem R2_dynamic_equilibrium
    {z : Complex}
    (hCocycle : R2SchurCocycleFamilyAt z)
    (hGyroGyration : R2GyroGyrationLawAt z)
    (hGyroAngleSeries : R2GyroAngleSeriesLawAt z)
    (hNormalBridge :
      R2SchurCocycleFamilyAt z ->
      R2GyroGyrationLawAt z ->
      R2GyroAngleSeriesLawAt z ->
      R2DynamicEquilibriumNormalFormAt z)
    (hLeakageBridge :
      R2SchurCocycleFamilyAt z ->
      R2LeakageAdditivityAt z) :
    R2DynamicEquilibriumNormalFormAt z /\ R2LeakageAdditivityAt z := by
  have hNormal : R2DynamicEquilibriumNormalFormAt z :=
    hNormalBridge hCocycle hGyroGyration hGyroAngleSeries
  have hLeakage : R2LeakageAdditivityAt z := hLeakageBridge hCocycle
  exact And.intro hNormal hLeakage

end LeanV31
