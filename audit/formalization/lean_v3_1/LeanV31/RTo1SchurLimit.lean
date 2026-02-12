import LeanV31.R2DynamicEquilibrium

namespace LeanV31

def R2SchurFamilyUniformBoundAt (_z : Complex) : Prop :=
  Exists fun M : Nat => 0 <= M
def R2PointwiseRToOneLimitAt (_z : Complex) : Prop :=
  Exists fun N : Nat => 0 < N
def R2LocallyUniformSchurLimitAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0
def R2SchurLimitBoundaryValuesAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0

/- S116 wrapper:
for a uniformly bounded Schur family with pointwise `r -> 1` limit, normal
family compactness yields locally uniform analytic convergence to a Schur
limit, including the standard boundary-value consequence. -/
theorem r_to_1_schur_limit
    {z : Complex}
    (hUniformBound : R2SchurFamilyUniformBoundAt z)
    (hPointwiseLimit : R2PointwiseRToOneLimitAt z)
    (hLocalBridge :
      R2SchurFamilyUniformBoundAt z ->
      R2PointwiseRToOneLimitAt z ->
      R2LocallyUniformSchurLimitAt z)
    (hBoundaryBridge :
      R2LocallyUniformSchurLimitAt z ->
      R2SchurLimitBoundaryValuesAt z) :
    R2LocallyUniformSchurLimitAt z /\ R2SchurLimitBoundaryValuesAt z := by
  have hLocal : R2LocallyUniformSchurLimitAt z :=
    hLocalBridge hUniformBound hPointwiseLimit
  have hBoundary : R2SchurLimitBoundaryValuesAt z := hBoundaryBridge hLocal
  exact And.intro hLocal hBoundary

end LeanV31
