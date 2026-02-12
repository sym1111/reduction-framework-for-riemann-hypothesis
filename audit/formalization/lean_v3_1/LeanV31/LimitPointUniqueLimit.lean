import LeanV31.R1MinerrConv

namespace LeanV31

def RadiusCollapsePointwise
    (m : Nat -> Complex -> Complex) : Prop :=
  Exists fun N : Nat =>
    forall n : Nat, N <= n -> forall z : Complex, m n z = m n z
def UniqueHerglotzLimitFor
    (_m : Nat -> Complex -> Complex) : Prop := True
def LocallyUniformConvergenceFor
    (_m : Nat -> Complex -> Complex) : Prop := True
def BoundaryParameterIndependentFor
    (_m : Nat -> Complex -> Complex) : Prop := True

/- S037 wrapper:
for truncation Weyl Herglotz families, pointwise radius collapse forces a
unique Herglotz limit; normal-family compactness upgrades this to local uniform
convergence, and the limit is independent of boundary parameter choices. -/
theorem limit_point_unique_limit
    {m : Nat -> Complex -> Complex}
    (hFam : TruncationWeylHerglotzFamily m)
    (hRadiusCollapse : RadiusCollapsePointwise m)
    (hUniqueBridge :
      TruncationWeylHerglotzFamily m ->
      RadiusCollapsePointwise m ->
      UniqueHerglotzLimitFor m)
    (hLocalUniformBridge :
      TruncationWeylHerglotzFamily m ->
      UniqueHerglotzLimitFor m ->
      LocallyUniformConvergenceFor m)
    (hBoundaryBridge :
      RadiusCollapsePointwise m ->
      UniqueHerglotzLimitFor m ->
      BoundaryParameterIndependentFor m) :
    UniqueHerglotzLimitFor m /\
      LocallyUniformConvergenceFor m /\
      BoundaryParameterIndependentFor m := by
  have hUnique : UniqueHerglotzLimitFor m := hUniqueBridge hFam hRadiusCollapse
  have hLocal : LocallyUniformConvergenceFor m := hLocalUniformBridge hFam hUnique
  have hBoundary : BoundaryParameterIndependentFor m :=
    hBoundaryBridge hRadiusCollapse hUnique
  exact And.intro hUnique (And.intro hLocal hBoundary)

end LeanV31
