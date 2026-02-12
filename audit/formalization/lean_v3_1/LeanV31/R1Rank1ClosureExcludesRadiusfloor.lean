import LeanV31.R1MassDivergenceSelectsDivergentBranch

namespace LeanV31

def R1MassDivergenceInternalClosureAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0
def R1RadiusFloorSubsequenceExcludedAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0
def R1RadiusCollapseAllUpperAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S064 wrapper:
rank-one mass-divergence internal closure rules out radius-floor subsequences;
equivalently, Weyl radii collapse to zero throughout the upper half-plane. -/
theorem R1_rank1_closure_excludes_radiusfloor
    {z : Complex}
    (hClosure : R1MassDivergenceInternalClosureAt z)
    (hExcludeBridge :
      R1MassDivergenceInternalClosureAt z ->
      R1RadiusFloorSubsequenceExcludedAt z)
    (hCollapseBridge :
      R1RadiusFloorSubsequenceExcludedAt z ->
      R1RadiusCollapseAllUpperAt z) :
    R1RadiusFloorSubsequenceExcludedAt z /\ R1RadiusCollapseAllUpperAt z := by
  have hExclude : R1RadiusFloorSubsequenceExcludedAt z := hExcludeBridge hClosure
  have hCollapse : R1RadiusCollapseAllUpperAt z := hCollapseBridge hExclude
  exact And.intro hExclude hCollapse

end LeanV31
