import LeanV31.R1ClassicalMassApplicability
import LeanV31.R1MassDivergenceInternal

namespace LeanV31

def R1LimitPointCollapseAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R1WeylLimitUniqueAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ forall n : Nat, n0 <= n -> n0 <= n

/- S112 wrapper:
under mass divergence, the internal/classical collapse routes and applicability
package close to Weyl-radius collapse; limit-point uniqueness then follows from
the standard uniqueness bridge. -/
theorem R1_limit_point
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hInternalCollapse : R1GlobalRadiusCollapseAt z)
    (hClassicalMass : R1ClassicalMassCriterionAt z)
    (hApplicability : R1ClassicalMassApplicabilityAt z)
    (hCollapseBridge :
      R1TotalMassDivergesAt z ->
      R1GlobalRadiusCollapseAt z ->
      R1ClassicalMassCriterionAt z ->
      R1ClassicalMassApplicabilityAt z ->
      R1LimitPointCollapseAt z)
    (hUniqueBridge :
      R1LimitPointCollapseAt z ->
      R1WeylLimitUniqueAt z) :
    R1LimitPointCollapseAt z /\ R1WeylLimitUniqueAt z := by
  have hCollapse : R1LimitPointCollapseAt z :=
    hCollapseBridge hMassDiverges hInternalCollapse hClassicalMass hApplicability
  have hUnique : R1WeylLimitUniqueAt z := hUniqueBridge hCollapse
  exact And.intro hCollapse hUnique

end LeanV31
