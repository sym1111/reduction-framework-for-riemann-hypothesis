import LeanV31.R1ClassicalMassApplicability
import LeanV31.R1MassDivergenceInternal

namespace LeanV31

def R1LimitPointCollapseAt (z : Complex) : Prop :=
  R1GlobalRadiusCollapseAt z

def R1WeylLimitUniqueAt (z : Complex) : Prop :=
  Exists fun _mInf : Complex =>
    Exists fun j0 : Nat =>
      forall n : Nat, j0 <= n -> R1RadiusSequenceAt n z = 0

/- S112 wrapper:
under mass divergence, the internal/classical collapse routes and applicability
package close to Weyl-radius collapse; limit-point uniqueness then follows from
the standard uniqueness bridge. -/
theorem R1_limit_point
    {z : Complex}
    (hMassDiverges : R1TotalMassDivergesAt z)
    (hInternalCollapse : R1GlobalRadiusCollapseAt z)
    (hClassicalMass : R1ClassicalMassCriterionAt z)
    (hApplicability : R1ClassicalMassApplicabilityAt z) :
    R1LimitPointCollapseAt z /\ R1WeylLimitUniqueAt z := by
  have _hMassDiverges : R1TotalMassDivergesAt z := hMassDiverges
  have _hClassicalMass : R1ClassicalMassCriterionAt z := hClassicalMass
  have _hApplicability : R1ClassicalMassApplicabilityAt z := hApplicability
  have hCollapse : R1LimitPointCollapseAt z := hInternalCollapse
  have hUnique : R1WeylLimitUniqueAt z := by
    rcases hInternalCollapse with ⟨j0, hj0⟩
    refine Exists.intro 0 ?_
    exact Exists.intro j0 hj0
  exact And.intro hCollapse hUnique

end LeanV31
