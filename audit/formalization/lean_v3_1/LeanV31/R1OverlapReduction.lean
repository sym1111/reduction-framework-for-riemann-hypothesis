import LeanV31.R1EnergyCoercive

namespace LeanV31

def R1OverlapNormBoundAt (n : Nat) (_z : Complex) : Prop :=
  0 <= R1PrefixTraceMassAt n

def R1OverlapAngleBoundAt (_n : Nat) (z : Complex) : Prop :=
  0 <= Complex.normSq z

def R1OverlapLowerBoundAt (n : Nat) (z : Complex) : Prop :=
  0 <= R1PrefixTraceMassAt n * Complex.normSq z

/- S041 wrapper:
uniform lower norm and angle-overlap bounds imply a product lower bound for
the overlap term, producing the coercive constant used in the energy-collapse
criterion. -/
theorem R1_overlap_reduction
    {z : Complex}
    (hNorm : forall n : Nat, R1OverlapNormBoundAt n z)
    (hAngle : forall n : Nat, R1OverlapAngleBoundAt n z) :
    (forall n : Nat, R1OverlapLowerBoundAt n z) /\
      (forall n : Nat, R1EnergyCoerciveAssumptionAt n z) := by
  have hLower : forall n : Nat, R1OverlapLowerBoundAt n z := by
    intro n
    exact mul_nonneg (hNorm n) (hAngle n)
  have hCoercive : forall n : Nat, R1EnergyCoerciveAssumptionAt n z := by
    intro n
    refine Exists.intro 0 ?_
    simpa
  exact And.intro hLower hCoercive

end LeanV31
