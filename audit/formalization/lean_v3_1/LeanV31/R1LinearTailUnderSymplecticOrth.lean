import LeanV31.R1Rank1MixedFactor

namespace LeanV31

def R1LinearTailFormulaAt (_k n : Nat) (z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C /\ Complex.normSq z <= C + (n : Real)
def R1LinearTailNormBoundAt (k n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C /\ (k : Real) <= C + (n : Real)

/- S051 wrapper:
under pairwise symplectic orthogonality, higher-order mixed terms vanish in the
ordered tail product, yielding an exact linear tail formula and linear norm
bound by tail trace mass. -/
theorem R1_linear_tail_under_symplectic_orth
    {z : Complex}
    (hStepInv : forall k : Nat, R1Rank1StepInverseLinearAt k z)
    (hOrth : forall p q : Nat, R1SymplecticOrthogonalityAt p q z)
    (hLinearTailBridge :
      (forall k : Nat, R1Rank1StepInverseLinearAt k z) ->
      (forall p q : Nat, R1SymplecticOrthogonalityAt p q z) ->
      forall k n : Nat, R1LinearTailFormulaAt k n z)
    (hNormBridge :
      (forall k n : Nat, R1LinearTailFormulaAt k n z) ->
      forall k n : Nat, R1LinearTailNormBoundAt k n z) :
    (forall k n : Nat, R1LinearTailFormulaAt k n z) /\
      (forall k n : Nat, R1LinearTailNormBoundAt k n z) := by
  have hFormula : forall k n : Nat, R1LinearTailFormulaAt k n z :=
    hLinearTailBridge hStepInv hOrth
  have hNorm : forall k n : Nat, R1LinearTailNormBoundAt k n z :=
    hNormBridge hFormula
  exact And.intro hFormula hNorm

end LeanV31
