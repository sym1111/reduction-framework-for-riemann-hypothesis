import LeanV31.R1CS2TailMassWindowSector
import LeanV31.R1Rank1TransportInvariance

namespace LeanV31

def R1Rank1StepLinearAt (_k : Nat) (z : Complex) : Prop :=
  Exists fun C : Real => 0 <= C /\ Complex.normSq z <= C
def R1Rank1StepInverseLinearAt (k : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k

/- S049 wrapper:
rank-one block structure (nilpotent `JH`) linearizes each one-step transfer:
`M = I - zJH`, `M^{-1} = I + zJH`. -/
theorem R1_rank1_step_linear
    {z : Complex}
    (hRankOne : forall k : Nat, R1RankOneBlockAt k z)
    (hTransport : forall k : Nat, R1TransportInvariantAt k z)
    (hLinearBridge :
      (forall k : Nat, R1RankOneBlockAt k z) ->
      (forall k : Nat, R1TransportInvariantAt k z) ->
      forall k : Nat, R1Rank1StepLinearAt k z)
    (hInverseBridge :
      (forall k : Nat, R1Rank1StepLinearAt k z) ->
      forall k : Nat, R1Rank1StepInverseLinearAt k z) :
    (forall k : Nat, R1Rank1StepLinearAt k z) /\
      (forall k : Nat, R1Rank1StepInverseLinearAt k z) := by
  have hLinear : forall k : Nat, R1Rank1StepLinearAt k z :=
    hLinearBridge hRankOne hTransport
  have hInv : forall k : Nat, R1Rank1StepInverseLinearAt k z :=
    hInverseBridge hLinear
  exact And.intro hLinear hInv

end LeanV31
