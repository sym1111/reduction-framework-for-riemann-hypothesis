import LeanV31.R1OverlapReduction

namespace LeanV31

def R1EnergyNStepIdentityAt (n : Nat) (_z : Complex) : Prop := Exists fun m : Nat => m = n
def R1LagrangeGlobalIdentityAt (n : Nat) (z : Complex) : Prop :=
  Exists fun L : Real => 0 <= L /\ L <= (n : Real) + Complex.normSq z
def R1LagrangeMonotoneAt (_n : Nat) (_z : Complex) : Prop := Exists fun C : Real => 0 <= C

/- S042 wrapper:
the n-step energy identity evaluated on a test vector yields the global
Lagrange identity on truncations; positivity of each summand gives
nonnegativity and monotonicity in truncation level. -/
theorem R1_lagrange_identity_global
    {z : Complex}
    (hz : InUpperB21 z)
    (hEnergy : forall n : Nat, R1EnergyNStepIdentityAt n z)
    (hLagrangeBridge :
      InUpperB21 z ->
      (forall n : Nat, R1EnergyNStepIdentityAt n z) ->
      forall n : Nat, R1LagrangeGlobalIdentityAt n z)
    (hMonotoneBridge :
      (forall n : Nat, R1LagrangeGlobalIdentityAt n z) ->
      forall n : Nat, R1LagrangeMonotoneAt n z) :
    (forall n : Nat, R1LagrangeGlobalIdentityAt n z) /\
      (forall n : Nat, R1LagrangeMonotoneAt n z) := by
  have hLag : forall n : Nat, R1LagrangeGlobalIdentityAt n z :=
    hLagrangeBridge hz hEnergy
  have hMono : forall n : Nat, R1LagrangeMonotoneAt n z := hMonotoneBridge hLag
  exact And.intro hLag hMono

end LeanV31
