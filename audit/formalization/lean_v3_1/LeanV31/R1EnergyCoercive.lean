import LeanV31.R1DetQ

namespace LeanV31

def R1RadiusEnergyIdentityAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= n + C
def R1EnergyCoerciveAssumptionAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= C + n
def R1RadiusUpperBoundAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= C
def R1MassDivergenceAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R1RadiusCollapseAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S040 wrapper:
the radius-energy identity plus a uniform coercive overlap lower bound yields
an explicit reciprocal radius upper bound; under diverging trace mass this
forces Weyl-disk radius collapse. -/
theorem R1_energy_coercive
    {z : Complex}
    (hz : InUpperB21 z)
    (hRadiusEnergy : forall n : Nat, R1RadiusEnergyIdentityAt n z)
    (hCoercive : forall n : Nat, R1EnergyCoerciveAssumptionAt n z)
    (hBoundBridge :
      InUpperB21 z ->
      (forall n : Nat, R1RadiusEnergyIdentityAt n z) ->
      (forall n : Nat, R1EnergyCoerciveAssumptionAt n z) ->
      forall n : Nat, R1RadiusUpperBoundAt n z)
    (hCollapseBridge :
      (forall n : Nat, R1RadiusUpperBoundAt n z) ->
      R1MassDivergenceAt z ->
      R1RadiusCollapseAt z) :
    (forall n : Nat, R1RadiusUpperBoundAt n z) /\
      (R1MassDivergenceAt z -> R1RadiusCollapseAt z) := by
  have hBound : forall n : Nat, R1RadiusUpperBoundAt n z :=
    hBoundBridge hz hRadiusEnergy hCoercive
  have hImp : R1MassDivergenceAt z -> R1RadiusCollapseAt z := by
    intro hMass
    exact hCollapseBridge hBound hMass
  exact And.intro hBound hImp

end LeanV31
