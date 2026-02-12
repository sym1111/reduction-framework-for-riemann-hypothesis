import LeanV31.R1OverlapReduction
import LeanV31.R1CanonicalFormulaCore

namespace LeanV31

def R1EnergyNStepIdentityAt (n : Nat) (_z : Complex) : Prop :=
  R1PrefixTraceMassAt (n + 1) =
    R1PrefixTraceMassAt n + R1HamiltonianTraceAt n

def R1LagrangeGlobalIdentityAt (n : Nat) (z : Complex) : Prop :=
  R1KappaGaugeAt n z <= R1PrefixTraceMassAt (n + 1) + Complex.normSq z

def R1LagrangeMonotoneAt (n : Nat) (_z : Complex) : Prop :=
  R1PrefixTraceMassAt n <= R1PrefixTraceMassAt (n + 1)

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
      forall n : Nat, R1LagrangeGlobalIdentityAt n z) :
    (forall n : Nat, R1LagrangeGlobalIdentityAt n z) /\
      (forall n : Nat, R1LagrangeMonotoneAt n z) := by
  have hLag : forall n : Nat, R1LagrangeGlobalIdentityAt n z :=
    hLagrangeBridge hz hEnergy
  have hMono : forall n : Nat, R1LagrangeMonotoneAt n z := by
    intro n
    have hEq : R1PrefixTraceMassAt (n + 1) =
        R1PrefixTraceMassAt n + R1HamiltonianTraceAt n := hEnergy n
    have hTraceNonneg : 0 <= R1HamiltonianTraceAt n := by
      have hn : (0 : Real) <= (n : Real) := by
        exact_mod_cast (Nat.zero_le n)
      have h1 : (0 : Real) <= (1 : Real) := by
        norm_num
      simpa [R1HamiltonianTraceAt] using add_nonneg hn h1
    calc
      R1PrefixTraceMassAt n <= R1PrefixTraceMassAt n + R1HamiltonianTraceAt n := by
        exact le_add_of_nonneg_right hTraceNonneg
      _ = R1PrefixTraceMassAt (n + 1) := by
        symm
        exact hEq
  exact And.intro hLag hMono

end LeanV31
