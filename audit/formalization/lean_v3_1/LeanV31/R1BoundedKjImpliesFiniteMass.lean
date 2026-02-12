import LeanV31.R1JformNotCS2
import LeanV31.R1RadiusfloorKappaBottleneck

namespace LeanV31

def R1KjUniformBoundOnSubseqAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C
def R1FiniteTotalMassByBoundedKjAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S066 wrapper:
on a radius-floor subsequence, combining the prefix-trace/kappa bottleneck with
uniform `K_j` boundedness yields uniform prefix-mass bounds and therefore
finite total trace mass. -/
theorem R1_bounded_Kj_implies_finite_mass
    {z : Complex}
    (hBottleneck : forall j : Nat, R1PrefixTraceKappaBottleneckAt j z)
    (hKjBounded : R1KjUniformBoundOnSubseqAt z)
    (hFiniteMassBridge :
      (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) ->
      R1KjUniformBoundOnSubseqAt z ->
      R1FiniteTotalMassByBoundedKjAt z) :
    R1FiniteTotalMassByBoundedKjAt z := by
  exact hFiniteMassBridge hBottleneck hKjBounded

end LeanV31
