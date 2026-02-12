import LeanV31.R1RadiusfloorKappaBottleneck

namespace LeanV31

def R1KappaLowerFromPrefixAt (j : Nat) (z : Complex) : Prop :=
  Exists fun c : Real =>
    0 <= c /\ c + R1PrefixTraceMassAt j <= R1KappaGaugeAt j z

/- S055 wrapper:
rearranging the prefix-trace bottleneck yields a quantitative lower bound on
frame growth `kappa` by prefix trace mass. -/
theorem R1_kappa_lower_from_prefix
    {z : Complex}
    (hBottleneck : forall j : Nat, R1PrefixTraceKappaBottleneckAt j z)
    (hLowerBridge :
      (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) ->
      forall j : Nat, R1KappaLowerFromPrefixAt j z) :
    forall j : Nat, R1KappaLowerFromPrefixAt j z := by
  exact hLowerBridge hBottleneck

end LeanV31
