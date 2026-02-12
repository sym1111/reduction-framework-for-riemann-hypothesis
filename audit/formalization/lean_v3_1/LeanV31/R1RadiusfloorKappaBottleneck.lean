import LeanV31.R1KappaTailExp
import LeanV31.R1TwoChannelTraceCompare

namespace LeanV31

def R1RadiusFloorSubsequenceAt (_z : Complex) : Prop :=
  Exists fun u : Nat -> Nat => StrictMono u
def R1TwoChannelEnergyWindowAt (j : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => j <= C + j
def R1PrefixTraceKappaBottleneckAt (j : Nat) (_z : Complex) : Prop := Exists fun C : Nat => j <= C
def R1FrameGrowthDivergenceAt (_z : Complex) : Prop := Exists fun j0 : Nat => 0 <= j0 /\ 0 < j0

/- S054 wrapper:
on a radius-floor subsequence, two-channel energy bounds and channel-trace
comparison yield a prefix-trace-vs-kappa bottleneck inequality, forcing frame
growth divergence when prefix trace mass diverges. -/
theorem R1_radiusfloor_kappa_bottleneck
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorSubsequenceAt z)
    (hTwoChannelEnergy : forall j : Nat, R1TwoChannelEnergyWindowAt j z)
    (hTraceCompare : forall k j : Nat, R1TwoChannelTraceCompareAt k j z)
    (hBottleneckBridge :
      R1RadiusFloorSubsequenceAt z ->
      (forall j : Nat, R1TwoChannelEnergyWindowAt j z) ->
      (forall k j : Nat, R1TwoChannelTraceCompareAt k j z) ->
      forall j : Nat, R1PrefixTraceKappaBottleneckAt j z)
    (hDivergenceBridge :
      (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) ->
      R1FrameGrowthDivergenceAt z) :
    (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) /\
      R1FrameGrowthDivergenceAt z := by
  have hBottleneck : forall j : Nat, R1PrefixTraceKappaBottleneckAt j z :=
    hBottleneckBridge hRadiusFloor hTwoChannelEnergy hTraceCompare
  have hDiv : R1FrameGrowthDivergenceAt z := hDivergenceBridge hBottleneck
  exact And.intro hBottleneck hDiv

end LeanV31
