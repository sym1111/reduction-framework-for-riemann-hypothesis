import LeanV31.R1KappaTailExp
import LeanV31.R1TwoChannelTraceCompare

namespace LeanV31

def R1RadiusFloorSubsequenceAt (z : Complex) : Prop :=
  Exists fun u : Nat -> Nat =>
    StrictMono u /\
      Exists fun r0 : Real =>
        0 < r0 /\ forall n : Nat, r0 <= R1RadiusSequenceAt (u n) z

def R1TwoChannelEnergyWindowAt (j : Nat) (z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\
      forall n : Nat,
        j <= n ->
          Complex.normSq (R1QtildeAt n z 0 0) +
            Complex.normSq (R1QtildeAt n z 1 1) <= C

def R1PrefixTraceKappaBottleneckAt (j : Nat) (z : Complex) : Prop :=
  Exists fun C : Real =>
    0 <= C /\ R1PrefixTraceMassAt j <= C + R1KappaGaugeAt j z

def R1FrameGrowthDivergenceAt (z : Complex) : Prop :=
  forall M : Real, Exists fun j : Nat => M <= R1KappaGaugeAt j z

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
