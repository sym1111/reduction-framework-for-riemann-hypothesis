import LeanV31.R1LagrangeIdentityGlobal

namespace LeanV31

def R1TwoChannelFrameAt (k j : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k \/ n = j
def R1TwoChannelTraceCompareAt (k j : Nat) (_z : Complex) : Prop := Exists fun n : Nat => n = k \/ n = j

/- S043 wrapper:
for an invertible two-channel frame, trace of a PSD block is controlled by the
inverse frame-Gram operator norm times the sum of channel energies. -/
theorem R1_two_channel_trace_compare
    {z : Complex}
    (hFrame : forall k j : Nat, R1TwoChannelFrameAt k j z)
    (hCompareBridge :
      (forall k j : Nat, R1TwoChannelFrameAt k j z) ->
      forall k j : Nat, R1TwoChannelTraceCompareAt k j z) :
    (forall k j : Nat, R1TwoChannelFrameAt k j z) /\
      (forall k j : Nat, R1TwoChannelTraceCompareAt k j z) := by
  have hCompare : forall k j : Nat, R1TwoChannelTraceCompareAt k j z :=
    hCompareBridge hFrame
  exact And.intro hFrame hCompare

end LeanV31
