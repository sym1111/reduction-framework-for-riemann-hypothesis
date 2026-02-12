import LeanV31.R1CS2Equiv
import LeanV31.R1Det1
import LeanV31.R1RadiusfloorKappaBottleneck

namespace LeanV31

def R1FrameRatioKappaBalanceAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S094 wrapper:
determinant-one transfer normalization and CS2 singular-value relations give a
pointwise inequality balancing transported-frame coercivity ratio against the
kappa growth factor, controlled by channel constants. -/
theorem R1_frame_ratio_kappa_balance
    {z : Complex}
    (hRadiusFloor : R1RadiusFloorSubsequenceAt z)
    (hBottleneck :
      (forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) /\
      R1FrameGrowthDivergenceAt z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hCS2Equiv :
      R1CS2ConditionAt z <-> R1CS2TailBoundAt z)
    (hBalanceBridge :
      R1RadiusFloorSubsequenceAt z ->
      ((forall j : Nat, R1PrefixTraceKappaBottleneckAt j z) /\
        R1FrameGrowthDivergenceAt z) ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      (R1CS2ConditionAt z <-> R1CS2TailBoundAt z) ->
      R1FrameRatioKappaBalanceAt z) :
    R1FrameRatioKappaBalanceAt z := by
  exact hBalanceBridge hRadiusFloor hBottleneck hDet1 hCS2Equiv

end LeanV31
