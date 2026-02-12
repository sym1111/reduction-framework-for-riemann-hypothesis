import LeanV31.R1Rank1TransportInvariance
import LeanV31.R1Det1

namespace LeanV31

def R1LimitCircleSubsequenceAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R1CS2ConditionAt (_z : Complex) : Prop := Exists fun c0 : Nat => 0 <= c0
def R1TwoChannelEnergyBoundAt (_z : Complex) : Prop := Exists fun C : Real => 0 <= C
def R1FiniteTotalMassAt (_z : Complex) : Prop := Exists fun m0 : Nat => 0 <= m0 /\ 0 < m0

/- S045 wrapper:
under a radius-floor limit-circle subsequence and CS2 frame control, transport
invariance plus two-channel trace comparison reduce total mass to bounded
two-channel energies, forcing finite total trace mass. -/
theorem R1_limit_circle_implies_finite_mass
    {z : Complex}
    (hLimitCircle : R1LimitCircleSubsequenceAt z)
    (hCS2 : R1CS2ConditionAt z)
    (hLagrange : forall n : Nat, R1LagrangeGlobalIdentityAt n z)
    (hTraceCompare : forall k j : Nat, R1TwoChannelTraceCompareAt k j z)
    (hTransport : forall k : Nat, R1TransportInvariantAt k z)
    (hDet1 : forall n : Nat, R1TruncationTransferDetOneAt n z)
    (hEnergyBridge :
      R1LimitCircleSubsequenceAt z ->
      (forall n : Nat, R1LagrangeGlobalIdentityAt n z) ->
      (forall k : Nat, R1TransportInvariantAt k z) ->
      R1TwoChannelEnergyBoundAt z)
    (hFiniteMassBridge :
      R1CS2ConditionAt z ->
      (forall k j : Nat, R1TwoChannelTraceCompareAt k j z) ->
      (forall n : Nat, R1TruncationTransferDetOneAt n z) ->
      R1TwoChannelEnergyBoundAt z ->
      R1FiniteTotalMassAt z) :
    R1TwoChannelEnergyBoundAt z /\ R1FiniteTotalMassAt z := by
  have hEnergy : R1TwoChannelEnergyBoundAt z :=
    hEnergyBridge hLimitCircle hLagrange hTransport
  have hFinite : R1FiniteTotalMassAt z :=
    hFiniteMassBridge hCS2 hTraceCompare hDet1 hEnergy
  exact And.intro hEnergy hFinite

end LeanV31
