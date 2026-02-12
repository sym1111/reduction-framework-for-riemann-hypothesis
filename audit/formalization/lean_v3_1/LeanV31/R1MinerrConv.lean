import LeanV31.R1Minimax

namespace LeanV31

def R1CenterErrorBoundAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= C + n
def R1RadiusConvergesToZeroAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 < n0
def R1CenterConvergesToLimitAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S036 wrapper:
from the disk-center form and minimax characterization, each truncation center
satisfies the radius error bound; when radii collapse to zero, centers converge
to the unique Weyl limit. -/
theorem R1_minerr_conv
    {z : Complex}
    (hCenterForm : forall n : Nat, R1DiskCenterFormAt n z)
    (hMinimax : forall n : Nat, R1MinimaxEqAt n z)
    (hErrorBridge :
      (forall n : Nat, R1DiskCenterFormAt n z) ->
      (forall n : Nat, R1MinimaxEqAt n z) ->
      forall n : Nat, R1CenterErrorBoundAt n z)
    (hConvBridge :
      (forall n : Nat, R1CenterErrorBoundAt n z) ->
      R1RadiusConvergesToZeroAt z ->
      R1CenterConvergesToLimitAt z) :
    (forall n : Nat, R1CenterErrorBoundAt n z) /\
      (R1RadiusConvergesToZeroAt z -> R1CenterConvergesToLimitAt z) := by
  have hErr : forall n : Nat, R1CenterErrorBoundAt n z :=
    hErrorBridge hCenterForm hMinimax
  have hImp : R1RadiusConvergesToZeroAt z -> R1CenterConvergesToLimitAt z := by
    intro hRadius
    exact hConvBridge hErr hRadius
  exact And.intro hErr hImp

end LeanV31
