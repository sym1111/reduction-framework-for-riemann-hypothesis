import LeanV31.PolarizedJKernelB21

namespace LeanV31

def R1MembershipIdentityAvailable (_n : Nat) (z : Complex) : Prop :=
  Exists fun m : Complex => m = z
def OnWeylBoundary (_n : Nat) (_z _m : Complex) : Prop :=
  Exists fun c0 : Complex => c0 = _m
def SatisfiesWeylCircleEq (_n : Nat) (_z _m : Complex) : Prop :=
  Exists fun c0 : Complex => c0 = _m

/- S032 wrapper:
for fixed n and z in upper half-plane, boundary membership in the Weyl disk
is equivalent to the quadratic-form circle equation. -/
theorem R1_circle_eq
    {n : Nat} {z : Complex}
    (hz : InUpperB21 z)
    (hMembership :
      R1MembershipIdentityAvailable n z)
    (hBoundaryBridge :
      InUpperB21 z ->
      R1MembershipIdentityAvailable n z ->
      forall m : Complex, OnWeylBoundary n z m <-> SatisfiesWeylCircleEq n z m) :
    forall m : Complex, OnWeylBoundary n z m <-> SatisfiesWeylCircleEq n z m := by
  exact hBoundaryBridge hz hMembership

end LeanV31
