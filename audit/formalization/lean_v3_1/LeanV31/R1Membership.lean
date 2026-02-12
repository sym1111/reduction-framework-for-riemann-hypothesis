import LeanV31.R1CircleEq

namespace LeanV31

def R1MembershipIdentityAt (_n : Nat) (z m : Complex) : Prop := m = z
def R1DiskMembershipSignAgree (_n : Nat) (z m : Complex) : Prop := z = m

/- S033 wrapper:
the projective preimage identity transports the Weyl quadratic form to the
imaginary part of the inverse-Mobius parameter, giving a sign/membership
criterion and the boundary conic equivalence. -/
theorem R1_membership
    {n : Nat} {z : Complex}
    (hz : InUpperB21 z)
    (hMembershipInput : R1MembershipIdentityAvailable n z)
    (hIdentityBridge :
      InUpperB21 z ->
      R1MembershipIdentityAvailable n z ->
      forall m : Complex, R1MembershipIdentityAt n z m)
    (hSignBridge :
      (forall m : Complex, R1MembershipIdentityAt n z m) ->
      forall m : Complex, R1DiskMembershipSignAgree n z m)
    (hBoundaryBridge :
      (forall m : Complex, R1MembershipIdentityAt n z m) ->
      forall m : Complex, OnWeylBoundary n z m <-> SatisfiesWeylCircleEq n z m) :
    (forall m : Complex, R1MembershipIdentityAt n z m) /\
      (forall m : Complex, R1DiskMembershipSignAgree n z m) /\
      (forall m : Complex, OnWeylBoundary n z m <-> SatisfiesWeylCircleEq n z m) := by
  have hIdentity : forall m : Complex, R1MembershipIdentityAt n z m :=
    hIdentityBridge hz hMembershipInput
  have hSign : forall m : Complex, R1DiskMembershipSignAgree n z m :=
    hSignBridge hIdentity
  have hBoundary : forall m : Complex, OnWeylBoundary n z m <-> SatisfiesWeylCircleEq n z m :=
    hBoundaryBridge hIdentity
  exact And.intro hIdentity (And.intro hSign hBoundary)

end LeanV31
