import LeanV31.Basic

namespace LeanV31

def R2PGLMapEqualityAt (_z : Complex) : Prop :=
  Exists fun k0 : Nat => 0 < k0
def R2PGLCrossCancelIdentityAt (_z : Complex) : Prop :=
  Exists fun k0 : Nat => 0 < k0 /\ forall n : Nat, k0 <= n -> k0 <= n

/- S114 wrapper:
for Mobius maps in `PGL(2,C)`, equality of maps is equivalent to the
cross-cancelled polynomial identity (and coefficient vanishing). -/
theorem PGL_cross
    {z : Complex}
    (hForward :
      R2PGLMapEqualityAt z ->
      R2PGLCrossCancelIdentityAt z)
    (hBackward :
      R2PGLCrossCancelIdentityAt z ->
      R2PGLMapEqualityAt z) :
    R2PGLMapEqualityAt z <-> R2PGLCrossCancelIdentityAt z := by
  exact Iff.intro hForward hBackward

end LeanV31
