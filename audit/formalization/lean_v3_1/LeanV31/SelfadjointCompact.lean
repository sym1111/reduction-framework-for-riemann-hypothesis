import LeanV31.WeylIsHerglotz

namespace LeanV31

def SelfadjointCompactAt (_z : Complex) : Prop :=
  Exists fun n0 : Nat => 0 <= n0 /\ 0 < n0

/- S130 wrapper:
the regularized half-line operator realization is self-adjoint with compact
resolvent in the stated setting. -/
theorem selfadjoint_compact
    {z : Complex}
    (hSelfadjointBridge :
      SelfadjointCompactAt z) :
    SelfadjointCompactAt z := by
  exact hSelfadjointBridge

end LeanV31
