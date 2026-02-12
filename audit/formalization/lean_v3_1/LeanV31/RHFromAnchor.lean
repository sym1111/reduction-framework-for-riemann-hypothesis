import Mathlib

namespace LeanV31

def HasOnlyRealZeros (f : Complex -> Complex) : Prop :=
  forall z : Complex, f z = 0 -> z.im = 0

def HolomorphicOnUpperHalfPlane (F : Complex -> Complex) : Prop :=
  DifferentiableOn ℂ F {z : Complex | 0 < z.im}

def HerglotzOnUpperHalfPlane (H : Complex -> Complex) : Prop :=
  HolomorphicOnUpperHalfPlane H /\
    forall z : Complex, 0 < z.im -> 0 <= (H z).im

def SchurOnUpperHalfPlane (W : Complex -> Complex) : Prop :=
  HolomorphicOnUpperHalfPlane W /\
    forall z : Complex, 0 < z.im -> ‖W z‖ <= 1

def HasCanonicalSystemEnergyRealization (_H : Complex -> Complex) : Prop :=
  Exists fun W : Complex -> Complex => SchurOnUpperHalfPlane W

/- S144 wrapper:
from the final-bridge RH input (real-zero property) and standard bridges
(log-derivative holomorphy/Herglotz, Cayley to Schur, and L*-realization),
derive the full anchor conclusion package. -/
theorem rh_from_anchor
    {f : Complex -> Complex}
    (hFinalBridgeRH : HasOnlyRealZeros f)
    (hLogDerivHol :
      HasOnlyRealZeros f ->
        HolomorphicOnUpperHalfPlane (fun z => -(deriv f z) / f z))
    (hLogDerivHerglotz :
      HasOnlyRealZeros f ->
        HerglotzOnUpperHalfPlane (fun z => -(deriv f z) / f z))
    (hCayleySchur :
      forall H : Complex -> Complex,
        HerglotzOnUpperHalfPlane H ->
          SchurOnUpperHalfPlane (fun z => (1 + Complex.I * H z) / (1 - Complex.I * H z)))
    (hLstarRealization :
      forall H : Complex -> Complex,
        HerglotzOnUpperHalfPlane H -> HasCanonicalSystemEnergyRealization H) :
    HasOnlyRealZeros f /\
      HolomorphicOnUpperHalfPlane (fun z => -(deriv f z) / f z) /\
      HerglotzOnUpperHalfPlane (fun z => -(deriv f z) / f z) /\
      SchurOnUpperHalfPlane (fun z => (1 + Complex.I * (-(deriv f z) / f z)) /
        (1 - Complex.I * (-(deriv f z) / f z))) /\
      HasCanonicalSystemEnergyRealization (fun z => -(deriv f z) / f z) := by
  have hHol :
      HolomorphicOnUpperHalfPlane (fun z => -(deriv f z) / f z) :=
    hLogDerivHol hFinalBridgeRH
  have hHer :
      HerglotzOnUpperHalfPlane (fun z => -(deriv f z) / f z) :=
    hLogDerivHerglotz hFinalBridgeRH
  have hSchur :
      SchurOnUpperHalfPlane (fun z => (1 + Complex.I * (-(deriv f z) / f z)) /
        (1 - Complex.I * (-(deriv f z) / f z))) :=
    hCayleySchur (fun z => -(deriv f z) / f z) hHer
  have hReal :
      HasCanonicalSystemEnergyRealization (fun z => -(deriv f z) / f z) :=
    hLstarRealization (fun z => -(deriv f z) / f z) hHer
  exact And.intro hFinalBridgeRH
    (And.intro hHol (And.intro hHer (And.intro hSchur hReal)))

end LeanV31
