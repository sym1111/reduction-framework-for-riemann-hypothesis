import LeanV31.MobiusHerglotzB21

namespace LeanV31

def InUpperB21 (z : Complex) : Prop := 0 < Complex.im z

def PolarizedEnergyIdentityAt
    (zeta omega : Complex) (M R H : Complex -> Complex) : Prop :=
  M zeta + M omega = (H zeta + H omega) + (R zeta + R omega)

def PolarizedKernelPSDOnUpper
    (M R H : Complex -> Complex) : Prop :=
  forall (zeta omega : Complex),
    InUpperB21 zeta -> InUpperB21 omega ->
      0 <= Complex.re
        ((M zeta - H zeta - R zeta) * (M omega - H omega - R omega))

/- S025 wrapper:
polarized J-kernel identity plus positivity bridge yields PSD kernel on C_+. -/
theorem polarized_J_kernel
    {M R H : Complex -> Complex}
    (hFormula :
      forall (zeta omega : Complex),
        InUpperB21 zeta -> InUpperB21 omega ->
          PolarizedEnergyIdentityAt zeta omega M R H)
    (hPosBridge :
      (forall (zeta omega : Complex),
        InUpperB21 zeta -> InUpperB21 omega ->
          PolarizedEnergyIdentityAt zeta omega M R H) ->
        PolarizedKernelPSDOnUpper M R H) :
    (forall (zeta omega : Complex),
      InUpperB21 zeta -> InUpperB21 omega ->
        PolarizedEnergyIdentityAt zeta omega M R H) /\
      PolarizedKernelPSDOnUpper M R H := by
  have hPsd : PolarizedKernelPSDOnUpper M R H := hPosBridge hFormula
  exact And.intro hFormula hPsd

end LeanV31
