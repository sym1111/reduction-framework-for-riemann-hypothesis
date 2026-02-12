import LeanV31.NoPoleNevanlinna

namespace LeanV31

def HasUpperHalfPlaneZero (f : Complex -> Complex) : Prop :=
  Exists fun z : Complex => 0 < z.im /\ f z = 0

theorem laurent_sign_contradiction_of_nevanlinna
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H) :
    HasUpperHalfPlaneZero f -> False := by
  intro hHasZero
  cases hHasZero with
  | intro z hz =>
      exact hNevanlinnaExclusion z hz.1 hz.2

/- S021 wrapper:
if H = -f'/f is Herglotz on C_+, then f has no zeros in C_+.
The pole-contradiction argument is provided as an explicit bridge hypothesis. -/
theorem no_zeros_from_herglotz
    {f H : Complex -> Complex}
    (hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H) :
    ZeroFreeOnUpper f := by
  intro z hzIm hzZero
  have hLaurentSign : HasUpperHalfPlaneZero f -> False :=
    laurent_sign_contradiction_of_nevanlinna hNevanlinnaExclusion
  by_contra hContra
  have hHasZero : HasUpperHalfPlaneZero f :=
    Exists.intro z (And.intro hzIm hzZero)
  exact hContra (hLaurentSign hHasZero)

theorem no_zeros_from_herglotz_via_detector
    {f H : Complex -> Complex}
    (hCertificate : CircleHardyZeroFreeCertificate f H) :
    ZeroFreeOnUpper f := by
  have hNoPole : StripPoleExclusionViaNevanlinna f H :=
    no_pole_nevanlinna hCertificate
  exact hNoPole

end LeanV31
