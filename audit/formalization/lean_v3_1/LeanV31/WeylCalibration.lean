import LeanV31.LocalDerivativeAnchorTail

namespace LeanV31

open Set

def IsHerglotzOn (s : Set Complex) (m : Complex -> Complex) : Prop :=
  forall z, s z -> 0 <= Complex.im (m z)

/- Placeholder predicate kept abstract in this wrapper layer.
   The concrete HB criterion is supplied via hypotheses. -/
def IsHermiteBiehler (E : Complex -> Complex) : Prop :=
  forall z : Complex, 0 < Complex.im z ->
    ‖star (E (star z))‖ < ‖E z‖

/- Placeholder for "real zeros interlace" packaging.
   The concrete analytic statement is attached as a hypothesis. -/
def RealInterlacingData (A B : Complex -> Complex) : Prop :=
  forall x : Real, (A x = 0 -> B x != 0) /\ (B x = 0 -> A x != 0)

theorem herglotz_transfer_of_eqOn
    {s : Set Complex} {m1 m2 : Complex -> Complex}
    (heq : s.EqOn m1 m2)
    (h1 : IsHerglotzOn s m1) :
    IsHerglotzOn s m2 := by
  intro z hz
  have hzEq : m2 z = m1 z := by simpa using (heq hz).symm
  simpa [hzEq] using h1 z hz

/- S141 core wrapper:
`pick_kernel_equal` gives Weyl/arithmetic equality on `s`; then Herglotz
passes from Weyl to arithmetic by equality transfer. -/
theorem weyl_calibration_core
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : Set.Subset u s) (hu_nonempty : Set.Nonempty u)
    {mWeyl mArith : Complex -> Complex}
    (hmWeyl : DifferentiableOn Complex mWeyl s)
    (hmArith : DifferentiableOn Complex mArith s)
    (hderiv_u : u.EqOn (deriv mWeyl) (deriv mArith))
    {z0 : Complex} (hz0u : u z0) (h0 : mWeyl z0 = mArith z0)
    (hWeylHerglotz : IsHerglotzOn s mWeyl) :
    s.EqOn mWeyl mArith /\ IsHerglotzOn s mArith := by
  have hEq : s.EqOn mWeyl mArith :=
    (pick_kernel_equal hs hconn hu hu_sub hu_nonempty hmWeyl hmArith hderiv_u hz0u h0).1
  exact And.intro hEq (herglotz_transfer_of_eqOn hEq hWeylHerglotz)

/- Full theorem wrapper for S141:
external bridges (Herglotz -> HB and HB -> interlacing) are parameters. -/
theorem weyl_calibration_with_hb
    {s u : Set Complex}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hu : IsOpen u) (hu_sub : Set.Subset u s) (hu_nonempty : Set.Nonempty u)
    {mWeyl mArith E A B : Complex -> Complex}
    (hmWeyl : DifferentiableOn Complex mWeyl s)
    (hmArith : DifferentiableOn Complex mArith s)
    (hderiv_u : u.EqOn (deriv mWeyl) (deriv mArith))
    {z0 : Complex} (hz0u : u z0) (h0 : mWeyl z0 = mArith z0)
    (hWeylHerglotz : IsHerglotzOn s mWeyl)
    (hArithToHB : IsHerglotzOn s mArith -> IsHermiteBiehler E)
    (hHBToInterlace : IsHermiteBiehler E -> RealInterlacingData A B) :
    s.EqOn mWeyl mArith /\ IsHerglotzOn s mArith /\
      IsHermiteBiehler E /\ RealInterlacingData A B := by
  rcases
      weyl_calibration_core hs hconn hu hu_sub hu_nonempty
        hmWeyl hmArith hderiv_u hz0u h0 hWeylHerglotz
    with ⟨hEq, hArith⟩
  have hHB : IsHermiteBiehler E := hArithToHB hArith
  have hInt : RealInterlacingData A B := hHBToInterlace hHB
  exact And.intro hEq (And.intro hArith (And.intro hHB hInt))

end LeanV31
