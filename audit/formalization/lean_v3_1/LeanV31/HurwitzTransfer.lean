import Mathlib

namespace LeanV31

open Set

def NoZerosOn (f : Complex -> Complex) (S : Set Complex) : Prop :=
  forall z, S z -> Not (f z = 0)

/- Placeholder packaging for "same number of zeros in R (with multiplicity)". -/
def SameZeroCountIn (f g : Complex -> Complex) (R : Set Complex) : Prop :=
  forall z : Complex, R z -> (f z = 0 <-> g z = 0)

/- S143 wrapper:
boundary non-vanishing plus a strict boundary perturbation bound yields boundary
non-vanishing for the perturbed function; combined with a Rouché-style bridge,
this gives zero-count transfer in `R`. -/
theorem hurwitz_rect_transfer
    {Xi : Complex -> Complex}
    {XiFamily : Real -> Complex -> Complex}
    {R boundary : Set Complex}
    (hUniformBoundary :
      Exists fun alphaR : Real =>
        0 < alphaR /\
          forall alpha : Real, 0 < alpha -> alpha < alphaR ->
            forall z, boundary z ->
              ‖XiFamily alpha z - Xi z‖ < ‖Xi z‖)
    (hRoucheBridge :
      forall alpha : Real, NoZerosOn (XiFamily alpha) boundary ->
        SameZeroCountIn (XiFamily alpha) Xi R) :
    Exists fun alphaR : Real =>
      0 < alphaR /\
        forall alpha : Real, 0 < alpha -> alpha < alphaR ->
          NoZerosOn (XiFamily alpha) boundary /\
            SameZeroCountIn (XiFamily alpha) Xi R := by
  rcases hUniformBoundary with ⟨alphaR, hAlphaRPos, hBound⟩
  refine ⟨alphaR, hAlphaRPos, ?_⟩
  intro alpha hAlphaPos hAlphaLt
  have hNoZeros : NoZerosOn (XiFamily alpha) boundary := by
    intro z hz
    have hlt : ‖XiFamily alpha z - Xi z‖ < ‖Xi z‖ :=
      hBound alpha hAlphaPos hAlphaLt z hz
    intro hZero
    have hEq : ‖XiFamily alpha z - Xi z‖ = ‖Xi z‖ := by
      simp [hZero]
    have hltSelf : ‖Xi z‖ < ‖Xi z‖ := by
      rw [hEq] at hlt
      exact hlt
    exact (lt_irrefl ‖Xi z‖) hltSelf
  exact And.intro hNoZeros (hRoucheBridge alpha hNoZeros)

end LeanV31
