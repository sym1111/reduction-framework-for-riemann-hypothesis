import Mathlib
import LeanV32.Cayley

namespace LeanV32

noncomputable section

/-!
Paper v3.2: Herglotz/Schur predicates on the upper half-plane and the Cayley maps
connecting them.

We use the **strict** variants:
- Herglotz: `Im(H z) > 0` on `Im(z) > 0`
- Schur: `‖W z‖ < 1` on `Im(z) > 0`

This matches the algebraic Cayley lemmas in `LeanV32.Cayley`.
-/

def HolomorphicOnUpperHalfPlane (F : Complex → Complex) : Prop :=
  DifferentiableOn ℂ F {z : Complex | 0 < z.im}

def HerglotzOnUpperHalfPlane (H : Complex → Complex) : Prop :=
  HolomorphicOnUpperHalfPlane H ∧ ∀ z : Complex, 0 < z.im → 0 < (H z).im

def SchurOnUpperHalfPlane (W : Complex → Complex) : Prop :=
  HolomorphicOnUpperHalfPlane W ∧ ∀ z : Complex, 0 < z.im → ‖W z‖ < 1

theorem schur_of_herglotz
    {H : Complex → Complex}
    (hH : HerglotzOnUpperHalfPlane H) :
    SchurOnUpperHalfPlane (fun z => C_val (H z)) := by
  refine And.intro ?_ ?_
  · -- holomorphy: quotient of differentiable functions, away from the pole `H z = -i`.
    have hHol : DifferentiableOn ℂ H {z : Complex | 0 < z.im} := hH.1
    have hConstI : DifferentiableOn ℂ (fun _ : Complex => (Complex.I : Complex)) {z : Complex | 0 < z.im} :=
      differentiableOn_const (c := (Complex.I : Complex))
    have hNum : DifferentiableOn ℂ (fun z => H z - Complex.I) {z : Complex | 0 < z.im} :=
      hHol.sub hConstI
    have hDen : DifferentiableOn ℂ (fun z => H z + Complex.I) {z : Complex | 0 < z.im} :=
      hHol.add hConstI
    have hDen_ne : ∀ z : Complex, z ∈ {z : Complex | 0 < z.im} → H z + Complex.I ≠ 0 := by
      intro z hz hzero
      have hHz : H z = -Complex.I := eq_neg_of_add_eq_zero_left hzero
      have : (H z).im = -1 := by simp [hHz]
      have : (0 : Real) < -1 := by simpa [this] using hH.2 z hz
      linarith
    -- Assemble the quotient.
    simpa [C_val] using (hNum.div hDen hDen_ne)
  · intro z hz
    exact norm_C_val_lt_one_of_im_pos (m := H z) (hH.2 z hz)

theorem herglotz_of_schur
    {W : Complex → Complex}
    (hW : SchurOnUpperHalfPlane W) :
    HerglotzOnUpperHalfPlane (fun z => C_val_inv (W z)) := by
  refine And.intro ?_ ?_
  · -- holomorphy: quotient of differentiable functions; `‖W z‖ < 1` excludes `W z = 1`.
    have hHol : DifferentiableOn ℂ W {z : Complex | 0 < z.im} := hW.1
    have hConst1 : DifferentiableOn ℂ (fun _ : Complex => (1 : Complex)) {z : Complex | 0 < z.im} :=
      differentiableOn_const (c := (1 : Complex))
    have hConstI : DifferentiableOn ℂ (fun _ : Complex => (Complex.I : Complex)) {z : Complex | 0 < z.im} :=
      differentiableOn_const (c := (Complex.I : Complex))
    have hNum : DifferentiableOn ℂ (fun z => Complex.I * ((1 : Complex) + W z))
        {z : Complex | 0 < z.im} :=
      hConstI.mul (hConst1.add hHol)
    have hDen : DifferentiableOn ℂ (fun z => (1 : Complex) - W z) {z : Complex | 0 < z.im} :=
      hConst1.sub hHol
    have hDen_ne : ∀ z : Complex, z ∈ {z : Complex | 0 < z.im} → (1 : Complex) - W z ≠ 0 := by
      intro z hz hzero
      have hWz : W z = 1 := (sub_eq_zero.mp hzero).symm
      have hnorm : (‖W z‖ : Real) = 1 := by simp [hWz]
      exact (ne_of_lt (hW.2 z hz)) hnorm
    simpa [C_val_inv] using (hNum.div hDen hDen_ne)
  · intro z hz
    exact im_C_val_inv_pos_of_norm_lt_one (w := W z) (hW.2 z hz)

end

end LeanV32
