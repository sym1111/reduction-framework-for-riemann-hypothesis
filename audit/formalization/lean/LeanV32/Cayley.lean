import Mathlib

namespace LeanV32

noncomputable section

/-!
Paper v3.2: locked Cayley maps (value / spectral coordinates).

TeX label: `eq:R2_cayley_locked` (and `eq:R2_csp_locked` for the spectral Cayley map).
-/

def C_val (m : Complex) : Complex :=
  (m - Complex.I) / (m + Complex.I)

def C_val_inv (w : Complex) : Complex :=
  Complex.I * (1 + w) / (1 - w)

def C_sp (lam : Complex) : Complex :=
  Complex.I * (1 + lam) / (1 - lam)

def C_sp_inv (zeta : Complex) : Complex :=
  (zeta - Complex.I) / (zeta + Complex.I)

/-!
Basic algebra of the Cayley maps.

These lemmas keep *all* division steps explicit via `field_simp` so later modules
can audit which denominators are required to be nonzero.
-/

lemma C_val_inv_C_val (m : Complex) (hm : m ≠ -Complex.I) :
    C_val_inv (C_val m) = m := by
  have hden : m + Complex.I ≠ 0 := by
    intro h
    apply hm
    exact eq_neg_of_add_eq_zero_left h
  unfold C_val_inv C_val
  field_simp [hden]
  ring_nf

lemma C_val_C_val_inv (w : Complex) (hw : w ≠ 1) :
    C_val (C_val_inv w) = w := by
  have hden : (1 - w) ≠ (0 : Complex) := by
    intro h
    apply hw
    have : (1 : Complex) = w := sub_eq_zero.mp h
    simpa using this.symm
  unfold C_val C_val_inv
  field_simp [hden]
  ring_nf

lemma C_sp_inv_C_sp (lam : Complex) (hlam : lam ≠ 1) :
    C_sp_inv (C_sp lam) = lam := by
  simpa [C_sp_inv, C_sp, C_val, C_val_inv] using (C_val_C_val_inv (w := lam) hlam)

lemma C_sp_C_sp_inv (zeta : Complex) (hzeta : zeta ≠ -Complex.I) :
    C_sp (C_sp_inv zeta) = zeta := by
  simpa [C_sp_inv, C_sp, C_val, C_val_inv] using (C_val_inv_C_val (m := zeta) hzeta)

lemma normSq_C_val_lt_one_of_im_pos (m : Complex) (hm : 0 < m.im) :
    Complex.normSq (C_val m) < 1 := by
  have hden_ne : m + Complex.I ≠ 0 := by
    intro h
    have hm_eq : m = -Complex.I := eq_neg_of_add_eq_zero_left h
    have him : m.im = -1 := by simp [hm_eq]
    have : (0 : Real) < (-1 : Real) := by simpa [him] using hm
    linarith
  have hden_pos : 0 < Complex.normSq (m + Complex.I) :=
    (Complex.normSq_pos).2 hden_ne

  have hnum_lt : Complex.normSq (m - Complex.I) < Complex.normSq (m + Complex.I) := by
    cases m with
    | mk x y =>
      have hy : 0 < y := by simpa using hm
      simp [Complex.normSq]
      nlinarith

  have hratio : Complex.normSq (m - Complex.I) / Complex.normSq (m + Complex.I) < 1 :=
    (div_lt_one₀ hden_pos).2 hnum_lt
  simpa [C_val, Complex.normSq_div] using hratio

lemma norm_C_val_lt_one_of_im_pos (m : Complex) (hm : 0 < m.im) :
    ‖C_val m‖ < 1 := by
  have hnormSq : Complex.normSq (C_val m) < 1 :=
    normSq_C_val_lt_one_of_im_pos (m := m) hm
  have hpow : ‖C_val m‖ ^ 2 < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hnormSq
  exact (sq_lt_one_iff₀ (norm_nonneg (C_val m))).1 hpow

lemma im_C_val_inv_pos_of_norm_lt_one (w : Complex) (hw : ‖w‖ < 1) :
    0 < (C_val_inv w).im := by
  have hw2 : ‖w‖ ^ 2 < (1 : Real) ^ 2 := by
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    nlinarith [hw, hw0]
  have hnormSq_w : Complex.normSq w < 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hw2
  have hnum_pos : 0 < 1 - Complex.normSq w := by
    linarith

  have hw_ne_one : w ≠ 1 := by
    intro h
    have hn : ‖w‖ = 1 := by simp [h]
    exact (ne_of_lt hw) hn
  have hden_ne : (1 - w) ≠ (0 : Complex) :=
    sub_ne_zero.2 ((ne_comm).1 hw_ne_one)
  have hden_pos : 0 < Complex.normSq (1 - w) :=
    (Complex.normSq_pos).2 hden_ne

  have him_eq : (C_val_inv w).im = ((1 + w) / (1 - w)).re := by
    unfold C_val_inv
    simp [div_eq_mul_inv, mul_assoc, Complex.mul_im]
  have hre_eq :
      ((1 + w) / (1 - w)).re = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    simp [Complex.div_re, Complex.normSq]
    ring
  have : (C_val_inv w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    simp [him_eq, hre_eq]
  simpa [this] using (div_pos hnum_pos hden_pos)

end

end LeanV32
