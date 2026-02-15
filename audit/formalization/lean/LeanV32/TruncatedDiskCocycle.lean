import Mathlib
import LeanV32.CanonicalStepDiskMap
import LeanV32.DiskMapInvariance
import LeanV32.OverlapDenomBound

namespace LeanV32

noncomputable section

/-!
Paper v3.2: truncated disk cocycle iterates `w_{k,n}(z)`.

TeX context:
- `w_{k,n}(z) := F_k^{val}(w_{k+1,n}(z); z)`
- hence `w_{k,n}(z) = (F_k^{val} ∘ ... ∘ F_{n-1}^{val})(0)`.

This file defines the iterates, proves the disk bound `‖w_{k,n}(z)‖ ≤ 1`, and then
packages the denominator-separation property (`DenomSepAt`) for these iterates.
-/

-- The induced one-step disk map (total function; denominator control is handled separately).
def Fval (alpha z w : Complex) : Complex :=
  mobius (diskMat alpha z) w

-- Truncated iterate: apply `F_k, ..., F_{n-1}` to `0` (foldr matches the TeX composition order).
def wkn (alphaSeq : Nat → Complex) (z : Complex) (k n : Nat) : Complex :=
  (((List.range (n - k)).map (fun t => k + t)).foldr (fun i acc => Fval (alphaSeq i) z acc) 0)

lemma wkn_self (alphaSeq : Nat → Complex) (z : Complex) (n : Nat) :
    wkn alphaSeq z n n = 0 := by
  simp [wkn]

lemma wkn_norm_le_one_of_step
    (alphaSeq : Nat → Complex) (z : Complex)
    (hstep : ∀ i : Nat, ∀ w : Complex, ‖w‖ ≤ 1 → ‖Fval (alphaSeq i) z w‖ ≤ 1) :
    ∀ k n : Nat, ‖wkn alphaSeq z k n‖ ≤ 1 := by
  classical
  have hfold :
      ∀ l : List Nat, ∀ acc : Complex,
        ‖acc‖ ≤ 1 →
          ‖l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc‖ ≤ 1 := by
    intro l
    induction l with
    | nil =>
        intro acc hacc
        simpa
    | cons i l ih =>
        intro acc hacc
        have hacc' : ‖l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc‖ ≤ 1 :=
          ih acc hacc
        simpa [List.foldr] using (hstep i (l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc) hacc')

  intro k n
  have h0 : ‖(0 : Complex)‖ ≤ 1 := by simp
  simpa [wkn] using hfold (((List.range (n - k)).map (fun t => k + t))) 0 h0

lemma wkn_norm_le_one
    (alphaSeq : Nat → Complex) (z : Complex)
    (hz : 0 < z.im) (hα : ∀ k : Nat, ‖alphaSeq k‖ < 1) :
    ∀ k n : Nat, ‖wkn alphaSeq z k n‖ ≤ 1 := by
  refine wkn_norm_le_one_of_step (alphaSeq := alphaSeq) (z := z) ?_
  intro i w hw
  simpa [Fval] using diskMat_mobius_norm_le_one (alphaSeq i) z w hz (hα i) hw

lemma wkn_norm_lt_one_of_step
    (alphaSeq : Nat → Complex) (z : Complex)
    (hstep : ∀ i : Nat, ∀ w : Complex, ‖w‖ < 1 → ‖Fval (alphaSeq i) z w‖ < 1) :
    ∀ k n : Nat, ‖wkn alphaSeq z k n‖ < 1 := by
  classical
  have hfold :
      ∀ l : List Nat, ∀ acc : Complex,
        ‖acc‖ < 1 → ‖l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc‖ < 1 := by
    intro l
    induction l with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons i l ih =>
        intro acc hacc
        have hacc' :
            ‖l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc‖ < 1 :=
          ih acc hacc
        simpa [List.foldr] using
          (hstep i (l.foldr (fun i acc => Fval (alphaSeq i) z acc) acc) hacc')

  intro k n
  have h0 : ‖(0 : Complex)‖ < 1 := by simp
  simpa [wkn] using hfold (((List.range (n - k)).map (fun t => k + t))) 0 h0

lemma wkn_norm_lt_one
    (alphaSeq : Nat → Complex) (z : Complex)
    (hz : 0 < z.im) (hα : ∀ k : Nat, ‖alphaSeq k‖ < 1) :
    ∀ k n : Nat, ‖wkn alphaSeq z k n‖ < 1 := by
  refine wkn_norm_lt_one_of_step (alphaSeq := alphaSeq) (z := z) ?_
  intro i w hw
  simpa [Fval] using diskMat_mobius_norm_lt_one (alphaSeq i) z w hz (hα i) hw

-- Herglotz-side approximants obtained by inverse Cayley on the disk iterates.
def mkn (alphaSeq : Nat → Complex) (z : Complex) (k n : Nat) : Complex :=
  C_val_inv (wkn alphaSeq z k n)

lemma mkn_im_pos
    (alphaSeq : Nat → Complex) (z : Complex)
    (hz : 0 < z.im) (hα : ∀ k : Nat, ‖alphaSeq k‖ < 1) :
    ∀ k n : Nat, 0 < (mkn alphaSeq z k n).im := by
  intro k n
  unfold mkn
  exact im_C_val_inv_pos_of_norm_lt_one (w := wkn alphaSeq z k n)
    (wkn_norm_lt_one alphaSeq z hz hα k n)

-- Convenience alias: the paper's denominator separation property for the actual iterates.
def DenomSepCocycleAt (z : Complex) (alphaSeq : Nat → Complex) : Prop :=
  DenomSepAt z alphaSeq (fun k n => wkn alphaSeq z k n)

lemma denomExpr_ne_zero_of_denomSepCocycleAt
    (z : Complex) (alphaSeq : Nat → Complex)
    (h : DenomSepCocycleAt z alphaSeq) :
    ∀ n k : Nat, k < n → denomExpr (alphaSeq k) z (wkn alphaSeq z k n) ≠ 0 := by
  rcases h with ⟨δ, hδ_pos, hδ⟩
  intro n k hk
  have hδ_le : δ ≤ ‖denomExpr (alphaSeq k) z (wkn alphaSeq z k n)‖ :=
    hδ n k hk
  have hnorm_pos : 0 < ‖denomExpr (alphaSeq k) z (wkn alphaSeq z k n)‖ :=
    lt_of_lt_of_le hδ_pos hδ_le
  exact (norm_pos_iff).1 hnorm_pos

lemma den_ne_zero_of_denomSepCocycleAt
    (z : Complex) (alphaSeq : Nat → Complex)
    (h : DenomSepCocycleAt z alphaSeq) :
    ∀ n k : Nat, k < n → den (diskMat (alphaSeq k) z) (wkn alphaSeq z k n) ≠ 0 := by
  intro n k hk
  have hne : denomExpr (alphaSeq k) z (wkn alphaSeq z k n) ≠ 0 :=
    denomExpr_ne_zero_of_denomSepCocycleAt (z := z) (alphaSeq := alphaSeq) h n k hk
  simpa [denomExpr_eq] using hne

lemma denomSepCocycleAt_of_pole_exclusion
    (z : Complex) (alphaSeq : Nat → Complex) (ε : Real)
    (hz : 0 < z.im) (hα : ∀ k : Nat, ‖alphaSeq k‖ < 1) (hε : 0 < ε)
    (hp : ∀ k : Nat, 1 + ε ≤ ‖denomPole (alphaSeq k) z‖) :
    DenomSepCocycleAt z alphaSeq := by
  unfold DenomSepCocycleAt
  refine denomSepAt_of_pole_exclusion (z := z) (alphaSeq := alphaSeq)
    (wkn := fun k n => wkn alphaSeq z k n) (ε := ε) hz hα hε ?_ hp
  intro n k hk
  exact wkn_norm_le_one alphaSeq z hz hα k n

lemma denomSepCocycleAt_of_alpha_bound
    (z : Complex) (alphaSeq : Nat → Complex) (r0 : Real)
    (hz : 0 < z.im) (hr0_nonneg : 0 ≤ r0) (hr0 : r0 < 1)
    (hα : ∀ k : Nat, ‖alphaSeq k‖ ≤ r0) :
    DenomSepCocycleAt z alphaSeq := by
  rcases denomPole_norm_ge_one_add_eps_of_norm_le (z := z) hz r0 hr0_nonneg hr0 with ⟨ε, hε, hp⟩
  have hα' : ∀ k : Nat, ‖alphaSeq k‖ < 1 := by
    intro k
    exact lt_of_le_of_lt (hα k) hr0
  have hp' : ∀ k : Nat, 1 + ε ≤ ‖denomPole (alphaSeq k) z‖ := by
    intro k
    exact hp (alpha := alphaSeq k) (hα k)
  exact denomSepCocycleAt_of_pole_exclusion (z := z) (alphaSeq := alphaSeq) (ε := ε) hz hα' hε hp'

end

end LeanV32
