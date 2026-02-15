import LeanV32.GoldenAlphaWitness
import LeanV32.RHClosure

namespace LeanV32

noncomputable section

/-!
Docking layer (v3.2 Lean track):

`GoldenAlphaWitness` provides the exported 160-parameter Schur sequence `goldenAlphaSeq`
as an exact-rational Lean literal (padded by zeros for `k ≥ 160`), together with a
kernel-checked `AlphaRadiusBound`.

This file *names* that sequence as the paper's official `XiModel`-alpha sequence and
packages the minimal logical interface needed to run the closure endpoint in `RHClosure`.

Important: the only non-algebraic input that is **not** proven in LeanV32 is the
identification of the xi-model log-derivative with the cocycle Herglotz approximant.
We keep that as an explicit hypothesis `XiGoldenIdentification`.
-/

/-- The paper's official `XiModel` alpha-sequence (v3.2): the exported golden parameters. -/
def XiAlphaSeq : Nat → Complex :=
  goldenAlphaSeq

/-- Depth used for the exported golden certificate (length `160`). -/
def XiGoldenDepth : Nat :=
  160

/-- The cocycle Herglotz approximant at depth `XiGoldenDepth`. -/
def XiHGolden (z : Complex) : Complex :=
  mkn XiAlphaSeq z 0 XiGoldenDepth

/-- Identification hypothesis: the xi-model log-derivative matches `XiHGolden` on `Im(z)>0`. -/
def XiGoldenIdentification : Prop :=
  ∀ z : Complex, 0 < z.im → XiModelLogDerivative z = XiHGolden z

theorem XiAlphaRadiusBound : AlphaRadiusBound XiAlphaSeq := by
  simpa [XiAlphaSeq] using goldenAlphaRadiusBound

theorem XiHGolden_im_pos (z : Complex) (hz : 0 < z.im) : 0 < (XiHGolden z).im := by
  have hα : ∀ k : Nat, ‖XiAlphaSeq k‖ < 1 :=
    alphaRadiusBound_norm_lt_one (alphaSeq := XiAlphaSeq) XiAlphaRadiusBound
  have hpos : 0 < (mkn XiAlphaSeq z 0 XiGoldenDepth).im :=
    mkn_im_pos (alphaSeq := XiAlphaSeq) (z := z) (hz := hz) hα 0 XiGoldenDepth
  simpa [XiHGolden] using hpos

theorem xiModel_zeroFree_of_XiGoldenIdentification
    (hID : XiGoldenIdentification) : ZeroFreeOnUpper XiModel := by
  intro z hz hzero
  have hImPos : 0 < (XiModelLogDerivative z).im := by
    have hpos : 0 < (XiHGolden z).im := XiHGolden_im_pos (z := z) hz
    simpa [hID z hz] using hpos
  have hImZero : (XiModelLogDerivative z).im = 0 := by
    simp [XiModelLogDerivative, hzero]
  exact (ne_of_gt hImPos) hImZero

theorem mathlib_rh_of_XiGoldenIdentification
    (hID : XiGoldenIdentification) : MathlibRiemannHypothesis := by
  have hZeroFree : ZeroFreeOnUpper XiModel :=
    xiModel_zeroFree_of_XiGoldenIdentification (hID := hID)
  exact mathlib_rh_of_xi_model_zero_free hZeroFree

end

end LeanV32

