# Proof status (Lean v3.2 / LeanV32)

This folder contains the Lake project for the **v3.2 Lean track** (`LeanV32`).

## Build (strict)

From `audit/formalization/lean/`:

- `lake --wfail build`

The public release also pins a build transcript in `BUILD_CERT_*.log`.

## What is fully kernel-checked in LeanV32

The following parts are **proved in Lean** (no `sorry`/`admit`):

- Disk/cocycle algebra (R1-side): strict disk invariance, denominator non-vanishing controls, and the Herglotz-side truncation
  `mkn alphaSeq z k n` with `Im(mkn ...) > 0` on `Im(z)>0` given `‖alphaSeq k‖ < 1`.
- Golden alpha witness:
  - `LeanV32/GoldenAlphaWitness.lean` defines the 160-term `goldenAlphaVec : Vector Complex 160` as exact rationals,
    defines `goldenAlphaSeq : Nat → Complex` (zero-padded for `k ≥ 160`), and proves `goldenAlphaRadiusBound`.
- RH closure bridge:
  - `LeanV32/RHClosure.lean` shows `ZeroFreeOnUpper XiModel → MathlibRiemannHypothesis` where
    `XiModel(z) = xi(1/2 + i z)` is defined in `LeanV32/XiModelPaper.lean` using Mathlib’s `completedRiemannZeta`.

## The only remaining non-checked input (as of v3.2)

To reach **Mathlib’s RH statement** without any hypotheses, Lean still needs a proof of the following *identification*:

- `LeanV32/XiGoldenDocking.lean`:
  - `XiAlphaSeq := goldenAlphaSeq`
  - `XiHGolden(z) := mkn XiAlphaSeq z 0 160`
  - `XiGoldenIdentification : Prop := ∀ z, 0 < z.im → XiModelLogDerivative z = XiHGolden z`

All downstream endpoints are already proved:

- `XiGoldenIdentification → ZeroFreeOnUpper XiModel → MathlibRiemannHypothesis`.

So the proof state is:

> **LeanV32 closes the full v3.2 chain conditional on `XiGoldenIdentification`.**

## Roadmap for closing `XiGoldenIdentification` (paper alignment)

In the manuscript this corresponds to the *calibration / identification* step (the “target identification” layer),
which is substantially more analytic than the R1-side cocycle algebra.

A Lean proof would require formalizing (at minimum) the objects and arguments behind:

1. canonical-system / Weyl-function construction and limit-point uniqueness,
2. circle–Hardy pole-exclusion rigidity,
3. calibration by a Möbius gauge (jet pinning) and the identity principle to upgrade a germ match to a global identity.

Until that layer is formalized, the public Lean track keeps the identification as an **explicit hypothesis**
to avoid hiding assumptions.

