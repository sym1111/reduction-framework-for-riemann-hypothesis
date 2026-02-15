# Public repo storage policy (do not mix raw/local artifacts)

This repository is an **external/public release tree**. Keep it minimal and reproducible.

## What goes where

- `paper/v3.2/`
  - Release-ready TeX/PDF only.
  - Prefer the split entrypoints:
    - `A_Reduction_Framework_RH_core.tex` / `A_Reduction_Framework_RH_core.pdf`
    - `A_Reduction_Framework_RH_supp.tex` / `A_Reduction_Framework_RH_supp.pdf`
- `audit/formalization/lean/`
  - The Lake project for the Lean v3.2 track (`LeanV32`).
  - Default target is strict: `lake --wfail build`.
- `audit/provenance/v32_golden_alpha/`
  - Pinned golden artifacts (`.npy`) + verifier script + JSON report with SHA256.

## What must NOT be committed here

- Local scratch folders (e.g. `수학/`, desktop dumps, temp scripts).
- Ad-hoc exports or large raw datasets that are not part of a pinned provenance bundle.
- Build directories and intermediate artifacts (`.lake/`, `*.olean`, `*.aux`, `*.log`, etc.).

## If you need to add new raw artifacts

Do it in the **private** workspace first, then promote only the minimal, audit-grade subset to the public repo under:

- `audit/provenance/<tag>/` (include: artifact + verifier + report + short README)

Keep paths stable and avoid scattering files across unrelated directories.
