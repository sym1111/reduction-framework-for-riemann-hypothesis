# Reduction Framework for the Riemann Hypothesis

Public repository for ongoing manuscript and Lean formalization updates.
This project is maintained as a versioned release workflow (v3.1, v3.2, ...),
with reproducible `lake build` snapshots and Zenodo DOI tracking.

## Current Scope

- Manuscript source and PDF:
  - `A_Reduction_Framework_RH_v3.1.tex`
  - `A_Reduction_Framework_RH_v3.1.pdf`
- Lean formalization snapshot:
  - `audit/formalization/lean_v3_1/`
- Mapping/status note:
  - `audit/v3.1_chain_mapping_status.md`

## Reproducible Build

From `audit/formalization/lean_v3_1`:

```powershell
lake build
```

Toolchain:
- Lean: `leanprover/lean4:v4.27.0`
- mathlib: `v4.27.0`

## DOI

- Concept DOI (latest tracking): `10.5281/zenodo.18617447`
- Version DOI (v3.1 snapshot): `10.5281/zenodo.18617448`

Use the concept DOI for project-level references and the version DOI for
fixed-snapshot citations.

## Public Copy/Paste Text

### Preprint Description (short)

This preprint and its Lean formalization are under active refinement. We
maintain reproducible `lake build` snapshots, explicit theorem-to-code mapping,
and versioned DOI releases.

### Release Notes (short)

Public release snapshot of the Reduction Framework for the Riemann Hypothesis.
The repository includes manuscript sources, Lean formalization code, and
mapping/status audit notes for ongoing formalization upgrades.

### Progress Disclaimer (recommended)

The repository documents current formalization status transparently. Some
paper-route steps are currently represented in Lean as explicit external axioms
or bridge-parameter wrappers and are being upgraded incrementally.

## Update Checklist (v3.2+)

1. Run `lake build` and keep build status green.
2. Update `audit/v3.1_chain_mapping_status.md` (or next-version mapping file).
3. Publish GitHub release tag.
4. Confirm Zenodo DOI registration for the new release.
5. Update README DOI/version lines if needed.
