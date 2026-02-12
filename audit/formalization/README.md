# Full Formalization (v3.1) - Public Bundle

This folder is the public-facing formalization snapshot for
`A_Reduction_Framework_RH_v3.1.tex`.

## Included in this public bundle

- `audit/formalization/lean_v3_1/`
  - Lean source files (`LeanV31/*.lean`)
  - toolchain/build config (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`)
  - CI workflow (`.github/workflows/lean_action_ci.yml`)
  - build certificate log (`BUILD_CERT_2026-02-12.log`)
- `audit/formalization/v3.1_full_formalization_summary.md`

## Reproducible build

From `audit/formalization/lean_v3_1`:

```powershell
lake build
```

## Notes on scope

This public repository is a sanitized release snapshot.
Internal helper scripts and private process logs used during development are intentionally excluded.
