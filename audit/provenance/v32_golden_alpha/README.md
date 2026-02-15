# v3.2 Golden α provenance (LeanV32)

This folder pins down the **exact** 160-parameter golden Schur sequence used by the Lean v3.2 track,
and provides a bitwise audit check that the committed `.npy` artifact matches the Lean literal in
`LeanV32/GoldenAlphaWitness.lean`.

## What is included
- `alphas_golden_R0_scaled_r0.9_M2048_K160_pad1024_theta13.9804951740.npy` (complex128, length 160)
- `verify_golden_alpha_npy_matches_lean.py` (bitwise verifier)
- `golden_alpha_match_report.json` (verifier output; includes SHA256)
- `build_report_golden_R0_scaled_r0.9_M2048_K160_pad1024_theta13.9804951740.json` (golden build metadata)
- `verify_r2_internal_schur_nsamp4096_seed0.txt` (golden verification log)
- `meta_t0_109.099073_eta_0.12_r_0.9_M_2048_N_80_dps_80.json` (source Svals meta)

## Reproduce (from repo root)
1. Verify the `.npy` payload matches the Lean literal (bitwise IEEE-754):
   - `python audit/provenance/v32_golden_alpha/verify_golden_alpha_npy_matches_lean.py --json-out audit/provenance/v32_golden_alpha/golden_alpha_match_report.json`
2. Build the Lean v3.2 chain + golden witness (strict):
   - `cd audit/formalization/lean_v3_1`
   - `lake --wfail build LeanV32.BuildAll`

## Expected SHA256
- `.npy`: `f066d9e5368f59d8f60937c384b51a6754c51d61a9169734bd72ca838eb83792`
- `GoldenAlphaWitness.lean`: `e50a8310005bb35deb71fbef38a35e2a3e5780b3341783cea70a9a2d7085bf6d`

