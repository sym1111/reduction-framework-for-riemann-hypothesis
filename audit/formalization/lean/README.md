# Lean formalization (v3.2 / LeanV32)

This is the Lake project for the v3.2 Lean track.

For an auditable summary of what is proved vs what remains as an explicit hypothesis, see:

- `PROOF_STATUS.md`

## Build (strict)

From this folder:
- `lake --wfail build`

This builds `LeanV32.BuildAll` by default (full v3.2 chain + golden witness imports).

## Entry points

- `LeanV32` — main v3.2 library (paper-aligned modules)
- `LeanV32.BuildAll` — convenience target that additionally imports the golden witness/docking modules
