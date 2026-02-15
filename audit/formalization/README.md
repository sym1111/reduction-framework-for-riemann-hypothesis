# Formalization (v3.2 / LeanV32)

This folder contains the Lean formalization project for the **v3.2 track**.

## Location

- Lake project root: `audit/formalization/lean`
- Main library: `audit/formalization/lean/LeanV32`

## Build (strict)

From repository root:
- `cd audit/formalization/lean`
- `lake --wfail build`

`lakefile.toml` is configured so the default build target compiles the full v3.2 chain plus the golden witness
(via `LeanV32.BuildAll`).
