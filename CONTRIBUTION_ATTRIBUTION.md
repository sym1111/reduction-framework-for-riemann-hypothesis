# Contribution and Attribution Policy

Author signature for repository commits:
- Name: `Youngmin Shin`
- Email: `tlsdudals1994@gmail.com`

## Scope

This repository is a **public provenance record** for the v3.2 manuscript snapshot and its supporting audit artifacts
(including the Lean v3.2 / `LeanV32` build and the pinned golden α provenance bundle).

## What is claimed as this repository's contribution

The project claims contribution for:
- The reduction architecture and manuscript organization recorded here.
- The audit/provenance workflow and the reproducible artifacts committed in this repository.
- The Lean v3.2 formalization units under `audit/formalization/lean/LeanV32`.

## What is NOT claimed as original discovery

The project does **not** claim original discovery for:
- Classical results used as tools (kept with explicit citations in the manuscript).
- Theorems and infrastructure provided by Lean `mathlib` and the Lean/Coq ecosystem.

## Attribution rule

For every external theorem/result:
- Keep explicit citation in the manuscript (`.tex` references).
- Do not rephrase external results as if they were first proved here.

## Safe public wording template

Recommended wording for README/release notes:
- "This repository contains my manuscript snapshot, audit/provenance artifacts, and Lean-checked modules for the v3.2 track.
  Classical results and library theorems are used with attribution and are not claimed as original discoveries by this repository."
