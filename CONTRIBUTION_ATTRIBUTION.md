# Contribution and Attribution Policy (Public Release)

This repository is a public release bundle for RH v3.1.

## 1. Scope of this public repository

This repository publishes:
- Manuscript source and PDF for v3.1.
- Lean formalization sources under `audit/formalization/lean_v3_1/`.
- Selected audit summaries for dependency and consistency tracking.

This repository does not publish private process logs, internal meta-workflow notes, or legacy archive branches.

## 2. Commit identity

Author signature used for commits in this project:
- Name: `Youngmin Shin`
- Email: `tlsdudals1994@gmail.com`

## 3. What is claimed as contribution here

Claimed contribution in this repository includes:
- The reduction architecture and manuscript organization for RH v3.1.
- The formalization workflow and machine-checkable Lean code in this public bundle.
- The reproducible build setup (`lean-toolchain`, `lakefile.toml`, CI workflow).

## 4. What is NOT claimed as original discovery

This repository does not claim original discovery for:
- Classical theorems and standard results cited from prior literature.
- Lean `mathlib` results and foundational theorems from the proof assistant ecosystem.
- External papers used as dependencies in the manuscript.

## 5. Attribution rule

For each external theorem/result used:
- Keep explicit citation in the manuscript (`A_Reduction_Framework_RH_v3.1.tex`).
- Keep dependency context in the audit summaries when relevant.
- Do not present prior known results as first proved in this repository.

## 6. Public wording template

Suggested wording for release notes and metadata:

"This repository contains the RH v3.1 manuscript and a Lean formalization snapshot with explicit attribution to prior literature and library dependencies."

## 7. Scope boundary

- Commit authorship identifies who recorded changes.
- Scholarly novelty is evaluated by distinction between new construction and cited prior work.
- These two should be kept separate in public descriptions and reviews.
