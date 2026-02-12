# Contribution and Attribution Policy

Author signature for repository commits:
- Name: `Youngmin Shin`
- Email: `tlsdudals1994@gmail.com`

요약(한국어):
- 이 저장소의 커밋 작성자는 `Youngmin Shin`으로 고정한다.
- 본 저장소는 "내가 새로 구성/정식화한 부분"과 "외부 기존 정리"를 구분해 표기한다.
- 외부 기존 정리는 반드시 인용하고, 최초 발견처럼 주장하지 않는다.

## 1. What is claimed as this project's contribution

The project claims contribution for:
- The reduction architecture and manuscript organization in this repository.
- The formalization workflow, scripts, and audit process.
- The machine-checked formalization units explicitly marked as `formalized` in
  `audit/formalization/v3.1_statement_formalization_inventory.csv`.

Current core formalization contributions include:
- `S138`, `S139`, `S140`, `S141`, `S142`, `S143`, `S145`, `S146`.

## 2. What is NOT claimed as original discovery

The project does **not** claim original discovery for:
- Pre-existing theorems and classical results used as tools.
- Lean `mathlib` library theorems and Coq/Lean ecosystem foundations.
- External papers and known equivalences cited in the manuscript.

## 3. Attribution rule

For every external theorem/result:
- Keep explicit citation in manuscript (`.tex` references).
- Mark it as an external dependency when relevant in audit files.
- Do not rephrase external known results as if they were first proved here.

## 4. Safe public wording template

Recommended wording for README/release notes:
- "This repository contains my formalization workflow and verified wrappers for
  selected statements in the RH reduction manuscript. Classical results and
  library theorems are used with attribution and are not claimed as original
  discoveries by this repository."

## 5. Scope boundary (practical)

- `Commit author` proves who recorded code changes.
- `Scholarly novelty` depends on what is genuinely new versus cited prior work.
- Always separate these two concepts in public descriptions.
