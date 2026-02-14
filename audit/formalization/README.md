# Full Formalization (v3.1)

This folder tracks full-paper formalization progress for
`paper/v3.1/A_Reduction_Framework_RH.tex`.

## Goal

Move from partial helper checks to statement-level formalization coverage:

- target scope: every theorem/lemma/proposition/corollary in `v3.1`
- proof engines: Lean and/or Coq
- gate condition: each statement marked `formalized` with concrete artifact

## Files

- `init_v3_1_statement_inventory.ps1`
  - builds statement-level inventory from `audit/v3.1_statement_map.csv`
- `summarize_v3_1_statement_inventory.ps1`
  - generates compact coverage report
- `run_mathlib_formal_checks.ps1`
  - runs `lake build` in `audit/formalization/lean_v3_1`
- `log_formal_step.ps1`
  - appends one-step progress logs to:
    - `audit/formalization/step_logs/LATEST.md`
    - `audit/formalization/step_logs/INDEX.md`
    - `audit/formalization/step_logs/step_history.csv`
- `v3.1_statement_formalization_inventory.csv`
  - per-statement status tracker
- `v3.1_support_formal_artifacts.csv`
  - currently compiled support proofs not yet mapped as full statement proofs
- `v3.1_full_formalization_summary.md`
  - latest summary snapshot

## Status vocabulary

- `unstarted`: no formal artifact linked
- `in_progress`: artifact started, not complete
- `formalized`: statement-level formal proof completed
- `blocked`: blocked by missing definitions/libs or unresolved dependencies

## Practical workflow

1. refresh statement inventory:
   - `powershell -ExecutionPolicy Bypass -File audit/formalization/init_v3_1_statement_inventory.ps1`
2. edit statuses/artifacts in:
   - `audit/formalization/v3.1_statement_formalization_inventory.csv`
3. regenerate summary:
   - `powershell -ExecutionPolicy Bypass -File audit/formalization/summarize_v3_1_statement_inventory.ps1`
4. run base checker:
   - `powershell -ExecutionPolicy Bypass -File audit/run_formal_checks.ps1 -TexFile paper/v3.1/A_Reduction_Framework_RH.tex -ReportPrefix v3.1`
5. run full gate (mathlib + base):
   - `powershell -ExecutionPolicy Bypass -File audit/run_full_paper_formal_gate.ps1 -TexFile paper/v3.1/A_Reduction_Framework_RH.tex -ReportPrefix v3.1`
6. log each completed statement step:
   - `powershell -ExecutionPolicy Bypass -File audit/formalization/log_formal_step.ps1 -StatementId S145 -Action "formalize core" -Status formalized -Artifact "audit/formalization/lean_v3_1/LeanV31/SchurLocalUpdates.lean" -Formula "alpha_{k+1}=S_k'(0)/(1-conj(alpha_k)alpha_k)" -Remaining "S146" -Benefit "coverage +1"`

## Notes

- Existing `formal_checks/*.lean` and `formal_checks/*.v` are currently
  support-level checks. They compile, but do not yet certify full statement
  coverage of all `v3.1` labels.
