# External Mass Axis Matching Checklist (R1 Mainline)

Date: 2026-02-12
Scope: keep the **external mass-theorem axis** isolated from internal CS2
diagnostic routes, and track only the mainline matching status.

## 1) Mainline Route (Do Not Mix)

Paper labels (v3.1):

- `prop:R1_classical_mass` (`paper/v3.1/A_Reduction_Framework_RH.tex:4633`)
- `prop:R1_classical_mass_applicability` (`paper/v3.1/A_Reduction_Framework_RH.tex:4651`)
- `thm:R1-limit-point` (`paper/v3.1/A_Reduction_Framework_RH.tex:4672`)
- RH closure references:
  - `thm:final_bridge_closed` (`...:899`)
  - `thm:RH_from_anchor` (`...:6403`)

Lean mainline anchor:

- `audit/formalization/lean_v3_1/LeanV31/R1CitationStandardChain.lean:122`
  - `axiom paper_external_mass_divergence_limitpoint`

## 2) External Axis Validation Status

- [x] Single external axis identified (one `axiom` only in `LeanV31/*.lean`)
- [x] Standard-theorem source check completed
- [x] RH dependency meaning clarified (proof-dependency independence)
- [x] Evidence links pinned
- [x] External-axis retention rationale documented (why it remains for now)

Reference note:

- `audit/external_axiom_validation.md`

Retention policy summary:

- Keep this single external axis because it is RH-independent (proof-dependency
  meaning) and standard in canonical-system theory.
- Keep it as the only gate until concrete semantic internalization closes the
  hypothesis-matching layer.

## 3) Assumption Matching Matrix (Mainline)

External theorem side (canonical systems) -> Lean/paper side

- Hamiltonian regularity/positivity regime
  - Lean: `PaperR1ChainBlockPSDAt`, `PaperR1CanonicalStepModelAt`
  - Status: [x] theorem-shape matched
  - Note: deeper semantic internalization to concrete canonical-system objects is still pending

- Weyl-disk/radius model side
  - Lean: `PaperR1WeylDiskRadiusModelAt`
  - Status: [x] theorem-shape matched
  - Note: deeper semantic internalization to concrete Weyl-disk objects is still pending

- Spectral parameter in upper half-plane
  - Lean: `UpperHalfPlanePoint`
  - Status: [x] matched at interface level

- Mass divergence (`integral trace(H) = infinity`)
  - Lean: `PaperR1TotalMassDivergesAt`
  - Status: [x] theorem-shape matched
  - Note: concrete integration-model identification remains pending

- Limit-point/radius-collapse conclusion
  - Lean: `PaperR1RadiusCollapseAt`
  - Status: [x] theorem-shape matched
  - Note: concrete limit-point semantic identification remains pending

## 4) Non-Mainline Separation Rule

- `audit/v3.1_cs2_target_line_audit.md` is an internal CS2 closure audit.
- It must be treated as internal diagnostic/proof-closure context.
- It must not be used as a replacement statement for the external mass-theorem axis
  when describing the current mainline RH route.

## 5) Immediate Next Work (Mainline Only)

1. Add explicit Lean bridge lemmas for remaining semantic-internalization gaps in Section 3.
2. Keep `R1CitationStandardChain` as the single external-axis gate until those
   bridge lemmas are closed.
3. Update this checklist only on meaningful status transitions.

## 6) Formula Source Sync (2026-02-12)

- `v3.1` tex formula anchors verified and synced for R1 core shape:
  - `eq:R1-step` (`...v3.1.tex:1651`)
  - `eq:R1-disk` (`...v3.1.tex:1673`)
  - `eq:R1-circle-eq` (`...v3.1.tex:1689`)
  - `eq:R1-membership-identity` (`...v3.1.tex:1743`)
  - `eq:R1-radius` (`...v3.1.tex:1764`)
  - `eq:R1-collapse` (`...v3.1.tex:4675`)
- Lean reflection pass completed in:
  - `audit/formalization/lean_v3_1/LeanV31/R1ClassicalMassApplicability.lean`
- Targeted check:
  - `lake build LeanV31.R1ClassicalMassApplicability LeanV31.R1CitationStandardChain` passed.
