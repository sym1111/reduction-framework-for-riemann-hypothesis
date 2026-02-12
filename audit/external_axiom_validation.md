# External Axiom Validation: `paper_external_mass_divergence_limitpoint`

Date: 2026-02-12

## Scope

This note validates what the single external axiom in the current Lean chain
is intended to represent, and whether the cited mathematical axis is standard
and RH-independent in dependency terms.

## Lean Axiom (Current Snapshot)

File:
`audit/formalization/lean_v3_1/LeanV31/R1CitationStandardChain.lean`

- declaration: line 122
- used at: lines 155 and 292

Signature (informal):

- assumptions:
  - `PaperR1ApplicabilityAt z`
  - `UpperHalfPlanePoint z`
  - `PaperR1TotalMassDivergesAt z`
- conclusion:
  - `PaperR1RadiusCollapseAt z`

So the axiom is a mass-divergence/limit-point step under paper applicability
conditions.

## External Sources Checked

1. Complex Analysis and Operator Theory (2021), Marciniak et al.
   - URL: https://link.springer.com/article/10.1007/s11785-021-01148-w
   - Relevant statement appears in Theorem 6.1 / Eq. (6.3):
     limit-point iff integral of `trace(H)` diverges.
   - The paper cites this as standard canonical-system theory and points to
     classical references.

2. Same paper reference list (classical lineage used for the criterion):
   - de Branges, *Hilbert Spaces of Entire Functions* (1968)
   - Winkler, *The Inverse Spectral Problem for Canonical Systems* (1995)
   - These are standard canonical-system sources, not RH-specific sources.

3. Romanov and Woracek (arXiv:1206.5550)
   - URL: https://arxiv.org/abs/1206.5550
   - Abstract-level statement recalls de Branges' theorem:
     for trace-normed canonical systems (`tr H = 1`) one is in the limit-point
     case.

## RH Independence Clarification

Validation result:

- In dependency terms, this axis is RH-independent:
  the cited limit-point criteria are stated/proved in canonical-system
  spectral theory without RH assumptions.
- This note does **not** claim set-theoretic independence from RH.
  The meaning here is proof-dependency independence (no RH hypothesis used).

## Why Keep This External Axis (Current Policy)

- The retained axiom corresponds to a standard canonical-systems theorem axis
  that is RH-independent in proof-dependency terms.
- Current remaining gap is semantic internalization:
  mapping manuscript-side predicates to concrete canonical-system objects and
  hypothesis formulas.
- Therefore, the project keeps exactly one external axis gate for this step and
  does not introduce any additional external mathematical axis.
- Removal condition is explicit: once concrete hypothesis-matching lemmas are
  fully internalized, replace this gate with an internal theorem path.

## Assumption-Matching Status (Lean <-> External Theorem)

Current matching intent:

- `PaperR1ChainBlockPSDAt` + `PaperR1CanonicalStepModelAt`
  - intended to encode the canonical-system Hamiltonian regularity/positivity
    regime needed by the cited theorem.
- `PaperR1WeylDiskRadiusModelAt`
  - intended to encode Weyl-disk/radius semantics.
- `UpperHalfPlanePoint z`
  - matches spectral parameter in upper half-plane.
- `PaperR1TotalMassDivergesAt z`
  - intended to represent divergence of the total mass
    (`integral trace(H) = infinity`).
- `PaperR1RadiusCollapseAt z`
  - intended to represent the limit-point / radius-collapse conclusion.

Current formal-traceability state:

- explicit Lean theorem-shape matching lemmas are now present in
  `audit/formalization/lean_v3_1/LeanV31/R1CitationStandardChain.lean`.
- core formula source anchors are pinned in v3.1 tex
  (`eq:R1-step`, `eq:R1-disk`, `eq:R1-circle-eq`, `eq:R1-membership-identity`,
  `eq:R1-radius`, `eq:R1-collapse`) and reflected structurally in
  `audit/formalization/lean_v3_1/LeanV31/R1ClassicalMassApplicability.lean`.
- remaining work is deeper semantic internalization to concrete canonical-system
  objects (not just interface/theorem-shape matching).

## Practical Conclusion

As of this snapshot, the single external axiom is consistent with a standard
canonical-systems limit-point criterion used in the literature and does not
introduce RH as a hidden premise. The remaining work is explicit hypothesis
matching/internalization, not a second external mathematical axis.
