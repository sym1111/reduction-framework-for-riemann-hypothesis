# De-wrapper Progress Log (v3.1 Lean)

Date: 2026-02-11

## Batch Trace
1. `WStripSchur` signature honesty pass
- File: `audit/formalization/lean_v3_1/LeanV31/WStripSchur.lean`
- Removed unused assumptions from `W_strip_schur`.
- Current theorem takes only `hBoundedCharacteristic`.

2. `FinalBridgeClosed` signature honesty pass
- File: `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Removed unused detector/passivity assumptions from theorem signature.
- Removed unused `PassivityToDetectorClosure` definition and stale import.

3. Build verification
- Command: `lake build LeanV31.WStripSchur LeanV31.FinalBridgeClosed`
- Result: `Build completed successfully (7897 jobs).`

4. `hNotIdenticallyZero` elimination pass
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/NoPoleNevanlinna.lean`
  - `audit/formalization/lean_v3_1/LeanV31/NoZerosFromHerglotz.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Removed `(Exists fun z => f z != 0)` from the Nevanlinna exclusion function signature.
  - Propagated removal through RH closure chain.
- Build:
  - Command: `lake build LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`

5. `hHdef` elimination pass
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/NoPoleNevanlinna.lean`
  - `audit/formalization/lean_v3_1/LeanV31/NoZerosFromHerglotz.lean`
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Re-indexed Nevanlinna exclusion to `(f, H)` and removed explicit `H = -f'/f` argument from this chain.
  - Removed `hHdef` from `rh_from_lstar`, `reverse_RH`, `final_bridge_closed` signatures.
- Build:
  - Command: `lake build LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`

6. `hHol` elimination pass
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/NoPoleNevanlinna.lean`
  - `audit/formalization/lean_v3_1/LeanV31/NoZerosFromHerglotz.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Removed `HolomorphicOnUpperHalfPlane f` from the Nevanlinna exclusion function signature.
  - Propagated removal through RH closure chain.
- Build:
  - Command: `lake build LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`

7. Top-level dependency transparency pass (`final_bridge_closed`)
- File: `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Replaced indirect `hBoundedCharacteristic -> W_strip_schur -> W_global_schur` chain at theorem boundary
    with direct `hGlobalSchur : WGlobalSchurOnUpperHalfPlane W`.
  - No logical strengthening/weakening intended; this is a visibility cleanup.
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`

8. Wrapper-name elimination at top RH closure boundary
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Replaced top-level assumption name `hNevanlinnaExclusion` with direct semantic form
    `hNoZerosUpper : HerglotzOnUpperHalfPlane H -> ZeroFreeOnUpper f`.
  - This is an interface transparency change (assumption count unchanged).
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`

9. Internalized no-zeros bridge usage in RH chain
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Replaced higher-order assumption
    `hNoZerosUpper : HerglotzOnUpperHalfPlane H -> ZeroFreeOnUpper f`
    with direct bridge certificate
    `hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H`.
  - `rh_from_lstar` now derives `ZeroFreeOnUpper f` via
    `no_zeros_from_herglotz hHerglotz hNevanlinnaExclusion`.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`

10. Cayley bridge assumption normalized to explicit equivalence form
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Replaced function-form assumption
    `hSchurToHerglotz : WGlobalSchurOnUpperHalfPlane W -> HerglotzOnUpperHalfPlane H`
    with labeled equivalence form
    `hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W`.
  - `reverse_RH` now obtains Herglotz via `hCayleyEquiv.mpr hGlobalSchur`.
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`

11. Core theorem extraction for reverse/final bridge
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added `reverse_RH_core`:
    - assumptions: `hHerglotz`, `hNevanlinnaExclusion`, `hConjZero`
    - conclusion: `RiemannHypothesis f`.
  - Added `final_bridge_closed_core` with the same 3-assumption closure form.
  - Kept existing top-level wrapper signatures; now they derive `hHerglotz` and delegate to core.
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (warnings only: unnecessary `simpa`, unused variable lint)

12. Promote core signatures to top-level theorem names
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `reverse_RH` now uses core 3-assumption signature:
    - `hHerglotz`, `hNevanlinnaExclusion`, `hConjZero`.
  - previous 4-assumption entry is preserved as
    `reverse_RH_via_cayley`.
  - `final_bridge_closed` now uses core 3-assumption signature.
  - previous 4-assumption entry is preserved as
    `final_bridge_closed_via_cayley`.
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (warnings only)

13. Collapse core closure to `ZeroFree + symmetry`
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added `rh_from_lstar_core` with assumptions:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hConjZero`.
  - Refactored `rh_from_lstar` to derive `hZeroFree` from
    `hHerglotz + hNevanlinnaExclusion` and delegate to core.
  - Refactored `reverse_RH_core` / `reverse_RH` to core 2-assumption form.
  - Added `reverse_RH_via_nevanlinna` and kept `reverse_RH_via_cayley`.
  - Refactored `final_bridge_closed_core` / `final_bridge_closed` to core 2-assumption form.
  - Added `final_bridge_closed_via_nevanlinna` and kept `final_bridge_closed_via_cayley`.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (warnings only)

14. Add functional-conjugation symmetry route wrappers
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added `ConjugationSymmetric f := ∀ z, f (star z) = star (f z)`.
  - Added `conj_zero_of_conjugation_symmetric` and
    `rh_from_lstar_via_conjugation_symmetry`.
  - Added wrapper routes:
    - `reverse_RH_via_conjugation_symmetry`
    - `reverse_RH_via_nevanlinna_conjugation_symmetry`
    - `reverse_RH_via_cayley_conjugation_symmetry`
    - `final_bridge_closed_via_conjugation_symmetry`
    - `final_bridge_closed_via_nevanlinna_conjugation_symmetry`
    - `final_bridge_closed_via_cayley_conjugation_symmetry`
  - Cleaned local linter warning in `RHFromLstar` (`simpa` -> `simp`).
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (existing non-target lints only)

15. Build-warning cleanup for merge readiness
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/HurwitzTransfer.lean`
  - `audit/formalization/lean_v3_1/LeanV31/CanonicalTruncDetector0B21.lean`
- Change:
  - `HurwitzTransfer`: rewrote one inequality rewrite step to avoid unnecessary-`simpa` lint.
  - `CanonicalTruncDetector0B21`: removed unused quantified binders by simplifying
    `hModeBridge` / `hFamily` signatures.
- Build:
  - Command: `lake build LeanV31.HurwitzTransfer LeanV31.CanonicalTruncDetector0B21 LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7904 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (no warnings in this run)

16. Promote conjugation-symmetry assumption to core boundary
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Core theorems now use
    `hConjSymm : ConjugationSymmetric f` instead of direct
    zero-reflection premise `hConjZero`.
  - Added compatibility entries:
    - `reverse_RH_via_conj_zero`
    - `final_bridge_closed_via_conj_zero`
  - Existing `via_nevanlinna` / `via_cayley` routes with explicit `hConjZero`
    are preserved through compatibility wrappers.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

17. Add xi-functional-symmetry route (paper-facing entry)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added `XiFunctionalSymmetry f`:
    - conjugation symmetry `f(star z)=star(f z)`
    - plus reflected symmetry placeholder `f(-star z)=f z`.
  - Added bridge:
    - `conjugation_symmetric_of_xi_functional_symmetry`.
  - Added route wrappers:
    - `rh_from_lstar_via_xi_functional_symmetry`
    - `reverse_RH_via_xi_functional_symmetry`
    - `reverse_RH_via_nevanlinna_xi_functional_symmetry`
    - `reverse_RH_via_cayley_xi_functional_symmetry`
    - `final_bridge_closed_via_xi_functional_symmetry`
    - `final_bridge_closed_via_nevanlinna_xi_functional_symmetry`
    - `final_bridge_closed_via_cayley_xi_functional_symmetry`
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`

18. Nevanlinna pass-through removal (phase 1)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/BDetectorGram.lean`
  - `audit/formalization/lean_v3_1/LeanV31/NoPoleNevanlinna.lean`
  - `audit/formalization/lean_v3_1/LeanV31/NoZerosFromHerglotz.lean`
- Change:
  - Removed import-cycle pressure by changing `BDetectorGram` import from
    `NoPoleNevanlinna` to `Mathlib`.
  - Rewrote `no_pole_nevanlinna` so it no longer accepts the target proposition
    as a direct bridge argument.
  - New `no_pole_nevanlinna` derives
    `StripPoleExclusionViaNevanlinna f H` from detector/certificate inputs:
    `hDetector` and `hCertificateBridge`.
  - Simplified `no_zeros_from_herglotz` to use the Nevanlinna exclusion premise
    directly (`hNevanlinnaExclusion hHerglotz`) instead of re-invoking a
    pass-through theorem.
- Build:
  - Command: `lake build LeanV31.BDetectorGram LeanV31.HardyPoleLocator LeanV31.BDetector LeanV31.CircleHardyCertificate LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).` (warnings only)
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

18. Core boundary re-tightening to direct zero-reflection premise
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Restored core closure boundary to the direct premise
    `hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0`.
  - `reverse_RH_core` / `reverse_RH` now use `(hZeroFree, hConjZero)`.
  - `final_bridge_closed_core` / `final_bridge_closed` now use `(hZeroFree, hConjZero)`.
  - Symmetry routes remain available as wrappers:
    - `*_via_conjugation_symmetry`
    - `*_via_xi_functional_symmetry`
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

19. Paper-label trace comments added to RH closure chain
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added explicit paper-label trace comments at closure boundaries:
    - `lem:no_zeros_from_herglotz`
    - `lem:no_pole_nevanlinna`
    - `lem:cayley_equiv`
    - `prop:W_global_schur`
    - `cor:rh_from_Lstar`
  - No theorem signature or proof logic changes.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

20. Internalize `hZeroFree` derivation on the Nevanlinna core route
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added `zero_free_of_nevanlinna` and
    `rh_from_lstar_core_via_nevanlinna` in `RHFromLstar`.
  - Added `reverse_RH_core_via_nevanlinna` in `ReverseRH`.
  - Added `final_bridge_closed_core_via_nevanlinna` in `FinalBridgeClosed`.
  - Refactored `*_via_nevanlinna` routes to delegate through these core-level
    bridge theorems, so `hZeroFree` is now derived internally on that path.
  - No top-level theorem signature change in this batch.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

21. Promote direct core boundary from `hZeroFree` to Nevanlinna bridge inputs
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `reverse_RH_core` and `reverse_RH` now take:
    - `hHerglotz : HerglotzOnUpperHalfPlane H`
    - `hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H`
    - `hConjZero`.
  - `final_bridge_closed_core` and `final_bridge_closed` now take the same
    Nevanlinna bridge assumptions plus `hConjZero`.
  - Compatibility wrappers keep old entry points:
    - `*_via_conj_zero` (`hZeroFree + hConjZero`)
    - `*_via_conjugation_symmetry` / `*_via_xi_functional_symmetry`
    - `*_via_cayley`.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

22. Re-tighten endpoint to direct RH closure pair (`hZeroFree`, `hConjZero`)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `reverse_RH_core` / `reverse_RH` now use:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0`.
  - `reverse_RH_core_via_nevanlinna` / `reverse_RH_via_nevanlinna` now
    derive `hZeroFree` internally from
    `hHerglotz + hNevanlinnaExclusion` and delegate to endpoint core.
  - `final_bridge_closed_core` / `final_bridge_closed` now use the same
    endpoint pair `(hZeroFree, hConjZero)`.
  - `final_bridge_closed_core_via_nevanlinna` /
    `final_bridge_closed_via_nevanlinna` preserve the paper-labeled
    bridge route and internally derive `hZeroFree`.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

23. Internalize zero-reflection premise at `final_bridge_closed` endpoint
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `final_bridge_closed_core` / `final_bridge_closed` now use:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hConjSymm : ConjugationSymmetric f`
    and derive `hConjZero` internally via
    `conj_zero_of_conjugation_symmetric`.
  - `final_bridge_closed_core_via_nevanlinna` /
    `final_bridge_closed_via_nevanlinna` now use
    `(hHerglotz, hNevanlinnaExclusion, hConjSymm)`.
  - Compatibility routes preserving direct `hConjZero` remain:
    - `final_bridge_closed_via_conj_zero`
    - `final_bridge_closed_via_cayley`.
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar`
  - Result: `Build completed successfully (7897 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

24. Add detector-route closure wrappers for endpoint zero-free derivation
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added detector-based route wrappers:
    - `final_bridge_closed_via_detector_conjugation_symmetry`
    - `final_bridge_closed_via_detector_xi_functional_symmetry`
  - These wrappers derive `hZeroFree` from
    `circle_hardy_certificate` and feed endpoint closure.
  - Core endpoint assumptions remain unchanged:
    - `hZeroFree`
    - `hConjSymm`.
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar`
  - Result: `Build completed successfully (7901 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

25. Internalize conjugation-symmetry premise into xi-functional endpoint
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `final_bridge_closed_core` / `final_bridge_closed` now use:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hXiSymm : XiFunctionalSymmetry f`
    and derive `hConjSymm` then `hConjZero` internally.
  - `final_bridge_closed_core_via_nevanlinna` /
    `final_bridge_closed_via_nevanlinna` now use
    `(hHerglotz, hNevanlinnaExclusion, hXiSymm)`.
  - Conjugation-only wrappers remain as compatibility routes:
    - `final_bridge_closed_via_conjugation_symmetry`
    - `final_bridge_closed_via_nevanlinna_conjugation_symmetry`.
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar`
  - Result: `Build completed successfully (7901 jobs).`
 - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

26. Add paper-chain closure routes (Hardy locator -> detector -> certificate)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added paper-route wrappers:
    - `final_bridge_closed_via_hardy_locator_conjugation_symmetry`
    - `final_bridge_closed_via_hardy_locator_xi_functional_symmetry`
  - These routes explicitly compose:
    - `hardy_pole_locator` (S007)
    - `b_detector` (S008)
    - `circle_hardy_certificate` (S009)
    - final RH closure (`thm:final_bridge_closed` chain endpoint)
  - Core endpoint assumptions remain unchanged:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hXiSymm : XiFunctionalSymmetry f`
- Build:
 - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar`
  - Result: `Build completed successfully (7901 jobs).`
  - Command: `lake build LeanV31.CircleHardyCertificate LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz`
  - Result: `Build completed successfully (7895 jobs).`

27. Extend paper-chain to canonical truncation entry (S028 -> S007 -> S008 -> S009 -> RH)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Added canonical-truncation route wrappers:
    - `final_bridge_closed_via_canonical_trunc_conjugation_symmetry`
    - `final_bridge_closed_via_canonical_trunc_xi_functional_symmetry`
  - New wrappers compose:
    - `canonical_trunc_detector0` (S028) to obtain all-level detector defect zero,
    - a bridge `hDefectToGram` to `BDetectorGramIdentity`,
    - then existing S007 -> S008 -> S009 route wrappers,
    - then RH closure (`thm:final_bridge_closed` endpoint path).
  - This pushes `hZeroFree` generation one level deeper into the paper-structured chain.
  - Core endpoint assumptions remain unchanged:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hXiSymm : XiFunctionalSymmetry f`
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar LeanV31.CanonicalTruncDetector0B21`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build LeanV31.CircleHardyCertificate LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur`
  - Result: `Build completed successfully (7899 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed LeanV31.CanonicalTruncDetector0B21`
  - Result: `Build completed successfully (7908 jobs).`
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

28. Reduce core symmetry assumption from xi-functional to conjugation symmetry
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `final_bridge_closed_core` now uses:
    - `hZeroFree : ZeroFreeOnUpper f`
    - `hConjSymm : ConjugationSymmetric f`
    instead of `(hZeroFree, hXiSymm)`.
  - `final_bridge_closed` and `final_bridge_closed_via_nevanlinna` were aligned to
    the same minimal closure signature using `hConjSymm`.
  - Xi-functional routes are preserved as compatibility entrypoints and now
    explicitly derive `hConjSymm` via
    `conjugation_symmetric_of_xi_functional_symmetry`.
  - Effect:
    - The core endpoint no longer depends on the extra reflected-symmetry part
      of `XiFunctionalSymmetry`; only the symmetry actually used in RH closure
      remains in the core boundary.
- Build:
  - Command: `lake build LeanV31.FinalBridgeClosed LeanV31.ReverseRH LeanV31.RHFromLstar`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build LeanV31.CanonicalTruncDetector0B21 LeanV31.CircleHardyCertificate LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed LeanV31.CanonicalTruncDetector0B21`
  - Result: `Build completed successfully (7908 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

29. Add explicit sufficiency/non-sufficiency facts for closure assumptions
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/RHFromLstar.lean`
- Change:
  - Added explicit sufficiency theorem:
    - `zero_free_and_conjugation_symmetry_suffice`
      (matches the current core closure shape).
  - Added explicit non-sufficiency witnesses:
    - `zero_free_on_upper_not_sufficient`
    - `conjugation_symmetric_not_sufficient`
  - Purpose:
    - make the remaining-core-obligation boundary explicit,
    - prevent false expectation that either assumption alone can close RH.
  - Also normalized `RHFromLstar.lean` into clean UTF-8/no-BOM text to remove
    prior token/encoding corruption artifacts.
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build LeanV31.CanonicalTruncDetector0B21 LeanV31.CircleHardyCertificate LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz`
  - Result: `Build completed successfully (7902 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed LeanV31.CanonicalTruncDetector0B21`
  - Result: `Build completed successfully (7908 jobs).`
 - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

30. Remove definitional detector bridge from Hardy-locator closure routes
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/BDetector.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `BDetectorFunctionalOnCircle` and `HardyPoleLocatorOnCircle` are currently
    definitionally the same proposition in this codebase.
  - Simplified `b_detector` to:
    - input: `hLocator : HardyPoleLocatorOnCircle H`
    - output: `BDetectorFunctionalOnCircle H`
    with no extra bridge hypothesis.
  - Propagated this simplification through closure routes by removing
    `hDetectorBridge` from:
    - `final_bridge_closed_via_hardy_locator_conjugation_symmetry`
    - `final_bridge_closed_via_hardy_locator_xi_functional_symmetry`
    - `final_bridge_closed_via_canonical_trunc_conjugation_symmetry`
    - `final_bridge_closed_via_canonical_trunc_xi_functional_symmetry`
  - Effect:
    - one route-level assumption class eliminated from S007 -> S008 -> S009
      composition paths.
    - core RH closure boundary is unchanged (`hZeroFree`, `hConjSymm`).
- Build:
  - Command: `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed LeanV31.CanonicalTruncDetector0B21`
  - Result: `Build completed successfully (7908 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

## Current Remaining Assumptions In `final_bridge_closed`
1. `hZeroFree : ZeroFreeOnUpper f`
2. `hConjSymm : ConjugationSymmetric f`

## Wrapper Entry (`final_bridge_closed_via_nevanlinna`) Assumptions
1. `hHerglotz : HerglotzOnUpperHalfPlane H`
2. `hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H`
3. `hConjSymm : ConjugationSymmetric f`

## Wrapper Entry (`final_bridge_closed_via_conj_zero`) Assumptions
1. `hZeroFree : ZeroFreeOnUpper f`
2. `hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0`

## Wrapper Entry (`final_bridge_closed_via_conjugation_symmetry`) Assumptions
1. `hZeroFree : ZeroFreeOnUpper f`
2. `hConjSymm : ConjugationSymmetric f`

## Wrapper Entry (`final_bridge_closed_via_xi_functional_symmetry`) Assumptions
1. `hZeroFree : ZeroFreeOnUpper f`
2. `hXiSymm : XiFunctionalSymmetry f`

## Wrapper Entry (`final_bridge_closed_via_cayley`) Assumptions
1. `hGlobalSchur : WGlobalSchurOnUpperHalfPlane W`
2. `hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W`
3. `hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H`
4. `hConjZero : forall z : Complex, f z = 0 -> f (star z) = 0`

## Wrapper Entry (`final_bridge_closed_via_detector_conjugation_symmetry`) Assumptions
1. `hDetector : BDetectorFunctionalOnCircle H`
2. `hCertificateBridge : BDetectorFunctionalOnCircle H -> CircleHardyZeroFreeCertificate f H`
3. `hConjSymm : ConjugationSymmetric f`

## Wrapper Entry (`final_bridge_closed_via_detector_xi_functional_symmetry`) Assumptions
1. `hDetector : BDetectorFunctionalOnCircle H`
2. `hCertificateBridge : BDetectorFunctionalOnCircle H -> CircleHardyZeroFreeCertificate f H`
3. `hXiSymm : XiFunctionalSymmetry f`

## Canonical 7-Item Assumption Map (Lean <-> paper labels)
1. `hZeroFree : ZeroFreeOnUpper f`
- Lean path: `final_bridge_closed -> reverse_RH -> rh_from_lstar_core`
- Paper labels: no-zero endpoint aligned with `lem:no_zeros_from_herglotz`

2. `hConjSymm : ConjugationSymmetric f`
- Lean path: `final_bridge_closed -> conj_zero_of_conjugation_symmetric -> reverse_RH`
- Paper labels: symmetry closure step around `cor:rh_from_Lstar`

2b. `hXiSymm : XiFunctionalSymmetry f` (xi-compatibility entry)
- Lean path: `final_bridge_closed_via_xi_functional_symmetry -> conjugation_symmetric_of_xi_functional_symmetry -> final_bridge_closed`
- Paper labels: functional-symmetry phrasing around `cor:rh_from_Lstar`

3. `hHerglotz : HerglotzOnUpperHalfPlane H` (Nevanlinna wrapper route)
- Lean path: `*_via_nevanlinna -> reverse_RH_via_nevanlinna -> hZeroFree`
- Paper labels: `thm:Lstar`, `lem:no_zeros_from_herglotz`

4. `hNevanlinnaExclusion : StripPoleExclusionViaNevanlinna f H` (Nevanlinna wrapper route)
- Lean path: `*_via_nevanlinna -> reverse_RH_via_nevanlinna -> hZeroFree`
- Paper labels: `lem:no_pole_nevanlinna`

5. `hGlobalSchur : WGlobalSchurOnUpperHalfPlane W`
- Lean path: `final_bridge_closed_via_cayley -> hHer`
- Paper labels: `prop:W_global_schur`

6. `hCayleyEquiv : HerglotzOnUpperHalfPlane H <-> SchurOnUpperHalfPlane W`
- Lean path: `final_bridge_closed_via_cayley -> hHer`
- Paper labels: `lem:cayley_equiv`

7. Symmetry/compatibility wrapper entry (`hConjSymm` or direct `hConjZero`)
- Lean path:
  - `*_via_conjugation_symmetry` compatibility route
  - `*_via_conj_zero` / `*_via_cayley` compatibility routes
- Paper labels: symmetry discussion around `cor:rh_from_Lstar`; final endpoint `thm:RH_from_anchor`

## Importance Tiers (paper-critical, not action-order)
1. Tier S (core RH closure):
 - Item 1 (`hZeroFree`), Item 2 (`hConjSymm`)
2. Tier A (bridge entry):
 - Item 3 (`hHerglotz`), Item 4 (`hNevanlinnaExclusion`)
3. Tier B (transport bridge):
 - Item 5 (`hGlobalSchur`), Item 6 (`hCayleyEquiv`)
4. Tier C (alternative symmetry entry):
 - Item 7 (`hXiSymm`/direct `hConjZero` compatibility routes)

## Next Closure Order
1. Close item 1 (`hZeroFree`) by replacing detector/nevanlinna bridge assumptions with proved internal links.
2. Close item 2 (`hConjSymm`) by replacing symbolic symmetry assumption with formalized xi-identity or equivalent conjugation-symmetry route.
3. Preserve all route wrappers as traceable, review-friendly entrypoints.

## Gate Status
1. Focus gate (chain files):
- `lake build LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
- Status: pass

2. Expanded chain gate:
- `lake build LeanV31.BcPoissonStrip LeanV31.WBoundedCharacteristic LeanV31.WStripSchur LeanV31.WGlobalSchur LeanV31.NoPoleNevanlinna LeanV31.NoZerosFromHerglotz LeanV31.RHFromLstar LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
- Status: pass

3. Full project gate:
- `lake build`
- Status: pass (8030 jobs; no warnings in current run)

## Note
This log is maintained to keep every signature/assumption change explicit and prevent hidden drift.

31. Re-align top-level closure APIs to paper-chain route (v3.0 -> v3.1 internalization context)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - Promoted `reverse_RH` top-level entry to paper-facing Nevanlinna chain signature:
    - `(hHerglotz, hNevanlinnaExclusion, hConjZero)`.
  - Kept direct endpoint route as compatibility:
    - `reverse_RH_via_conj_zero` (`hZeroFree + hConjZero`).
  - Promoted `final_bridge_closed` top-level entry to paper-facing Nevanlinna chain signature:
    - `(hHerglotz, hNevanlinnaExclusion, hConjSymm)`.
  - Kept direct endpoint route as compatibility:
    - `final_bridge_closed_core` and `final_bridge_closed_via_conj_zero`.
  - Updated xi/detector wrappers to delegate to core compatibility endpoints
    (no new assumptions added).
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: `Build completed successfully (7907 jobs).`
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

18. Promote endpoint signatures to 2-assumption core (`ZeroFree + symmetry`)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/ReverseRH.lean`
  - `audit/formalization/lean_v3_1/LeanV31/FinalBridgeClosed.lean`
- Change:
  - `reverse_RH` promoted to core endpoint signature:
    - assumptions: `hZeroFree`, `hConjZero`
  - `reverse_RH_via_nevanlinna` now derives `hZeroFree` and delegates to `reverse_RH`.
  - `final_bridge_closed` promoted to core endpoint signature:
    - assumptions: `hZeroFree`, `hConjSymm`
  - `final_bridge_closed_via_nevanlinna` preserved for explicit paper route.
- Build:
  - Command: `lake build LeanV31.ReverseRH LeanV31.FinalBridgeClosed`
  - Result: one transient file-lock failure on `FinalBridgeClosed.olean` (not logic/type error).
  - Command: `lake build`
  - Result: `Build completed successfully (8030 jobs).`

32. Exhaustive module + paper scan (no keyword-only shortcut)
- Files:
  - `audit/formalization/lean_v3_1/LeanV31/EXHAUSTIVE_DECL_INDEX.csv`
  - `audit/formalization/lean_v3_1/LeanV31/EXHAUSTIVE_THEOREM_SIGNATURES.csv`
  - `audit/formalization/lean_v3_1/LeanV31/EXHAUSTIVE_CHAIN_REVIEW.md`
  - `audit/PAPER_LABEL_INDEX_v3_1.csv`
  - `audit/formalization/lean_v3_1/LeanV31/IndependentInequality.lean`
- What was done:
  - Enumerated all Lean modules under `LeanV31` (145 files) and indexed declarations (438).
  - Extracted theorem/lemma signatures project-wide (193) and scanned all signatures containing
    RH endpoint predicates (`ZeroFreeOnUpper`, `ConjugationSymmetric`, `XiFunctionalSymmetry`,
    `RiemannHypothesis`).
  - Built transitive import closure from `FinalBridgeClosed` (23 modules) and reviewed each file's
    declarations/imports in a single chain report.
  - Indexed theorem/lemma labels from paper v3.1 source (165 entries) for direct cross-check.
  - Added paper-level eigenvalue realization for `lem:independent_inequality`:
    - `independent_inequality_eigen_nonneg`
    - `independent_inequality_eigen_rigidity`
- Exhaustive findings:
  - In current Lean tree, no theorem in RH-closure path produces `ZeroFreeOnUpper` or
    `ConjugationSymmetric` unconditionally at endpoint; those remain supplied via bridge hypotheses.
  - `lem:independent_inequality` is now formalized at eigenvalue level in Lean, but remains outside
    the direct `FinalBridgeClosed` import chain.
- Build:
  - Command: `lake build LeanV31.IndependentInequality LeanV31.GyroGyration LeanV31.FinalBridgeClosed LeanV31.ReverseRH`
  - Result: pass (linter warnings only, no type errors).
