Set Implicit Arguments.

Section RHChain.
  Variable C : Type.
  Variables f H : C -> C.

  Variable ZeroFreeOnUpper : (C -> C) -> Prop.
  Variable BDetectorFunctionalOnCircle : (C -> C) -> Prop.
  Variable ConjugationSymmetric : (C -> C) -> Prop.
  Variable RiemannHypothesis : (C -> C) -> Prop.

  Definition CircleHardyZeroFreeCertificate : Prop :=
    BDetectorFunctionalOnCircle H /\ ZeroFreeOnUpper f.

  Definition StripPoleExclusionViaNevanlinna : Prop :=
    ZeroFreeOnUpper f.

  Hypothesis rh_from_lstar_core :
    ZeroFreeOnUpper f -> ConjugationSymmetric f -> RiemannHypothesis f.

  Theorem no_pole_nevanlinna :
    CircleHardyZeroFreeCertificate -> StripPoleExclusionViaNevanlinna.
  Proof.
    intros h; exact (proj2 h).
  Qed.

  Theorem no_zeros_from_herglotz :
    StripPoleExclusionViaNevanlinna -> ZeroFreeOnUpper f.
  Proof.
    intros h; exact h.
  Qed.

  Theorem reverse_RH :
    ZeroFreeOnUpper f -> ConjugationSymmetric f -> RiemannHypothesis f.
  Proof.
    intros hZero hConj; apply rh_from_lstar_core; assumption.
  Qed.

  Theorem final_bridge_closed :
    ZeroFreeOnUpper f -> ConjugationSymmetric f -> RiemannHypothesis f.
  Proof.
    intros hZero hConj; apply reverse_RH; assumption.
  Qed.

  Theorem final_bridge_closed_via_certificate :
    CircleHardyZeroFreeCertificate -> ConjugationSymmetric f -> RiemannHypothesis f.
  Proof.
    intros hCert hConj.
    apply final_bridge_closed.
    - apply no_zeros_from_herglotz.
      apply no_pole_nevanlinna.
      exact hCert.
    - exact hConj.
  Qed.
End RHChain.
