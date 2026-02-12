import LeanV31.RHFromAnchor

namespace LeanV31

open scoped ComplexConjugate

noncomputable def pickKernelH (H : Complex -> Complex) : Complex -> Complex -> Complex :=
  fun z w => (H z - conj (H w)) / (conj z - w)

def KernelPSDOnUpper (K : Complex -> Complex -> Complex) : Prop :=
  forall n : Nat,
    forall z : Fin n -> Complex,
      (forall i : Fin n, 0 < (z i).im) ->
        forall c : Fin n -> Complex,
          0 <= Complex.re (∑ i : Fin n, ∑ j : Fin n, conj (c i) * K (z i) (z j) * c j)

/- S017 wrapper:
for holomorphic `H` on `C_+`, Herglotz property is equivalent to positivity of
the Pick kernel. Forward/backward analytic bridges are carried as hypotheses. -/
theorem pick_herglotz
    {H : Complex -> Complex}
    (hHol : HolomorphicOnUpperHalfPlane H)
    (hForward :
      HerglotzOnUpperHalfPlane H -> KernelPSDOnUpper (pickKernelH H))
    (hBackward :
      KernelPSDOnUpper (pickKernelH H) -> HerglotzOnUpperHalfPlane H) :
    HerglotzOnUpperHalfPlane H <-> KernelPSDOnUpper (pickKernelH H) := by
  have _hHol := hHol
  constructor
  · intro hHer
    exact hForward hHer
  · intro hPsd
    exact hBackward hPsd

end LeanV31
