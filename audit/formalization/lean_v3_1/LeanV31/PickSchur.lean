import LeanV31.PickHerglotz

namespace LeanV31

open scoped ComplexConjugate

noncomputable def pickKernelW (W : Complex -> Complex) : Complex -> Complex -> Complex :=
  fun z w => (1 - W z * conj (W w)) / (conj z - w)

/- S018 wrapper:
for holomorphic `W` on `C_+`, Schur property is equivalent to positivity of
the Schur Pick kernel. -/
theorem pick_schur
    {W : Complex -> Complex}
    (hHol : HolomorphicOnUpperHalfPlane W)
    (hForward :
      SchurOnUpperHalfPlane W -> KernelPSDOnUpper (pickKernelW W))
    (hBackward :
      KernelPSDOnUpper (pickKernelW W) -> SchurOnUpperHalfPlane W) :
    SchurOnUpperHalfPlane W <-> KernelPSDOnUpper (pickKernelW W) := by
  have _hHol := hHol
  constructor
  · intro hSchur
    exact hForward hSchur
  · intro hPsd
    exact hBackward hPsd

end LeanV31
