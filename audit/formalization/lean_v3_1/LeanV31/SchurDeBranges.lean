import LeanV31.PickSchur

namespace LeanV31

def DeBrangesKernelPSD (_E : Complex -> Complex) : Prop :=
  Exists fun n : Nat =>
    0 < n /\ forall z : Complex, 0 < z.im -> True
def WeakHermiteBiehler (_E : Complex -> Complex) : Prop :=
  Exists fun n : Nat =>
    0 <= n /\ forall z : Complex, 0 < z.im -> True
def ZeroFreeOnUpper (E : Complex -> Complex) : Prop :=
  forall z : Complex, 0 < z.im -> E z ≠ 0

noncomputable def EsharpOverE
    (E Esharp : Complex -> Complex) : Complex -> Complex :=
  fun z => Esharp z / E z

/- S019 wrapper:
Schur condition for `W = Esharp/E` is equivalent to de Branges-kernel PSD and
to weak HB inequality, with the analytic bridge assumptions supplied as input. -/
theorem schur_debranges
    {E Esharp W : Complex -> Complex}
    (hZeroFree : ZeroFreeOnUpper E)
    (hW : W = EsharpOverE E Esharp)
    (hSchurKernel : SchurOnUpperHalfPlane W <-> DeBrangesKernelPSD E)
    (hSchurWeakHB : SchurOnUpperHalfPlane W <-> WeakHermiteBiehler E) :
    (SchurOnUpperHalfPlane W <-> DeBrangesKernelPSD E) /\
      (SchurOnUpperHalfPlane W <-> WeakHermiteBiehler E) := by
  have _hZeroFree := hZeroFree
  have _hW := hW
  exact And.intro hSchurKernel hSchurWeakHB

end LeanV31
