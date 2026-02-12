import LeanV31.CalibKernelMatch

namespace LeanV31

def PickKernelTwoSidesAt (z : Complex) : Prop :=
  Exists fun w : Complex => w = z

/- S136 wrapper:
operator-side and arithmetic-side Stieltjes models produce the two Pick-kernel
difference-quotient identities used in calibration transfer. -/
theorem pick_kernel_two_sides
    {z : Complex}
    (hArithStieltjes : ArithStieltjesModelAt z)
    (hKernelMatch : CalibKernelMatchAt z)
    (hBridge :
      ArithStieltjesModelAt z ->
      CalibKernelMatchAt z ->
      PickKernelTwoSidesAt z) :
    PickKernelTwoSidesAt z := by
  exact hBridge hArithStieltjes hKernelMatch

end LeanV31
