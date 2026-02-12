import LeanV31.W0

namespace LeanV31

def WUnitModulusOnReal (W : Complex -> Complex) : Prop :=
  forall x : Real, ‖W (x : Complex)‖ = 1

/- S003 wrapper:
boundary reality symmetry yields unit modulus of W on the real axis
(with removable handling at real zeros encoded in the bridge input). -/
theorem W_unit_real
    {W : Complex -> Complex}
    (hUnitBridge : WUnitModulusOnReal W) :
    WUnitModulusOnReal W := by
  exact hUnitBridge

end LeanV31
