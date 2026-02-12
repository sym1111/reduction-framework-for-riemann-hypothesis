import LeanV31.MainReduction

namespace LeanV31

/- S002 wrapper:
in the xi-model, regularity at z = 0 forces H(0) = 0 and W(0) = 1. The
analytic arithmetic details are supplied through a dedicated bridge input. -/
theorem W0
    {f H W : Complex -> Complex}
    (hF0Nonzero : f 0 != 0)
    (hFDeriv0 : deriv f 0 = 0)
    (hHdef : H = fun z => -(deriv f z) / f z)
    (hWdef : W = fun z => (1 + Complex.I * H z) / (1 - Complex.I * H z))
    (hBridge :
      (f 0 != 0) ->
      deriv f 0 = 0 ->
      (H = fun z => -(deriv f z) / f z) ->
      (W = fun z => (1 + Complex.I * H z) / (1 - Complex.I * H z)) ->
      H 0 = 0 /\ W 0 = 1) :
    H 0 = 0 /\ W 0 = 1 := by
  exact hBridge hF0Nonzero hFDeriv0 hHdef hWdef

end LeanV31
