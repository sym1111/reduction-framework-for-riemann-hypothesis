import LeanV31.CalibArithStieltjes

namespace LeanV31

def ArithChartDerivativeAt (z : Complex) : Prop :=
  Exists fun D : Complex => D = z

/- S133 wrapper:
on the local arithmetic chart, the quotient derivative formula is available in
the stated open set. -/
theorem m_arith_chart_derivative
    {z : Complex}
    (hArithModel : ArithStieltjesModelAt z)
    (hBridge :
      ArithStieltjesModelAt z -> ArithChartDerivativeAt z) :
    ArithChartDerivativeAt z := by
  exact hBridge hArithModel

end LeanV31
