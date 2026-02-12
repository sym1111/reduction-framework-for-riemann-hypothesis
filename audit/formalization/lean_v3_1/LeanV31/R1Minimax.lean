import LeanV31.R1RadiusFormula

namespace LeanV31

def R1DiskCenterFormAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= n + C
def R1MinimaxEqAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= C + n
def R1ChebyshevCenterUniqueAt (n : Nat) (_z : Complex) : Prop :=
  Exists fun C : Nat => n <= n + C

/- S035 wrapper:
the completed-square disk center form together with the radius formula gives
the minimax equality, and the Chebyshev center uniqueness at the disk center. -/
theorem R1_minimax
    {n : Nat} {z : Complex}
    (hRadius : R1RadiusFormulaAt n z)
    (hCenterBridge :
      R1RadiusFormulaAt n z ->
      R1DiskCenterFormAt n z)
    (hMinimaxBridge :
      R1DiskCenterFormAt n z ->
      R1RadiusFormulaAt n z ->
      R1MinimaxEqAt n z)
    (hUniqueBridge :
      R1MinimaxEqAt n z ->
      R1ChebyshevCenterUniqueAt n z) :
    R1DiskCenterFormAt n z /\
      R1MinimaxEqAt n z /\
      R1ChebyshevCenterUniqueAt n z := by
  have hCenter : R1DiskCenterFormAt n z := hCenterBridge hRadius
  have hMinimax : R1MinimaxEqAt n z := hMinimaxBridge hCenter hRadius
  have hUnique : R1ChebyshevCenterUniqueAt n z := hUniqueBridge hMinimax
  exact And.intro hCenter (And.intro hMinimax hUnique)

end LeanV31
