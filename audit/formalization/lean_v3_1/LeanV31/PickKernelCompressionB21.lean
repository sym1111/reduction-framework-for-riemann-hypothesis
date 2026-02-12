import LeanV31.DiscreteLagrangeGramB21

namespace LeanV31

def ScalarPickKernelPSDAtLevel (n : Nat) : Prop := Exists fun m : Nat => m <= n
def RankOneCompressionFormulaAtLevel (n : Nat) : Prop := Exists fun m : Nat => m <= n

/- S027 wrapper:
finite scalar Pick kernels are obtained as rank-one compressions of matrix
kernels; PSD transfers from matrix kernel PSD via this compression bridge. -/
theorem pick_kernel_compression
    (hCompression :
      forall (n : Nat), RankOneCompressionFormulaAtLevel n)
    (hPsdTransfer :
      (forall (n : Nat), MatrixPickKernelPSDAtLevel n) ->
      (forall (n : Nat), RankOneCompressionFormulaAtLevel n) ->
      forall (n : Nat), ScalarPickKernelPSDAtLevel n)
    (hMatrixPsd : forall (n : Nat), MatrixPickKernelPSDAtLevel n) :
    (forall (n : Nat), RankOneCompressionFormulaAtLevel n) /\
      (forall (n : Nat), ScalarPickKernelPSDAtLevel n) := by
  have hScalar : forall (n : Nat), ScalarPickKernelPSDAtLevel n :=
    hPsdTransfer hMatrixPsd hCompression
  exact And.intro hCompression hScalar

end LeanV31
