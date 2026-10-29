import RiemannGaussian.SemiprimeUniversalSourceExecution
open RiemannGaussian
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

def initial : UniversalType 2 2 1 := ⟨fun _=>0,fun _ _=>1⟩
def moved : UniversalType 2 2 1 := swapPositions 0 {1} initial
#eval (SemiprimeUniversalSourceExecution.universalRow 0 1 initial initial).coefficients
#eval (SemiprimeUniversalSourceExecution.universalRow 0 1 initial moved).coefficients
#eval SemiprimeUniversalSourceExecution.numerator 0 1 0 0 initial moved
#eval SemiprimeUniversalSourceExecution.constraint 0 1 0 0 initial moved
