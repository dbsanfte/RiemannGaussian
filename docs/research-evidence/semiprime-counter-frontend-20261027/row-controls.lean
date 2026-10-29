import RiemannGaussian.SemiprimeRowSelectionTracked
open RiemannGaussian.SemiprimeRowSelectionExecution
open RiemannGaussian.SemiprimeRowSelectionTracked

def sample : Fin 3 → Fin 3 → ℤ := !![0,1,1;1,2,3;2,4,6]
def zeroMatrix : Fin 2 → Fin 3 → ℤ := fun _ _ => 0
#eval (selectedIndices sample).map Fin.val
#eval (selectedIndices zeroMatrix).map Fin.val
#eval (runTracked sample (List.finRange 3)).operations
#eval (runTracked sample (List.finRange 3)).tests
#eval inSpan (run sample (List.finRange 3)) (fun v => (![0,1,1] : Fin 3 → ℚ) v)
#eval inSpan (run sample (List.finRange 3)) (fun v => (![0,0,1] : Fin 3 → ℚ) v)
