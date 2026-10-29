import RiemannGaussian.SemiprimeBinomialExecutionBounds
open scoped BigOperators
open RiemannGaussian.SemiprimeBinomialExecution
open RiemannGaussian.SemiprimeBinomialExecutionTracked
#eval List.ofFn (acquiredParity 0 4)
#eval List.ofFn (acquiredParity 1 3)
#eval List.ofFn (acquiredParity 2 3)
#eval List.ofFn (acquiredParity 3 1)
#eval List.ofFn (acquiredParity 2 0)
#eval ((acquireParity 1 3).arithmetic,(acquireParity 1 3).reads)
#eval List.ofFn (fun d : Fin 3 => ∑ j : Fin 3,acquiredParity 1 3 j*((1+d.val).choose j.val : ℤ))
#eval List.ofFn (fun k : Fin 5 => natCoeff (acquireChoose 4 5).coefficients k.val)
#check @acquiredParity
