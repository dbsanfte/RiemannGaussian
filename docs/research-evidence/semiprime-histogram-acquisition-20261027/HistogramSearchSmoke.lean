import RiemannGaussian.SemiprimeSourceHistogramSearch
set_option autoImplicit false
open RiemannGaussian SemiprimeBitArithmetic

def tieArity (_ : Fin 1) : ℕ := 1

def tieOwner (i : (e : Fin 1)×Fin (tieArity e)) : Fin 1 := i.2

def splitArity (_ : Fin 1) : ℕ := 2

def splitOwner (i : (e : Fin 1)×Fin (splitArity e)) : Fin 2 := i.2

#eval let out := SemiprimeSourceHistogramSearch.run 1 1 2 1 1 tieArity tieOwner
      (out.value.map bitValue,out.work)

#eval let out := SemiprimeSourceHistogramSearch.run 2 1 2 1 1 splitArity splitOwner
      (out.value.map bitValue,out.work)

#eval let out := SemiprimeSourceHistogramSearch.run 2 1 2 0 1 splitArity splitOwner
      (out.value.map bitValue,out.work)
