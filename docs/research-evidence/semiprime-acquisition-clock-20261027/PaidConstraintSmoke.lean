import RiemannGaussian.SemiprimePaidOriginalConstraints
set_option autoImplicit false
open RiemannGaussian
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

def onePort (R : Nat) : Nat × Nat × Nat × Bool :=
  let arity : Fin 1 → Nat := fun _ => 1
  let owner : ((e : Fin 1) × Fin (arity e)) → Fin 2 := fun _ => 0
  let en := SemiprimeFiniteEnumerations.indexed 2 1 2 1 arity
  let result := SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en 1 R
  let js := SemiprimeSourceConstraintAcquisition.rowIndices owner Sigma.fst en 1
  let ok := (List.finRange 1).all fun t => (List.finRange 2).all fun g =>
    (List.finRange js.values.length).all fun j => (List.finRange 2).all fun v =>
      decide ((SemiprimePaidOriginalConstraints.read result.value t.val g.val j.val v.val).value=
        SemiprimeSourceConstraintAcquisition.matrix owner Sigma.fst en 1 R t g j v)
  (result.value.indices.length,result.value.entries.length,result.work,ok)

#eval onePort 0
#eval onePort 4

def emptyPort : Nat × Nat × Nat :=
  let arity : Fin 0 → Nat := fun i => Fin.elim0 i
  let owner : ((e : Fin 0) × Fin (arity e)) → Fin 0 := fun i => Fin.elim0 i.1
  let en := SemiprimeFiniteEnumerations.indexed 0 0 1 0 arity
  let result := SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en 0 0
  (result.value.indices.length,result.value.entries.length,result.work)
#eval emptyPort
