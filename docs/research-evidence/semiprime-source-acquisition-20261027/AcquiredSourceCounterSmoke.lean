import RiemannGaussian.SemiprimeAcquiredSourceCounter
open RiemannGaussian SemiprimeLocalArrayFrontend SemiprimeAcquiredSourceCounter
private def arity (_ : Fin 1) : ℕ := 1
private def coordinate (_ : Fin 1) (_ : Fin 1) : Fin 1 := 0
private def run (T : (e : Fin 1) → (Fin (arity e) → Bool) → EntryReport) :=
  count (r := 1) (Q := 1) arity coordinate 1 0 1 1 T
#eval (run (fun _ a => ⟨if a ⟨0,by change 0<1; decide⟩ then 1 else 0,1,1⟩)).value
#eval (run (fun _ _ => ⟨1,1,1⟩)).value
#eval (run (fun _ _ => ⟨0,1,1⟩)).value
