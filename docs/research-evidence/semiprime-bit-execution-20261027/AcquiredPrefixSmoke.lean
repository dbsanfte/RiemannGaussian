import RiemannGaussian.SemiprimeAcquiredPrefixSearch
open RiemannGaussian SemiprimeAcquiredPrefixSearch SemiprimeMacroEntryBitPrimitives
set_option autoImplicit false
private def arity (_ : Fin 1) : ℕ := 1
private def coordinate (_ : Fin 1) (_ : Fin 1) : Fin 1 := 0
private def base (_ : Fin 1) (bits : Fin 1 → Bool) : CheckRun := ⟨bits 0,1⟩
private def count (fixed : List (Fin 1 × Bool)) :=
  prefixCount (r := 1) (Q := 1) arity coordinate 1 0 1 1 base fixed
#eval count []
#eval count [(0,false)]
#eval count [(0,true)]
#eval count [(0,false),(0,true)]
#eval let result := search (r := 1) (Q := 1) arity coordinate 1 0 1 1 base
      (result.values.map (List.map (fun p => (p.1.val,p.2))),result.queries)
#eval let result := search (r := 1) (Q := 1) arity coordinate 1 0 1 1 (fun _ _ => ⟨true,1⟩)
      (result.values.map (List.map (fun p => (p.1.val,p.2))),result.queries)
#eval let result := search (r := 1) (Q := 1) arity coordinate 1 0 1 1 (fun _ _ => ⟨false,1⟩)
      (result.values.map (List.map (fun p => (p.1.val,p.2))),result.queries)
