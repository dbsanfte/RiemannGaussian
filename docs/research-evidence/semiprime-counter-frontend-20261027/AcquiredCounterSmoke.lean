import RiemannGaussian.SemiprimeNodeArrayExecution
open RiemannGaussian
open Polynomial SemiprimeIndexedNodeCertificate SemiprimeLocalArrayFrontend
private def partition : Fin 1 ≃ ((_g : Fin 1) × Fin 1) where
  toFun v := ⟨0,v⟩
  invFun v := v.2
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨g,v⟩
    have h : g=0 := Subsingleton.elim _ _
    subst g
    rfl
private def arity (_ : Fin 1) : ℕ := 1
private def design : SemiprimeNodeArrayExecution.RuntimeDesign 1 1 where
  r := 1
  h := fun _ => 1
  m := fun _ => 0
  W := fun _ => 0
  grouping := partition
  assigned := fun _ => 0
  C := fun _ j => Fin.elim0 j
private def truth (_ : Fin 1) (a : Fin 1 → Bool) : EntryReport :=
  ⟨if a 0 then 1 else 0,1,1⟩
private def run (T : (e : Fin 1) → (Fin (arity e) → Bool) → EntryReport) :=
  SemiprimeNodeArrayExecution.count 2 2 0 (fun _ => design)
    (fun _ _ _ => #[1]) T
#eval ((run truth).value,(run truth).work)
#eval (run (fun _ _ => ⟨1,1,1⟩)).value
#eval (run (fun _ _ => ⟨0,1,1⟩)).value
