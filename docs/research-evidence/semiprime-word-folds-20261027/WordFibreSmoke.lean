import RiemannGaussian.SemiprimeMaterializedWordFibre
open RiemannGaussian
open SemiprimeRationalBits SemiprimeJetBits SemiprimeNodeArrayExecution

def oneGrouping : Fin 1 ≃ ((g : Fin 1) × Fin ((fun _ : Fin 1 => 1) g)) where
  toFun := fun i => ⟨0,i⟩
  invFun := fun x => x.2
  left_inv := fun _ => rfl
  right_inv := by
    intro x
    rcases x with ⟨g,i⟩
    have hg : g=0 := Subsingleton.elim _ _
    subst g
    rfl

def smokeDesign : RuntimeDesign 1 0 where
  r := 1
  h := fun _ => 1
  m := fun _ => 1
  W := fun _ => 1
  grouping := oneGrouping
  assigned := Fin.elim0
  C := fun _ _ _ => 0

def smokeGroup (U : Finset (Fin 1)) (g : Fin 1) (a : (k : Fin 1) → Fin (smokeDesign.h k) → Bool) : JetReport :=
  SemiprimeNativeGroupBits.run (n:=1) (F:=0) (r:=1) (h:=fun _ => 1) 2 (fun e => Fin.elim0 e) 2 0 SemiprimeJetBits.oneWord (fun e => Fin.elim0 e) oneGrouping Fin.elim0 (fun v => decide (v∈U)) (fun e => Fin.elim0 e) g a

-- Three actual summary bins (two empty), both local head words, and all three signed supports.
#eval (let width := SemiprimeWordPacketWidth.packetWidth 2 0 1 0 0 2 1 2 3 3; let out := SemiprimeMaterializedWordFibre.node (List.replicate width false) 2 smokeDesign smokeGroup; (decode out.words,out.words.size,out.clock))
