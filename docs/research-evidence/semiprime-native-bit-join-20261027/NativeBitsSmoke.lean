import RiemannGaussian.SemiprimeNativeGroupBits
open RiemannGaussian
open SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits

def emptyGrouping : Fin 0 ≃ ((g : Fin 1) × Fin ((fun _ : Fin 1 => 0) g)) where
  toFun := Fin.elim0
  invFun := fun x => Fin.elim0 x.2
  left_inv := fun x => Fin.elim0 x
  right_inv := fun x => Fin.elim0 x.2

-- Actual physical two-branch tree with an empty source domain: the acquired port is zero.
#eval (let r := SemiprimeNativeLocalBits.run (n:=0) 2 1 2 0 SemiprimeJetBits.oneWord (fun _ v => Fin.elim0 v) (fun v => Fin.elim0 v) (fun v => Fin.elim0 v) (fun eta => ⟨⟨false,if eta 0 then [true] else []⟩,3⟩); (SemiprimeJetBits.decode r.words,r.words.size,r.clock))

-- Actual physical active constant factor, followed by the same-order group product.
#eval (let r := SemiprimeNativeGroupBits.run (n:=0) (F:=1) (r:=1) (h:=fun _ => 0) 2 (fun _ => 0) 2 0 SemiprimeJetBits.oneWord (fun _ i => Fin.elim0 i) emptyGrouping (fun _ => 0) (fun v => Fin.elim0 v) (fun _ _ => ⟨⟨false,[true]⟩,7⟩) 0 (fun _ v => Fin.elim0 v); (SemiprimeJetBits.decode r.words,r.words.size,r.clock))

-- Actual nonempty original source cache: one corrected half-valued port, table eta↦eta0.
#eval (let r := SemiprimeNativeLocalBits.run (n:=1) 3 1 2 0 SemiprimeJetBits.oneWord (fun _ _ => #[⟨⟨false,[true]⟩,[false,true]⟩]) (fun _ => true) (fun _ => true) (fun eta => ⟨⟨false,if eta 0 then [true] else []⟩,3⟩); (SemiprimeJetBits.decode r.words,r.words.size,r.clock))
