import Formalism.LocalToGlobal.HermitianForms.FormsTied

/-! # Projecting an adelic form to a double class -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical

/-- Cutting an adelic form down to one double class preserves its transformation
law. Only injectivity of the class labels is needed to read off its restrictions. -/
theorem single_mem_form_classes {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad)
    {ι : Type} [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n)
    {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective fun c => (Quotient.mk'' (yc c) : Cls S))
    (c : C) {φ : C → Frames (gramC J emb) → ℂ} (hφ : φ ∈ FiC S emb lam yc) :
    Pi.single c (φ c) ∈ FiC S emb lam yc := by
  classical
  obtain ⟨g, hg, rfl⟩ := hφ
  let cl := fun x => (Quotient.mk'' x : Cls S)
  let cut := fun x => if cl x = cl (yc c) then g x else 0
  refine ⟨cut, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ x x' κ he y y' hy
    let k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.val, ((S.U_eq κ.val).1 κ.2).1⟩
    let a := x' * k⁻¹ * x⁻¹
    have ha : a.val = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ := by
      simp only [a, k, Subgroup.coe_inv, Subgroup.coe_mul, he]
      group
    have hcl : cl x = cl x' := by
      apply (DoubleCoset.eq _ _ x x').2
      exact ⟨a, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, ha.symm⟩),
        k, κ.2, by dsimp [a]; group⟩
    by_cases hx : cl x = cl (yc c)
    · simpa only [cut, ← hcl, if_pos hx] using hg.1 γ hγ x x' κ he y y' hy
    · simp only [cut, ← hcl, if_neg hx, Pi.zero_apply, mul_zero]
  · apply Submodule.mem_pi.2
    intro x _
    dsimp only [cut]
    split
    · exact Submodule.mem_pi.1 hg.2 x (Set.mem_univ x)
    · exact Submodule.zero_mem _
  · funext b
    change cut (yc b) = (Pi.single c (g (yc c)) : C → Frames (gramC J emb) → ℂ) b
    by_cases hb : b = c
    · subst b
      simp [cut]
    · simp [cut, show cl (yc b) ≠ cl (yc c) from fun h => hb (hinj h), Pi.single_eq_of_ne hb]

/-- The level-zero value tie alone supplies the class projections in the rank
and frame estimates, including at classes with nontrivial stabilizers. -/
theorem single_mem_unramified_forms {D : D7} {u : D.what₂.Word}
    {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (c : (D.mem u).C.cls 0) (φ : (D.mem u).A.Mu0) :
    Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0 := by
  classical
  apply (Mu0_iff W _).2
  have h := single_mem_form_classes K.lev (embT D) ((D.fm u).lam 0) K.y K.y_bij.1 c
    ((Mu0_iff W _).1 φ.property)
  convert h using 1
  funext b z
  by_cases hb : b = c
  · subst b
    simp
  · simp [Pi.single_eq_of_ne hb]

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.single_mem_unramified_forms
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
