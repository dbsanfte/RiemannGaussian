import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Prod

/-! # Rational outputs of an operator on a finitely generated lattice -/

namespace RiemannGaussian.AlpogeLattice

/-- An operator on the ambient space can have outputs back in the embedded
space. On a finitely generated input lattice all these outputs lie in a
finitely generated module over the original Noetherian ring. -/
theorem rational_outputs_fg {R K E V W : Type*} [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [Field E] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [AddCommGroup W] [Module E W] {σ : K →+* E}
    (emb : V →ₛₗ[σ] W) (hinj : Function.Injective emb) (op : W →ₗ[E] W)
    (A : Submodule R V) (hA : A.FG) :
    ∃ N : Submodule R V, N.FG ∧ ∀ x ∈ A, ∀ y, emb y = op (emb x) → y ∈ N := by
  let graph : Submodule R (V × V) :=
    { carrier := {p | p.1 ∈ A ∧ emb p.2 = op (emb p.1)}
      zero_mem' := ⟨A.zero_mem, by simp⟩
      add_mem' := fun hx hy => ⟨A.add_mem hx.1 hy.1, by
        simpa only [Prod.fst_add, Prod.snd_add, map_add] using congrArg₂ (· + ·) hx.2 hy.2⟩
      smul_mem' := fun r p hp => ⟨A.smul_mem r hp.1, by
        change emb (r • p.2) = op (emb (r • p.1))
        rw [← algebraMap_smul K r p.1, ← algebraMap_smul K r p.2,
          LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hp.2]⟩ }
  let first : graph →ₗ[R] A :=
    ((LinearMap.fst R V V).comp graph.subtype).codRestrict A fun p => p.property.1
  have hfirst : Function.Injective first := by
    intro p q hpq
    have h₁ : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    exact Prod.ext h₁ (hinj (p.property.2.trans ((congrArg (fun x => op (emb x)) h₁).trans q.property.2.symm)))
  have : Module.Finite R A := Module.Finite.iff_fg.2 hA
  have : IsNoetherian R graph := isNoetherian_of_injective first hfirst
  let second := (LinearMap.snd R V V).comp graph.subtype
  exact ⟨second.range, Submodule.fg_range second, fun x hx y hxy => ⟨⟨(x,y), hx, hxy⟩, rfl⟩⟩

end RiemannGaussian.AlpogeLattice

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeLattice.rational_outputs_fg
  for ax in ← collectAxioms decl do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
