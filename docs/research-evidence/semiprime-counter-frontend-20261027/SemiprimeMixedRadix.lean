/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFiniteEnumerations

/-! # List-free mixed-radix summary codes and explicit filtered fibres -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeMixedRadix
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

/-- Decode a finite product code using div/mod through `finProdFinEquiv`.
The definition constructs no list of codes or assignments. Zero radices are allowed. -/
def decode : (n : ℕ) → (bounds : Fin n → ℕ) →
    Fin (∏ i, bounds i) ≃ ((i : Fin n) → Fin (bounds i))
  | 0, bounds => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ⟨0, by simp⟩
      left_inv := by intro i; apply Fin.ext; have hi := i.isLt; simp at hi; simp only; omega
      right_inv := by intro x; funext i; exact Fin.elim0 i }
  | n+1, bounds =>
      (finCongr (Fin.prod_univ_succ bounds)).trans
        (finProdFinEquiv.symm.trans
          ((Equiv.prodCongr (Equiv.refl _) (decode n (fun i => bounds i.succ))).trans
            (Fin.consEquiv (fun i => Fin (bounds i)))))

/-- Two nested finite summary boxes, still without listing either box. -/
def nested (groups : ℕ) (rows : Fin groups → ℕ)
    (radius : (g : Fin groups) → Fin (rows g) → ℕ) :
    Fin (∏ g, ∏ j, radius g j) ≃ ((g : Fin groups) → (j : Fin (rows g)) → Fin (radius g j)) :=
  (decode groups (fun g => ∏ j, radius g j)).trans
    (Equiv.piCongrRight (fun g => decode (rows g) (radius g)))

/-- Exact forward/backward round trip of the executable summary code. -/
theorem decode_roundtrip (n : ℕ) (bounds : Fin n → ℕ) (i : Fin (∏ j, bounds j)) :
    (decode n bounds).symm (decode n bounds i)=i := (decode n bounds).symm_apply_apply i

/-- Filtered fibres retain the supplied vertex order; inverse lookup is `List.idxOf`. -/
def filtered {A : Type*} [DecidableEq A] (en : FiniteEnumeration A)
    (p : A → Prop) [DecidablePred p] :
    Fin (en.values.filter (fun x => decide (p x))).length ≃ {x // p x} :=
  listSubtypeEquiv _ (en.nodup.filter _) p (by intro x; simp [en.complete x])

#print axioms decode_roundtrip
end RiemannGaussian.SemiprimeMixedRadix
