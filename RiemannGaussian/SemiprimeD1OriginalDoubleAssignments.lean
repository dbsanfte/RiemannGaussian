/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketAssignmentRows

/-! # Original X/Y assignments biject with the actual two-sided incidence tags
The correspondence uses the acquired original placement order. Together with
the computed child pullbacks it turns the original double assignment sum into
independent sums on the actual child scopes, without a projection oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeD1OriginalDoubleAssignments
open scoped BigOperators
open SemiprimeD1OriginalIncidenceIndex SemiprimeD1PacketAssignmentRows
open SemiprimeD1ChildAssignmentEquiv
noncomputable section

/-- Original Boolean assignments on the actual acquired occurrence stream. -/
abbrev Bits (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :=
  Fin (SemiprimeD1PacketReplayOriginal.acquire n F r a arity owner).placements.length → Bool

/-- The inverse reads the computed position inverse and preserves both sides;
it does not select or solve any Boolean assignment. -/
def doubleAssignments (n F r a : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (Bits n F r a arity owner × Bits n F r a arity owner) ≃ (Tag arity → Bool) where
  toFun xy := tagBits n F r a arity owner xy.1 xy.2
  invFun bits :=
    (fun j => bits ((position n F r a arity owner).symm j,false),
     fun j => bits ((position n F r a arity owner).symm j,true))
  left_inv xy := by
    apply Prod.ext <;> funext j
    · simp only [tagBits,Bool.false_eq_true,ite_false,Equiv.apply_symm_apply]
    · simp only [tagBits,ite_true,Equiv.apply_symm_apply]
  right_inv bits := by
    funext tag
    rcases tag with ⟨port,side⟩
    cases side <;> simp only [tagBits,Bool.false_eq_true,ite_false,ite_true,
      Equiv.symm_apply_apply]

/-- The original two assignment sums are exactly one sum over original tags,
including the empty-incidence case. -/
theorem sum_original {R : Type*} [AddCommMonoid R] (n F r a : ℕ)
    (arity : Fin F → ℕ) (owner : ((e : Fin F) × Fin (arity e)) → Fin n)
    (term : (Tag arity → Bool) → R) :
    (∑ x : Bits n F r a arity owner,∑ y : Bits n F r a arity owner,
      term (tagBits n F r a arity owner x y)) = ∑ bits : Tag arity → Bool, term bits := by
  classical
  have h := (doubleAssignments n F r a arity owner).sum_comp term
  change (∑ xy : Bits n F r a arity owner × Bits n F r a arity owner,
    term (tagBits n F r a arity owner xy.1 xy.2)) = _ at h
  simpa only [Fintype.sum_prod_type] using h

/-- Applying the actual cached colour partition to the original X/Y sum
gives independent contractions on the actual acquired child scopes. -/
theorem sum_child_products {R : Type*} [CommRing R] (n F r a : ℕ) [NeZero r]
    (arity : Fin F → ℕ) (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (term : (g : Fin r) → (Fin (scope n F r a arity owner i g) → Bool) → R) :
    (∑ x : Bits n F r a arity owner,∑ y : Bits n F r a arity owner,
      ∏ g : Fin r,term g (assignments n F r a arity owner i
        (tagBits n F r a arity owner x y) g)) =
      ∏ g : Fin r,∑ bits : Fin (scope n F r a arity owner i g) → Bool,term g bits := by
  exact (sum_original n F r a arity owner (fun bits =>
    ∏ g,term g (assignments n F r a arity owner i bits g))).trans
      (sum_product n F r a arity owner i term)

end
end RiemannGaussian.SemiprimeD1OriginalDoubleAssignments
