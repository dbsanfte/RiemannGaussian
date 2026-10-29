/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorNetwork
import RiemannGaussian.SemiprimeStreamingTensor

/-! # Exact multilinear factorization along an actual variable partition
The product identity requires a partition of the variable occurrences. It is
not asserted for overlapping tensor scopes. Empty fibres retain their scalar
tensors, which is essential for isolated vertices in group children.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1PartitionedTensor
open scoped BigOperators
variable {I G R : Type*} [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] [CommRing R]

/-- Assignments regroup by the literal unique owner of each variable. -/
def assignments (group : I → G) : (I → Bool) ≃ ((g : G) → {i // group i = g} → Bool) where
  toFun bits _ i := bits i.val
  invFun bits i := bits (group i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv bits := by
    funext g i
    rcases i with ⟨i, hi⟩
    subst g
    rfl

/-- Finite multilinear extension, over any finite occurrence set and any ring. -/
noncomputable def evaluate (T : (I → Bool) → R) (x : I → R) : R :=
  ∑ bits : I → Bool, T bits * ∏ i, if bits i then x i else 1-x i

/-- The ordinary recursive extension is precisely this finite formula. -/
theorem evaluate_fin (n : ℕ) (T : (Fin n → Bool) → R) (x : Fin n → R) :
    SemiprimeStreamingTensor.evaluate n T x = evaluate T x := by
  exact SemiprimeStreamingTensor.evaluate_eq_sum n T x

omit [DecidableEq I] in
/-- A variable weight product splits according to its unique actual group. -/
theorem product_fibres (group : I → G) (f : I → R) :
    (∏ i, f i) = ∏ g, ∏ i : {i // group i = g}, f i.val := by
  classical
  have h := (Equiv.sigmaFiberEquiv group).prod_comp f
  simpa only [Fintype.prod_sigma, Equiv.sigmaFiberEquiv_apply] using h.symm

/-- The multilinear extension of a product over DISJOINT scopes is exactly the
product of local extensions, including all empty-scope tensor factors. -/
theorem evaluate_product (group : I → G)
    (T : (g : G) → ({i // group i = g} → Bool) → R) (x : I → R) :
    evaluate (fun bits => ∏ g, T g (fun i => bits i.val)) x =
      ∏ g, evaluate (T g) (fun i : {i // group i = g} => x i.val) := by
  classical
  unfold evaluate
  rw [← (assignments group).symm.sum_comp]
  change (∑ bits : (g : G) → {i // group i = g} → Bool,
    (∏ g, T g (fun i => bits (group i.val) ⟨i.val, rfl⟩)) *
      (∏ i, if bits (group i) ⟨i, rfl⟩ then x i else 1-x i)) = _
  have hlocal (bits : (g : G) → {i // group i = g} → Bool) :
      (∏ g, T g (fun i => bits (group i.val) ⟨i.val, rfl⟩)) *
        (∏ i, if bits (group i) ⟨i, rfl⟩ then x i else 1-x i) =
      ∏ g, T g (bits g) *
        ∏ i : {i // group i = g}, if bits g i then x i.val else 1-x i.val := by
    have hbits (g : G) :
        (fun i : {i // group i = g} => bits (group i.val) ⟨i.val, rfl⟩) = bits g := by
      funext i
      rcases i with ⟨i, hi⟩
      subst g
      rfl
    simp only [hbits]
    rw [product_fibres group]
    have hweight (g : G) :
        (∏ i : {i // group i = g}, if bits (group i.val) ⟨i.val, rfl⟩ then x i.val else 1-x i.val) =
        ∏ i : {i // group i = g}, if bits g i then x i.val else 1-x i.val := by
      apply Finset.prod_congr rfl
      intro i _
      rcases i with ⟨i, hi⟩
      subst g
      rfl
    simp only [hweight, Finset.prod_mul_distrib]
  simp_rw [hlocal]
  exact (Fintype.prod_sum (fun g bits => T g bits *
    ∏ i : {i // group i = g}, if bits i then x i.val else 1-x i.val)).symm

end RiemannGaussian.SemiprimeD1PartitionedTensor
