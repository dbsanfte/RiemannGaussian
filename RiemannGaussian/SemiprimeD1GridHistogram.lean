/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GridResidue
import RiemannGaussian.SemiprimeD1JetRecoveryScalarHeight

/-! # Actual complete-grid translation and valuation histograms for D.10 -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GridHistogram
open scoped BigOperators
open SemiprimeD1GridValuation SemiprimeD1GridResidue SemiprimeD1WireKernelOriginal
  SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryScalarHeight

/-- Actual nonzero canonical residue level, not an advised cardinality. -/
def residueLevel (k v : ℕ) : Finset (ZMod (2^k)) :=
  Finset.univ.filter (fun x => x≠0 ∧ order k x=v)

/-- Exact residue-level cardinality from literal odd-multiple acquisition. -/
theorem residueLevel_card (k v : ℕ) (hv : v<k) :
    (residueLevel k v).card=2^(k-v-1) := by
  rw [← level_card k v hv]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨_,hxn,hv⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.val_lt,?_,hv⟩
    intro h0
    exact hxn ((ZMod.val_eq_zero x).mp h0)
  · intro x _ y _ he
    exact ZMod.val_injective _ he
  · intro q hq
    obtain ⟨hq,hqn,hv⟩ := Finset.mem_filter.mp hq
    have hqr := Finset.mem_range.mp hq
    have hval : (q:ZMod (2^k)).val=q := by rw [ZMod.val_natCast,Nat.mod_eq_of_lt hqr]
    refine ⟨(q:ZMod (2^k)),?_,hval⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro h0
      have := congrArg ZMod.val h0
      simp only [hval,ZMod.val_zero] at this
      exact hqn this
    · simpa only [order,hval] using hv

/-- Exact canonical finite-index/residue equivalence, supplied by explicit val/cast. -/
def indexEquiv (k : ℕ) : Fin (2^k) ≃ ZMod (2^k) where
  toFun q := (q.val:ZMod (2^k))
  invFun x := ⟨x.val,x.val_lt⟩
  left_inv q := by apply Fin.ext;simp only [ZMod.val_natCast,Nat.mod_eq_of_lt q.isLt]
  right_inv x := by simp only [ZMod.natCast_zmod_val]

/-- Original centered signed-grid translation into its complete residue system. -/
def gridEquiv (a : ℕ) : Fin (size a) ≃ ZMod (2^(a+1)) :=
  (indexEquiv (a+1)).trans (Equiv.addRight (-(center a:ZMod (2^(a+1)))))

/-- The concrete translation is exactly the ORIGINAL signed point, not a new grid. -/
theorem gridEquiv_apply (a : ℕ) (q : Fin (size a)) :
    gridEquiv a q=(point a q.val:ZMod (2^(a+1))) := by
  change (q.val:ZMod (2^(a+1)))+ -(center a:ZMod (2^(a+1)))=(point a q.val:ZMod (2^(a+1)))
  simp only [point,sub_eq_add_neg,Int.cast_add,Int.cast_neg,Int.cast_natCast]

/-- A bounded signed integer and its actual modular image have identical order. -/
theorem order_intCast (k : ℕ) (x : ℤ) (hx : x≠0) (hb : x.natAbs<2^k) :
    order k (x:ZMod (2^k))=padicValInt 2 x := by
  rw [← order_val,ZMod.val_intCast]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using (remainder_valuation k x hx hb).2

/-- Original nonzero grid points have their exact order in the translated residue grid. -/
theorem original_order (a : ℕ) (q : Fin (size a)) (hq : q.val≠center a) :
    order (a+1) (gridEquiv a q)=padicValInt 2 (point a q.val) := by
  rw [gridEquiv_apply]
  exact order_intCast _ _ ((not_congr (point_zero_iff a q.val)).mpr hq)
    (point_abs_lt a q.val q.isLt)

/-- The actual zero node is mapped to the actual zero residue. -/
theorem gridEquiv_zero_iff (a : ℕ) (q : Fin (size a)) : gridEquiv a q=0 ↔ q.val=center a := by
  have he : gridEquiv a ⟨center a,center_lt a⟩=0 := by rw [gridEquiv_apply];simp [point]
  constructor
  · intro h
    have := (gridEquiv a).injective (h.trans he.symm)
    exact congrArg Fin.val this
  · intro h
    have : q=⟨center a,center_lt a⟩ := Fin.ext h
    rw [this,he]

/-- Exact order of the original difference at every surviving original pair. -/
theorem original_difference_order (a : ℕ) (t q : Fin (size a)) (hne : q≠t) :
    order (a+1) (gridEquiv a t-gridEquiv a q)=
      padicValInt 2 (point a t.val-point a q.val) := by
  rw [gridEquiv_apply,gridEquiv_apply,← Int.cast_sub]
  apply order_intCast
  · exact point_sub_ne_zero a t.val q.val (fun h => hne (Fin.ext h))
  · have he : point a t.val-point a q.val=
        SemiprimeD1WireKernelFactors.difference t.val q.val := by unfold point SemiprimeD1WireKernelFactors.difference;ring
    rw [he]
    exact SemiprimeD1WireKernelFactors.difference_abs_lt (size a) t.val q.val t.isLt q.isLt

/-- The translated own/zero-node exclusions are EXACTLY the original excluded indices. -/
theorem original_membership (a : ℕ) (t q : Fin (size a)) :
    q.val∈others a t.val ↔ gridEquiv a q≠0 ∧ gridEquiv a q≠gridEquiv a t := by
  simp only [others,Finset.mem_erase,Finset.mem_range,q.isLt,and_true,
    ne_eq,gridEquiv_zero_iff,Equiv.apply_eq_iff_eq,Fin.ext_iff]
  tauto

end RiemannGaussian.SemiprimeD1GridHistogram
