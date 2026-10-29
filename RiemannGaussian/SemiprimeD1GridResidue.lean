/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GridValuation

/-! # Exact valuation and finite translation on the original complete residue grid -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GridResidue
open scoped BigOperators
open SemiprimeD1GridValuation SemiprimeD1WireKernelFactors

/-- Canonical residue-grid order; zero is always explicitly excluded in applications. -/
def order (k : ℕ) (x : ZMod (2^k)) : ℕ := padicValNat 2 x.val

/-- A nonzero canonical residue has nonzero original integer representative. -/
theorem val_ne_zero (k : ℕ) (x : ZMod (2^k)) (hx : x≠0) : (x.val:ℤ)≠0 := by
  have h : x.val≠0 := by intro h;apply hx;exact (ZMod.val_eq_zero x).mp h
  exact_mod_cast h

/-- Original integer representatives have exactly the stored residue valuation. -/
theorem order_val (k : ℕ) (x : ZMod (2^k)) : padicValInt 2 (x.val:ℤ)=order k x := by
  simp only [padicValInt.of_nat,order]

/-- Every nonzero residue order is below the grid exponent. -/
theorem order_lt (k : ℕ) (x : ZMod (2^k)) (hx : x≠0) : order k x<k := by
  have hn : x.val≠0 := by intro h;apply hx;exact (ZMod.val_eq_zero x).mp h
  have hp : 2^padicValNat 2 x.val≤x.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp (hp.trans_lt x.val_lt)

/-- Distinct residues give a genuine bounded integer difference. -/
theorem difference_ne_zero (k : ℕ) (x y : ZMod (2^k)) (hxy : x≠y) :
    (x.val:ℤ)-(y.val:ℤ)≠0 := by
  intro h
  apply hxy
  apply ZMod.val_injective
  omega

/-- Original bounded integer difference and canonical residue subtraction have SAME order. -/
theorem order_sub (k : ℕ) (x y : ZMod (2^k)) (hxy : x≠y) :
    order k (x-y)=padicValInt 2 ((x.val:ℤ)-(y.val:ℤ)) := by
  have hn := difference_ne_zero k x y hxy
  have hb : ((x.val:ℤ)-(y.val:ℤ)).natAbs<2^k :=
    difference_abs_lt (2^k) x.val y.val x.val_lt y.val_lt
  have hmod : (2:ℤ)^k∣((x.val:ℤ)-(y.val:ℤ))-((x-y).val:ℤ) := by
    have h : ((2^k:ℕ):ℤ)∣((x.val:ℤ)-(y.val:ℤ))-((x-y).val:ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2^k)).mp
      simp only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,sub_self]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
  simpa only [order_val] using (valuation_congruent k _ _ hn (valuation_lt k _ hn hb) hmod).2

/-- Exact nonarchimedean equality for distinct original integer orders. -/
theorem int_sub_order_of_lt (x y : ℤ) (hx : x≠0)
    (h : padicValInt 2 x<padicValInt 2 y) :
    x-y≠0 ∧ padicValInt 2 (x-y)=padicValInt 2 x := by
  apply valuation_congruent (padicValInt 2 x+1) x (x-y) hx (by omega)
  have hd : (2:ℤ)^(padicValInt 2 x+1)∣y :=
    (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr (by omega))
  convert hd using 1;ring

/-- Residue subtraction orders are the minimum when the original orders differ. -/
theorem order_sub_of_ne (k : ℕ) (x y : ZMod (2^k)) (hx : x≠0) (hy : y≠0)
    (h : order k x≠order k y) : order k (x-y)=min (order k x) (order k y) := by
  have hxy : x≠y := by intro he;subst y;exact h rfl
  rw [order_sub k x y hxy]
  rcases lt_or_gt_of_ne h with hlt|hgt
  · have h := (int_sub_order_of_lt (x.val:ℤ) (y.val:ℤ) (val_ne_zero k x hx)
      (by simpa only [order_val] using hlt)).2
    simpa only [order_val,Nat.min_eq_left hlt.le] using h
  · have h := (int_sub_order_of_lt (y.val:ℤ) (x.val:ℤ) (val_ne_zero k y hy)
      (by simpa only [order_val] using hgt)).2
    have he : (y.val:ℤ)-(x.val:ℤ)=-((x.val:ℤ)-(y.val:ℤ)) := by ring
    rw [he] at h
    simp only [padicValInt,Int.natAbs_neg] at h
    change padicValInt 2 ((x.val:ℤ)-(y.val:ℤ))=padicValInt 2 (y.val:ℤ) at h
    simpa only [order_val,Nat.min_eq_right hgt.le] using h

/-- The minimum-order lower bound also covers equal orders, without assuming a domain. -/
theorem order_sub_lower (k : ℕ) (x y : ZMod (2^k))
    (hxy : x≠y) : min (order k x) (order k y)≤order k (x-y) := by
  rw [order_sub k x y hxy]
  have hdx : (2:ℤ)^min (order k x) (order k y)∣(x.val:ℤ) := by
    apply (padicValInt_dvd_iff (p:=2) _ _).mpr
    exact Or.inr (by rw [order_val];exact Nat.min_le_left _ _)
  have hdy : (2:ℤ)^min (order k x) (order k y)∣(y.val:ℤ) := by
    apply (padicValInt_dvd_iff (p:=2) _ _).mpr
    exact Or.inr (by rw [order_val];exact Nat.min_le_right _ _)
  exact ((padicValInt_dvd_iff (p:=2) _ _).mp (dvd_sub hdx hdy)).resolve_left
    (difference_ne_zero k x y hxy)

/-- Literal modular translation q↦t-q, with no lookup or cardinality advice. -/
def reflect (k : ℕ) (t : ZMod (2^k)) : Equiv.Perm (ZMod (2^k)) := Equiv.subLeft t

/-- Original exclusion of the zero and own node is preserved by reflection. -/
theorem reflect_membership (k : ℕ) (t x : ZMod (2^k)) :
    (x≠0 ∧ x≠t) ↔ (t-x≠0 ∧ t-x≠t) := by
  constructor
  · rintro ⟨h0,ht⟩
    constructor
    · exact sub_ne_zero.mpr (Ne.symm ht)
    · intro h;apply h0;linear_combination -h
  · rintro ⟨h0,ht⟩
    constructor
    · intro h;apply ht;rw [h,sub_zero]
    · intro h;apply h0;rw [h,sub_self]

end RiemannGaussian.SemiprimeD1GridResidue
