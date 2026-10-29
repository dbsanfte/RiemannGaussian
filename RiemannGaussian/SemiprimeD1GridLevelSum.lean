/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GridRawSum
import RiemannGaussian.SemiprimeD1InvolutionRegroup

/-! # Actual D.10 complete-grid regrouping and tapered precision loss -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1GridLevelSum
open scoped BigOperators
open SemiprimeD1GridValuation SemiprimeD1GridResidue SemiprimeD1GridHistogram
  SemiprimeD1GridRawSum SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
  SemiprimeD1JetRecoveryGrid

/-- Regrouping uses the actual finite reflection, not a supplied valuation histogram. -/
theorem residue_regroup (k h u : ℕ) (t : ZMod (2^k)) (ht : t≠0) :
    residueValuation k h u t=
      ∑ x∈residueOthers k t,if order k t<order k x then
        ((multiplicity h u (order k x):ℤ)-(multiplicity h u (order k t):ℤ))*
          ((order k x:ℤ)-(order k t:ℤ)) else 0 := by
  unfold residueValuation
  apply SemiprimeD1InvolutionRegroup.regroup (residueOthers k t) (fun x => t-x) (order k)
    (fun v => (multiplicity h u v:ℤ)) (order k t)
  · intro x hx
    exact (residue_reflect k t x).mp hx
  · intro x _
    simp
  · intro x hx hl
    have hxn := ((residue_membership k t x).mp hx).1
    have hneq : order k t≠order k x := by omega
    rw [order_sub_of_ne k t x ht hxn hneq]
    exact Nat.min_eq_right hl.le
  · intro x hx hh
    have hxn := ((residue_membership k t x).mp hx).1
    have hneq : order k t≠order k x := by omega
    rw [order_sub_of_ne k t x ht hxn hneq]
    exact Nat.min_eq_left hh.le

/-- Exact summation over actual high residue levels, counting each literal grid value. -/
theorem high_level_sum (k i : ℕ) (t : ZMod (2^k)) (ht : t≠0)
    (hi : order k t=i) (f : ℕ→ℤ) :
    (∑ x∈residueOthers k t,if i<order k x then f (order k x) else 0)=
      ∑ v∈Finset.range k,if i<v then (2^(k-v-1):ℤ)*f v else 0 := by
  let S : Finset (ZMod (2^k)) := Finset.univ.erase 0
  let g := fun x : ZMod (2^k) => if i<order k x then f (order k x) else 0
  have hmem : t∈S := Finset.mem_erase.mpr ⟨ht,Finset.mem_univ _⟩
  have he := Finset.sum_erase_add S g hmem
  have hgt : g t=0 := by simp only [g,hi,lt_self_iff_false,ite_false]
  rw [hgt,add_zero] at he
  change (∑ x∈S.erase t,g x)=_
  rw [he]
  have hm : ∀ x∈S,order k x∈Finset.range k := by
    intro x hx
    exact Finset.mem_range.mpr (order_lt k x (Finset.mem_erase.mp hx).1)
  rw [← Finset.sum_fiberwise_of_maps_to hm g]
  apply Finset.sum_congr rfl
  intro v hv
  have hvk := Finset.mem_range.mp hv
  have hset : S.filter (fun x => order k x=v)=residueLevel k v := by
    ext x
    simp [S,residueLevel]
  rw [hset]
  have hg : (∑ x∈residueLevel k v,g x)=
      ∑ _x∈residueLevel k v,if i<v then f v else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨_,_,hxv⟩ := Finset.mem_filter.mp hx
    simp only [g,hxv]
  rw [hg,Finset.sum_const,nsmul_eq_mul,residueLevel_card k v hvk]
  by_cases hiv : i<v <;> simp only [hiv,ite_true,ite_false,mul_zero]
  rfl

/-- The actual high-level count sum is the original D.10 level expression. -/
theorem levels_eq_taper (a h u i : ℕ) (hi : i≤a) :
    (∑ v∈Finset.range (a+1),if i<v then (2^(a+1-v-1):ℤ)*
      (((multiplicity h u v:ℤ)-(multiplicity h u i:ℤ))*((v:ℤ)-(i:ℤ))) else 0)=
      levelValuation h u i (a-i) := by
  rw [← Finset.sum_filter]
  have hs : (Finset.range (a+1)).filter (fun v => i<v)=Finset.Ico (i+1) (a+1) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [hs,Finset.sum_Ico_eq_sum_range]
  have he : a+1-(i+1)=a-i := by omega
  rw [he]
  unfold levelValuation
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  have hex : a+1-(i+1+j)-1=(a-i)-(j+1) := by omega
  have hidx : i+1+j=i+(j+1) := by omega
  rw [hex,hidx]
  push_cast
  ring

/-- Complete actual D.10 identity for the original signed grid and taper. -/
theorem original_D10 (a h u : ℕ) (t : Fin (size a)) (ht : point a t.val≠0) :
    padicValRat 2 (Ezero a h u t.val)=
      levelValuation h u (padicValInt 2 (point a t.val))
        (a-padicValInt 2 (point a t.val)) := by
  have htc : t.val≠center a := (not_congr (point_zero_iff a t.val)).mp ht
  have hz : gridEquiv a t≠0 := by intro he;exact htc ((gridEquiv_zero_iff a t).mp he)
  have ho := original_order a t htc
  have hil : padicValInt 2 (point a t.val)≤a := by
    have h := order_lt (a+1) (gridEquiv a t) hz
    rw [ho] at h
    omega
  rw [Ezero_valuation,original_raw_sum,residue_regroup (a+1) h u _ hz]
  rw [high_level_sum (a+1) (order (a+1) (gridEquiv a t)) (gridEquiv a t) hz rfl
    (fun v => ((multiplicity h u v:ℤ)-(multiplicity h u (order (a+1) (gridEquiv a t)):ℤ))*
      ((v:ℤ)-(order (a+1) (gridEquiv a t):ℤ)))]
  rw [ho]
  exact levels_eq_taper a h u _ hil

/-- Original tapered precision-loss bound, with NO valuation/precision advice. -/
theorem original_D10_lower (a M u : ℕ) (t : Fin (size a)) (ht : point a t.val≠0) :
    -(6:ℤ)*(2:ℤ)^(a-padicValInt 2 (point a t.val))*(height M u:ℤ)≤
      padicValRat 2 (Ezero a (height M u) u t.val) := by
  rw [original_D10 a (height M u) u t ht]
  exact levelValuation_lower _ _ _ _

end RiemannGaussian.SemiprimeD1GridLevelSum
