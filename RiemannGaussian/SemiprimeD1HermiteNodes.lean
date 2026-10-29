/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteIdentity
import RiemannGaussian.SemiprimeD1GridLevelSum

/-! # Actual distinct signed tapered nodes and the original degree sufficiency -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteNodes
open scoped BigOperators
open Polynomial SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
  SemiprimeD1JetRecoveryGrid SemiprimeD1GridResidue SemiprimeD1GridHistogram
  SemiprimeD1HermiteIdentity

/-- Original active Hermite indices, acquired by the original grid/taper test. -/
def active (a h u : ℕ) : Finset ℕ :=
  (Finset.range (size a)).filter (fun q => q≠center a ∧ 0<nodeMultiplicity a h u q)

/-- Original signed rational node, with no field-point selection or inverse map. -/
def node (a q : ℕ) : ℚ := (point a q:ℚ)

/-- Original signed nodes are globally distinct before any active filtering. -/
theorem node_injective (a : ℕ) : Function.Injective (node a) := by
  intro q r he
  have hi : point a q=point a r := by
    unfold node at he
    exact_mod_cast he
  unfold point at hi
  omega

/-- Every actually active node has a positive retained multiplicity. -/
theorem active_positive (a h u t : ℕ) (ht : t∈active a h u) :
    0<nodeMultiplicity a h u t := (Finset.mem_filter.mp ht).2.2

/-- Actual signed original valuation-level set. -/
def originalLevel (a v : ℕ) : Finset ℕ :=
  (Finset.range (size a)).filter (fun q => q≠center a ∧ padicValInt 2 (point a q)=v)

/-- Exact cardinality of the ACTUAL signed grid levels, via the explicit translation. -/
theorem originalLevel_card (a v : ℕ) (hv : v≤a) : (originalLevel a v).card=2^(a-v) := by
  have hex : a+1-v-1=a-v := by omega
  rw [← hex,← residueLevel_card (a+1) v (by omega)]
  let idx := fun (q:ℕ) (hq:q∈originalLevel a v) =>
    (⟨q,Finset.mem_range.mp (Finset.mem_filter.mp hq).1⟩:Fin (size a))
  apply Finset.card_bij (fun q hq => gridEquiv a (idx q hq))
  · intro q hq
    obtain ⟨_,hqc,hval⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro he;exact hqc ((gridEquiv_zero_iff a (idx q hq)).mp he)
    · exact (original_order a (idx q hq) hqc).trans hval
  · intro q hq r hr he
    exact congrArg Fin.val ((gridEquiv a).injective he)
  · intro x hx
    obtain ⟨_,hxn,hval⟩ := Finset.mem_filter.mp hx
    let q := (gridEquiv a).symm x
    have hqc : q.val≠center a := by
      intro he
      have h0 := (gridEquiv_zero_iff a q).mpr he
      rw [(gridEquiv a).apply_symm_apply] at h0
      exact hxn h0
    have hq : q.val∈originalLevel a v := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr q.isLt,hqc,?_⟩
      have ho := original_order a q hqc
      rw [(gridEquiv a).apply_symm_apply] at ho
      exact ho.symm.trans hval
    refine ⟨q.val,hq,?_⟩
    have he : idx q.val hq=q := Fin.ext rfl
    rw [he]
    exact (gridEquiv a).apply_symm_apply x

/-- The literal L odd nodes alone supply at least L*h*u retained coefficients. -/
theorem total_ge_odd (a h u : ℕ) (hhu : 0<h*u) :
    2^a*(h*u)≤total (active a h u) (nodeMultiplicity a h u) := by
  have hsub : originalLevel a 0⊆active a h u := by
    intro q hq
    obtain ⟨hqr,hqc,hval⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨hqr,hqc,?_⟩
    simpa only [nodeMultiplicity,hval,SemiprimeD1TaperedLoss.multiplicity,Nat.sub_zero] using hhu
  have hsum : (∑ q∈originalLevel a 0,nodeMultiplicity a h u q)=2^a*(h*u) := by
    calc
      _ = ∑ _q∈originalLevel a 0,h*u := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [nodeMultiplicity,(Finset.mem_filter.mp hq).2.2,SemiprimeD1TaperedLoss.multiplicity,Nat.sub_zero]
      _ = _ := by rw [Finset.sum_const,smul_eq_mul,originalLevel_card a 0 (Nat.zero_le _),Nat.sub_zero]
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Original explicit ceiling numerator satisfies h*u>=3M, no precision advice. -/
theorem height_mul_ge (M u : ℕ) (hu : 0<u) : 3*M≤height M u*u := by
  have hm := Nat.mod_lt (3*M+u-1) hu
  have hd := Nat.div_add_mod (3*M+u-1) u
  change u*height M u+(3*M+u-1)%u=3*M+u-1 at hd
  have he : (3*M+u-1)+1=3*M+u := by omega
  nlinarith

/-- Original graph-degree bound is strictly below ACTUAL total retained multiplicity. -/
theorem original_degree_sufficient (a M u : ℕ) (hu : 0<u) (hM : u≤M) :
    M*(2*(2^a)-1)<total (active a (height M u) u) (nodeMultiplicity a (height M u) u) := by
  have hc := height_mul_ge M u hu
  have hmp : 0<M := by omega
  have hhu : 0<height M u*u := by nlinarith
  have ht := total_ge_odd a (height M u) u hhu
  have hL : 0<(2:ℕ)^a := by positivity
  have he : 2*(2^a)-1+1=2*(2^a) := by omega
  have hmul := Nat.mul_le_mul_left (2^a) hc
  nlinarith

/-- ORIGINAL distinct signed tapered grid Hermite identity, with the graph-degree
cutoff discharged by its actual original multiplicities. -/
theorem original_at_zero (a M u : ℕ) (hu : 0<u) (hM : u≤M) (H : ℚ[X])
    (hH : H.natDegree≤M*(2*(2^a)-1)) :
    H.eval 0=∑ t∈active a (height M u) u,
      (cardinal (active a (height M u) u) (node a) (nodeMultiplicity a (height M u) u) t).eval 0*
      (SemiprimeHermiteRecovery.localQuotient
        ((taylor (node a t) H)%ₘ X^nodeMultiplicity a (height M u) u t)
        (taylor (node a t) (cardinal (active a (height M u) u) (node a)
          (nodeMultiplicity a (height M u) u) t))
        (nodeMultiplicity a (height M u) u t)).eval (-(node a t)) := by
  apply at_zero
  · exact (node_injective a).injOn
  · intro t ht
    exact active_positive a (height M u) u t ht
  · exact hH.trans_lt (original_degree_sufficient a M u hu hM)

end RiemannGaussian.SemiprimeD1HermiteNodes
