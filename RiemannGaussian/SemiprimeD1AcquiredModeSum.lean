/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1SeparatedCoefficient
import RiemannGaussian.SemiprimeD1ModeCatalog
import Mathlib.Data.List.ToFinsupp

/-! # Exact useful-value readout over the actually acquired weighted tuples

The finite budget enumerator supplies every possibly nonzero coefficient once.
No full polynomial, support, coefficient oracle or resolvent is an input to the
enumerator. Coefficients in this identity are specifications; the separate
affine coefficient producer supplies them without building a full polynomial.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1AcquiredModeSum
open scoped BigOperators
open SemiprimeD1WeightedPolynomial SemiprimeD1SeparatedCoefficient
variable {R : Type*} [CommRing R]

/-- Original positive weights at the acquired finite indices; other variables are absent. -/
def weight (ws : List ℕ) (j : ℕ) : ℕ := ws.getD j 0

/-- A bounded exponent vector is represented by its actual finite coordinate list. -/
def exponents (K : ℕ) (e : ℕ→₀ℕ) : List ℕ := List.ofFn fun i : Fin K => e i.val

/-- Converting an acquired exponent list to finite support retains its exact weighted degree. -/
theorem degree_list (ws beta : List ℕ) :
    degree (weight ws) beta.toFinsupp=SemiprimeD1WeightedTuples.degree ws beta := by
  induction ws generalizing beta with
  | nil => simp [degree,weight,SemiprimeD1WeightedTuples.degree]
  | cons w ws ih =>
    cases beta with
    | nil => simp [degree,SemiprimeD1WeightedTuples.degree]
    | cons b beta =>
      rw [List.toFinsupp_cons_eq_single_add_embDomain,degree_add,degree_single]
      change w*b+(beta.toFinsupp.embDomain (addRightEmbedding 1)).sum
        (fun j n => (w::ws).getD j 0*n)=w*b+SemiprimeD1WeightedTuples.degree ws beta
      rw [Finsupp.sum_embDomain]
      exact congrArg (fun n => w*b+n) (ih beta)

/-- Equal acquired lists of the same finite shape cannot encode different tuples. -/
theorem list_injective (left right : List ℕ) (hlen : left.length=right.length)
    (he : left.toFinsupp=right.toFinsupp) : left=right := by
  apply List.ext_getElem hlen
  intro j hj hk
  have h := congrArg (fun e => e j) he
  simpa only [List.toFinsupp_apply_lt left j hj,List.toFinsupp_apply_lt right j hk] using h

/-- Every exponent supported on the actual acquired modes round-trips literally. -/
theorem exponents_decode (K : ℕ) (e : ℕ→₀ℕ) (he : ∀ j,K≤j→e j=0) :
    (exponents K e).toFinsupp=e := by
  ext j
  rw [List.toFinsupp_apply]
  by_cases hj : j<K
  · change (List.ofFn (fun i : Fin K => e i.val)).getD j 0=e j
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj)]
    simp only [List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simpa only [exponents,List.length_ofFn] using Nat.le_of_not_gt hj)]
    exact (he j (by omega)).symm

/-- The ACTUAL finite budget menu contains every original nonzero polynomial coefficient. -/
theorem support_in_menu (ws : List ℕ) (hw : ∀ w∈ws,0<w) (p : ℕ) (hp : 0<p)
    (P : MvPolynomial ℕ R) (hweight : Weighted (weight ws) P)
    (hon : On {j|j<ws.length} P) (hmod : (2:R)^p=0) :
    P.support⊆((SemiprimeD1WeightedTuples.tuples ws (p-1)).toFinset.image (fun beta : List ℕ => beta.toFinsupp)) := by
  intro e he
  have hne := MvPolynomial.mem_support_iff.mp he
  have hbound : ∀ j,ws.length≤j→e j=0 := by
    intro j hj
    exact hon e hne j (show ¬j<ws.length from Nat.not_lt.mpr hj)
  have hdecode := exponents_decode ws.length e hbound
  have hdeg : degree (weight ws) e<p := by
    by_contra h
    exact hne (coefficient_zero _ P hweight p hmod e (by omega))
  have hm : exponents ws.length e∈SemiprimeD1WeightedTuples.tuples ws (p-1) := by
    apply (SemiprimeD1WeightedTuples.mem_tuples hw).mpr
    refine ⟨List.length_ofFn,?_⟩
    rw [←degree_list,hdecode]
    omega
  exact Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr hm,hdecode⟩

/-- The useful value is EXACTLY a sum over acquired tuples, with absent coefficients0.
This is the cancellation identity consumed by the direct coefficient supplier. -/
theorem eval_acquired (ws : List ℕ) (hw : ∀ w∈ws,0<w) (p : ℕ) (hp : 0<p)
    (P : MvPolynomial ℕ R) (hweight : Weighted (weight ws) P)
    (hon : On {j|j<ws.length} P) (f : ZMod (2^p)→+*R) (values : ℕ→R) :
    MvPolynomial.eval values P=
      ((SemiprimeD1WeightedTuples.acquire ws (p-1)).values.map fun beta =>
        P.coeff beta.toFinsupp*(beta.toFinsupp.prod fun j n => values j^n)).sum := by
  classical
  let tuples := SemiprimeD1WeightedTuples.tuples ws (p-1)
  let term := fun e : ℕ→₀ℕ => P.coeff e*(e.prod fun j n => values j^n)
  have hsub := support_in_menu ws hw p hp P hweight hon (modular_nilpotence p f)
  have heval : MvPolynomial.eval values P=∑ e∈tuples.toFinset.image (fun beta : List ℕ => beta.toFinsupp),term e := by
    rw [MvPolynomial.eval_eq]
    change (∑ e∈P.support,term e)=_
    apply Finset.sum_subset hsub
    intro e _ he
    dsimp only [term]
    rw [MvPolynomial.notMem_support_iff.mp he,zero_mul]
  have hinj : Set.InjOn (fun beta : List ℕ => beta.toFinsupp) (tuples.toFinset : Set (List ℕ)) := by
    intro left hl right hr he
    have hleft := (SemiprimeD1WeightedTuples.mem_tuples hw).mp (List.mem_toFinset.mp hl)
    have hright := (SemiprimeD1WeightedTuples.mem_tuples hw).mp (List.mem_toFinset.mp hr)
    exact list_injective left right (hleft.1.trans hright.1.symm) he
  rw [heval,Finset.sum_image hinj,List.sum_toFinset _ (SemiprimeD1WeightedTuples.nodup ws (p-1))]
  rw [SemiprimeD1WeightedTuples.acquire_values]

end RiemannGaussian.SemiprimeD1AcquiredModeSum
