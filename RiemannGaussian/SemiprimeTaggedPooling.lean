/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSharedIntervalJet
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Higher coefficients retain zero-row labels after pooling

The first nonzero deformation coefficient retains the product of zero-row
tags. A marked companion retains their individual index labels, even when
ordinary first jets vanish. Scalar coefficients also distinguish unequal
hidden zero-row counts. These are exact coefficient identities, rather than
a cheap construction oracle: obtaining the required pooled coefficients
still has an unresolved total cost. A dense bivariate prefix has a quadratic
number of explicit slots and does not meet the sixth-root input budget.
-/

namespace RiemannGaussian.SemiprimeTaggedPooling

open scoped BigOperators
open Polynomial

/-- Zero indices are proof-side bookkeeping in the current coefficient
ring. No hidden-field zero set is supplied to a public constructor. -/
noncomputable def zeroIndices {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) : Finset ι := by
  classical
  exact S.filter (fun i => r i=0)

/-- The complete public linear deformation retains each original residual
and its slope. The coefficient ring may itself be a tag polynomial ring. -/
noncomputable def deformation {R ι : Type*} [CommRing R]
    (S : Finset ι) (r v : ι → R) : R[X] :=
  ∏ i ∈ S, (C (r i)+C (v i)*X)

/-- The marked companion omits one original factor at a time and keeps
its source weight. It uses no division by a vanishing residual. -/
noncomputable def markedDeformation {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w : ι → R) : R[X] :=
  ∑ i ∈ S, C (w i)*deformation (S.erase i) r v

/-- Constant deformation coefficients recover the original collision
product, including complete semiprime saturation. -/
theorem deformation_coeff_zero {R ι : Type*} [CommRing R]
    (S : Finset ι) (r v : ι → R) :
    (deformation S r v).coeff 0=∏ i ∈ S, r i := by
  rw [coeff_zero_eq_eval_zero]
  simp only [deformation, eval_prod, eval_add, eval_mul, eval_C, eval_X,
    mul_zero, add_zero]

/-- Reduction to any coefficient ring commutes with the public product. -/
theorem deformation_map {R F ι : Type*} [CommRing R] [CommRing F]
    (f : R →+* F) (S : Finset ι) (r v : ι → R) :
    (deformation S r v).map f=deformation S (fun i => f (r i)) (fun i => f (v i)) := by
  simp only [deformation, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_mul, map_C, map_X]

/-- The zero-index set stays within the original source. -/
theorem zeroIndices_subset {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) : zeroIndices S r ⊆ S := by
  classical
  exact Finset.filter_subset _ _

/-- Factor out precisely one deformation variable for each zero source
residual. Nonzero source factors are retained rather than discarded. -/
theorem deformation_zero_factorization {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v : ι → R) :
    deformation S r v=X^(zeroIndices S r).card*
      (C (∏ i ∈ zeroIndices S r, v i)*deformation (S \ zeroIndices S r) r v) := by
  classical
  have hprod : (∏ i ∈ zeroIndices S r, (C (r i)+C (v i)*X : R[X]))=
      C (∏ i ∈ zeroIndices S r, v i)*X^(zeroIndices S r).card := by
    calc
      (∏ i ∈ zeroIndices S r, (C (r i)+C (v i)*X : R[X]))=
          ∏ i ∈ zeroIndices S r, (C (v i)*X : R[X]) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hz := (Finset.mem_filter.mp hi).2
        rw [hz, map_zero, zero_add]
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, map_prod]
  unfold deformation
  rw [← Finset.prod_sdiff (zeroIndices_subset S r), hprod]
  ring

/-- Every coefficient below the local zero count vanishes, including
ordinary first derivatives when several rows vanish together. -/
theorem deformation_coeff_below {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v : ι → R) {n : ℕ} (hn : n<(zeroIndices S r).card) :
    (deformation S r v).coeff n=0 := by
  rw [deformation_zero_factorization, coeff_X_pow_mul']
  exact if_neg (by omega)

/-- The first surviving coefficient retains each zero slope and every
nonzero original residual, over any commutative ring. -/
theorem deformation_head_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v : ι → R) :
    (deformation S r v).coeff (zeroIndices S r).card=
      (∏ i ∈ zeroIndices S r, v i)*(∏ i ∈ S \ zeroIndices S r, r i) := by
  rw [deformation_zero_factorization, coeff_X_pow_mul', if_pos (le_refl _),
    Nat.sub_self, coeff_C_mul, deformation_coeff_zero]

/-- Removing an index removes it from the proof-side zero set too. -/
theorem zeroIndices_erase {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r : ι → R) (i : ι) :
    zeroIndices (S.erase i) r=(zeroIndices S r).erase i := by
  classical
  ext j
  simp [zeroIndices, and_assoc]

/-- Omitting a zero row leaves exactly the same nonzero source factors. -/
theorem nonzeroIndices_erase_of_zero {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r : ι → R) {i : ι} (hi : i ∈ zeroIndices S r) :
    (S.erase i) \ zeroIndices (S.erase i) r=S \ zeroIndices S r := by
  classical
  rw [zeroIndices_erase]
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  have hh : i ∈ S := zeroIndices_subset S r hi
  by_cases he : j=i
  · subst j
    simp [hi]
  · simp [he]

/-- The marked coefficient one order below the head retains all the
individual zero-index cofactors. Nonzero-row markings vanish there. -/
theorem markedDeformation_head_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w : ι → R) (hm : 0 < (zeroIndices S r).card) :
    (markedDeformation S r v w).coeff ((zeroIndices S r).card-1)=
      (∑ i ∈ zeroIndices S r, w i*∏ j ∈ (zeroIndices S r).erase i, v j)*
        ∏ j ∈ S \ zeroIndices S r, r j := by
  classical
  simp only [markedDeformation, finsetSum_coeff, coeff_C_mul]
  rw [Finset.sum_mul]
  have hsum : (∑ i ∈ zeroIndices S r,
      w i*(deformation (S.erase i) r v).coeff ((zeroIndices S r).card-1))=
      ∑ i ∈ S, w i*(deformation (S.erase i) r v).coeff ((zeroIndices S r).card-1) := by
    apply Finset.sum_subset (zeroIndices_subset S r)
    intro i _ hn
    rw [deformation_coeff_below, mul_zero]
    rw [zeroIndices_erase, Finset.erase_eq_of_notMem hn]
    omega
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : (zeroIndices (S.erase i) r).card=(zeroIndices S r).card-1 := by
    rw [zeroIndices_erase, Finset.card_erase_of_mem hi]
  rw [← hcard, deformation_head_coeff, nonzeroIndices_erase_of_zero S r hi,
    zeroIndices_erase]
  ring

/-- A coefficient is a Hasse derivative at zero. No factorial inverse is
needed, so the observation survives small positive characteristic. -/
theorem deformation_hasse_at_zero {R ι : Type*} [CommRing R]
    (S : Finset ι) (r v : ι → R) (n : ℕ) :
    (hasseDeriv n (deformation S r v)).eval 0=(deformation S r v).coeff n := by
  rw [← coeff_zero_eq_eval_zero, hasseDeriv_coeff]
  simp

/-- Simple zero slopes make the head genuinely nonzero over a domain. -/
theorem deformation_head_coeff_ne_zero {R ι : Type*} [CommRing R] [IsDomain R]
    [DecidableEq ι] (S : Finset ι) (r v : ι → R)
    (hv : ∀ i ∈ zeroIndices S r, v i ≠ 0) :
    (deformation S r v).coeff (zeroIndices S r).card ≠ 0 := by
  classical
  rw [deformation_head_coeff]
  apply mul_ne_zero (Finset.prod_ne_zero_iff.mpr hv)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi he
  have hh := Finset.mem_sdiff.mp hi
  exact hh.2 (Finset.mem_filter.mpr ⟨hh.1, he⟩)

/-- Unequal local zero counts give a proper prime gcd at the smaller
count. The larger side vanishes without supplying its slope inverses. -/
theorem unequal_zero_counts_gcd {ι : Type*} [DecidableEq ι]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (S : Finset ι)
    (r v : ι → ZMod (p*q))
    (hcount : (zeroIndices S (fun i =>
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (r i))).card <
      (zeroIndices S (fun i =>
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (r i))).card)
    (hv : ∀ i ∈ zeroIndices S (fun i =>
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (r i)),
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (v i) ≠ 0) :
    (p*q).gcd ((deformation S r v).coeff
      (zeroIndices S (fun i =>
        ZMod.castHom (dvd_mul_right p q) (ZMod p) (r i))).card).val=q := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p*q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp.pos hq.pos)⟩
  let n := (zeroIndices S (fun i =>
    ZMod.castHom (dvd_mul_right p q) (ZMod p) (r i))).card
  let c := (deformation S r v).coeff n
  have hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) c ≠ 0 := by
    rw [show c=(deformation S r v).coeff n from rfl, ← coeff_map, deformation_map]
    exact deformation_head_coeff_ne_zero S _ _ hv
  have hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) c=0 := by
    rw [show c=(deformation S r v).coeff n from rfl, ← coeff_map, deformation_map]
    exact deformation_coeff_below S _ _ hcount
  have hpnot : ¬p ∣ c.val := by
    intro hd
    apply hP
    rw [← SemiprimeCentreFreeCover.castHom_val (dvd_mul_right p q)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hqdiv : q ∣ c.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [SemiprimeCentreFreeCover.castHom_val (dvd_mul_left q p)]
    exact hQ
  exact Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr hpnot) hqdiv

/-- A public row tag is retained in each slope; X in the coefficient ring
is the tag variable, and the outer X is the deformation variable. -/
noncomputable def taggedDeformation {R ι : Type*} [CommRing R]
    (S : Finset ι) (r v a : ι → R) : R[X][X] :=
  deformation S (fun i => C (r i)) (fun i => C (v i)*(X-C (a i)))

/-- The companion retains the same public row tags and source markings. -/
noncomputable def taggedMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) : R[X][X] :=
  markedDeformation S (fun i => C (r i))
    (fun i => C (v i)*(X-C (a i))) (fun i => C (w i))

/-- Embedding residuals as constant tag polynomials creates no new zeros. -/
theorem zeroIndices_const {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) :
    zeroIndices S (fun i => C (r i))=zeroIndices S r := by
  classical
  ext i
  simp [zeroIndices, C_eq_zero]

/-- The head is the locator of the actual zero rows, times the original
nonzero source scale. This records row labels, rather than their sum. -/
theorem tagged_head_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v a : ι → R) :
    (taggedDeformation S r v a).coeff (zeroIndices S r).card=
      C ((∏ i ∈ zeroIndices S r, v i)*(∏ i ∈ S \ zeroIndices S r, r i))*
        SemiprimeCartesianCompletion.rootPolynomial (zeroIndices S r) a := by
  unfold taggedDeformation
  rw [← zeroIndices_const S r, deformation_head_coeff, zeroIndices_const]
  simp only [Finset.prod_mul_distrib, ← map_prod, map_mul,
    SemiprimeCartesianCompletion.rootPolynomial]
  ring

/-- The marked head retains all the labelled cofactors without dividing
by any vanishing original source residual. -/
theorem tagged_marked_head_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) (hm : 0 < (zeroIndices S r).card) :
    (taggedMarked S r v w a).coeff ((zeroIndices S r).card-1)=
      (∑ i ∈ zeroIndices S r, C (w i)*
        ∏ j ∈ (zeroIndices S r).erase i, C (v j)*(X-C (a j)))*
      C (∏ j ∈ S \ zeroIndices S r, r j) := by
  unfold taggedMarked
  rw [← zeroIndices_const S r, markedDeformation_head_coeff]
  · simp only [zeroIndices_const, map_prod]
  · rwa [zeroIndices_const]

/-- The derivative at a row tag is its cofactor. Other terms contain the
vanishing factor at that tag, including coincident-tag cases. -/
theorem rootPolynomial_derivative_at_tag {R ι : Type*} [CommRing R]
    [DecidableEq ι] (S : Finset ι) (a : ι → R) {i : ι} (hi : i ∈ S) :
    (SemiprimeCartesianCompletion.rootPolynomial S a).derivative.eval (a i)=
      ∏ j ∈ S.erase i, (a i-a j) := by
  simp only [SemiprimeCartesianCompletion.rootPolynomial, derivative_prod_finset,
    derivative_X_sub_C, mul_one, eval_finsetSum, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) (sub_self _)
  · intro hn
    exact (hn hi).elim

/-- Evaluation of the marked head isolates one original zero row. -/
theorem tagged_marked_head_eval {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) {i : ι} (hi : i ∈ zeroIndices S r) :
    ((taggedMarked S r v w a).coeff ((zeroIndices S r).card-1)).eval (a i)=
      w i*(∏ j ∈ (zeroIndices S r).erase i, v j)*
        (∏ j ∈ (zeroIndices S r).erase i, (a i-a j))*
        ∏ j ∈ S \ zeroIndices S r, r j := by
  have hm : 0 < (zeroIndices S r).card := Finset.card_pos.mpr ⟨i, hi⟩
  rw [tagged_marked_head_coeff S r v w a hm]
  simp only [eval_mul, eval_C, eval_finsetSum, eval_prod, eval_sub, eval_X]
  rw [Finset.sum_eq_single i]
  · rw [Finset.prod_mul_distrib]
    ring
  · intro j _ hji
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩)]
    · exact mul_zero _
    · rw [sub_self, mul_zero]
  · intro hn
    exact (hn hi).elim

/-- One source identity w_i=k*v_i suffices to recover its label from the
marked head and locator derivative. No hidden vector of indices is input. -/
theorem tagged_marked_identity_at_zero_tag {R ι : Type*} [CommRing R]
    [DecidableEq ι] (S : Finset ι) (r v w a : ι → R) {i : ι}
    (hi : i ∈ zeroIndices S r) (k : R) (hw : w i=k*v i) :
    ((taggedMarked S r v w a).coeff ((zeroIndices S r).card-1)).eval (a i)=
      k*((taggedDeformation S r v a).coeff (zeroIndices S r).card).derivative.eval (a i) := by
  rw [tagged_marked_head_eval S r v w a hi, tagged_head_coeff,
    derivative_C_mul, eval_mul, eval_C, rootPolynomial_derivative_at_tag _ _ hi, hw]
  rw [← Finset.mul_prod_erase (zeroIndices S r) v hi]
  ring

/-- Distinct local tags and nonzero local slopes make the head derivative
invertible in a field. This is separate from a public unit certificate. -/
theorem tagged_head_derivative_ne_zero {R ι : Type*} [CommRing R] [IsDomain R]
    [DecidableEq ι] (S : Finset ι) (r v a : ι → R) {i : ι}
    (hi : i ∈ zeroIndices S r) (hv : ∀ j ∈ zeroIndices S r, v j ≠ 0)
    (ha : ∀ j ∈ (zeroIndices S r).erase i, a i ≠ a j) :
    ((taggedDeformation S r v a).coeff (zeroIndices S r).card).derivative.eval (a i) ≠ 0 := by
  rw [tagged_head_coeff, derivative_C_mul, eval_mul, eval_C,
    rootPolynomial_derivative_at_tag _ _ hi]
  apply mul_ne_zero
  · rw [← deformation_head_coeff]
    exact deformation_head_coeff_ne_zero S r v hv
  · exact Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (ha j hj))

/-- A public certified inverse decodes the marked head at one row tag. -/
def decodedHead {R : Type*} [CommRing R] (marked : R[X]) (a : R) (denom : Rˣ) : R :=
  ((denom⁻¹ : Rˣ) : R)*marked.eval a

/-- Common unit normalization of the two heads preserves the decoded
index, with the denominator scaled by the same checked unit. -/
theorem decodedHead_rescale {R : Type*} [CommRing R]
    (marked : R[X]) (a : R) (scale denom : Rˣ) :
    decodedHead (C (scale : R)*marked) a (scale*denom)=decodedHead marked a denom := by
  simp only [decodedHead, eval_mul, eval_C, mul_inv_rev, Units.val_mul]
  have hc : ((scale⁻¹ : Rˣ) : R)*(scale : R)=1 := by simp
  calc
    _ = ((denom⁻¹ : Rˣ) : R)*(((scale⁻¹ : Rˣ) : R)*(scale : R))*marked.eval a := by ring
    _ = _ := by rw [hc, mul_one]

/-- Once its unit is checked against the locator derivative, the decoder
returns the literal source weight ratio at that row. -/
theorem decodedHead_at_zero_tag {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) {i : ι} (hi : i ∈ zeroIndices S r)
    (k : R) (hw : w i=k*v i) (denom : Rˣ)
    (hdenom : (denom : R)=
      ((taggedDeformation S r v a).coeff (zeroIndices S r).card).derivative.eval (a i)) :
    decodedHead ((taggedMarked S r v w a).coeff ((zeroIndices S r).card-1))
      (a i) denom=k := by
  unfold decodedHead
  rw [tagged_marked_identity_at_zero_tag S r v w a hi k hw, ← hdenom]
  calc
    ((denom⁻¹ : Rˣ) : R)*(k*(denom : R))=
        k*(((denom⁻¹ : Rˣ) : R)*(denom : R)) := by ring
    _ = k := by simp

/-- Reduction preserves the entire marked public deformation. -/
theorem markedDeformation_map {R F ι : Type*} [CommRing R] [CommRing F]
    [DecidableEq ι] (f : R →+* F) (S : Finset ι) (r v w : ι → R) :
    (markedDeformation S r v w).map f=
      markedDeformation S (fun i => f (r i)) (fun i => f (v i)) (fun i => f (w i)) := by
  simp only [markedDeformation, Polynomial.map_sum, Polynomial.map_mul, map_C,
    deformation_map]

/-- Both polynomial variables commute with reduction to a local ring. -/
theorem taggedDeformation_map {R F ι : Type*} [CommRing R] [CommRing F]
    (f : R →+* F) (S : Finset ι) (r v a : ι → R) :
    (taggedDeformation S r v a).map (Polynomial.mapRingHom f)=
      taggedDeformation S (fun i => f (r i)) (fun i => f (v i)) (fun i => f (a i)) := by
  simp only [taggedDeformation, deformation_map, Polynomial.coe_mapRingHom,
    map_C, Polynomial.map_mul, Polynomial.map_sub, map_X]

/-- The same reduction identity holds for the marked companion. -/
theorem taggedMarked_map {R F ι : Type*} [CommRing R] [CommRing F]
    [DecidableEq ι] (f : R →+* F) (S : Finset ι) (r v w a : ι → R) :
    (taggedMarked S r v w a).map (Polynomial.mapRingHom f)=
      taggedMarked S (fun i => f (r i)) (fun i => f (v i))
        (fun i => f (w i)) (fun i => f (a i)) := by
  simp only [taggedMarked, markedDeformation_map, Polynomial.coe_mapRingHom,
    map_C, Polynomial.map_mul, Polynomial.map_sub, map_X]

/-- A single public decoder reduces to the source index in every local
ring at the observed head order. Hidden zero sets remain proof bookkeeping. -/
theorem decodedHead_map_zero_tag {R F ι : Type*} [CommRing R] [CommRing F]
    [DecidableEq ι] (f : R →+* F) (S : Finset ι) (r v w a : ι → R)
    {i : ι} (hi : i ∈ zeroIndices S (fun j => f (r j))) (n : ℕ)
    (hn : n=(zeroIndices S (fun j => f (r j))).card)
    (k : F) (hw : f (w i)=k*f (v i)) (denom : Rˣ)
    (hdenom : (denom : R)=((taggedDeformation S r v a).coeff n).derivative.eval (a i)) :
    f (decodedHead ((taggedMarked S r v w a).coeff (n-1)) (a i) denom)=k := by
  have hQ : ((taggedDeformation S r v a).coeff n).map f=
      (taggedDeformation S (fun j => f (r j)) (fun j => f (v j))
        (fun j => f (a j))).coeff n := by
    rw [← taggedDeformation_map f S r v a, coeff_map]
    rfl
  have hH : ((taggedMarked S r v w a).coeff (n-1)).map f=
      (taggedMarked S (fun j => f (r j)) (fun j => f (v j))
        (fun j => f (w j)) (fun j => f (a j))).coeff (n-1) := by
    rw [← taggedMarked_map f S r v w a, coeff_map]
    rfl
  have hweight : f (((taggedMarked S r v w a).coeff (n-1)).eval (a i))=
      k*f (denom : R) := by
    rw [← eval_map_apply, hH, hn,
      tagged_marked_identity_at_zero_tag S (fun j => f (r j)) (fun j => f (v j))
        (fun j => f (w j)) (fun j => f (a j)) hi k hw, hdenom,
      ← eval_map_apply, ← derivative_map, hQ, hn]
  unfold decodedHead
  rw [map_mul, hweight]
  calc
    f ((denom⁻¹ : Rˣ) : R)*(k*f (denom : R))=
        k*f (((denom⁻¹ : Rˣ) : R)*(denom : R)) := by rw [map_mul]; ring
    _ = k := by simp

/-- The original interval supplies w_i=k*v_i at every actual root.
This discharges the marked-weight identity from the literal source. -/
theorem original_row_marking_at_root {R : Type*} [CommRing R] (alpha x : R)
    {L k : ℕ} (hk : k<L) (hx : x=alpha^k) :
    -SemiprimeIntervalJet.baseDerivative alpha x L=
      (k : R)*(x*SemiprimeIntervalJet.targetDerivative alpha x L) := by
  rw [hx, SemiprimeIntervalJet.baseDerivative_at_root alpha hk]
  ring

/-- Tagged decoding extracts the actual original interval exponent after
reduction. Its public inputs are original row jets, tags and a checked unit. -/
theorem decodedHead_original_row_root {R F ι : Type*} [CommRing R] [CommRing F]
    [DecidableEq ι] (f : R →+* F) (S : Finset ι) (alpha : R) (x a : ι → R)
    (L n : ℕ) {i : ι} (hi : i ∈ S) {k : ℕ} (hk : k<L)
    (hroot : f (x i)=(f alpha)^k)
    (hn : n=(zeroIndices S (fun j => f (SemiprimeIntervalJet.intervalProduct alpha (x j) L))).card)
    (denom : Rˣ) (hdenom : (denom : R)=
      ((taggedDeformation S
        (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
        (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L) a).coeff n).derivative.eval (a i)) :
    f (decodedHead ((taggedMarked S
      (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
      (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L)
      (fun j => -SemiprimeIntervalJet.baseDerivative alpha (x j) L) a).coeff (n-1))
      (a i) denom)=(k : F) := by
  classical
  apply decodedHead_map_zero_tag f S _ _ _ a (n := n) (k := (k : F))
    (denom := denom) (hn := hn) (hdenom := hdenom)
  · apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    change f (SemiprimeIntervalJet.intervalProduct alpha (x i) L)=0
    rw [SemiprimeIntervalJet.intervalProduct_map, hroot]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) (sub_self _)
  · rw [map_neg, SemiprimeIntervalJet.baseDerivative_map, map_mul,
      SemiprimeIntervalJet.targetDerivative_map]
    exact original_row_marking_at_root (f alpha) (f (x i)) hk hroot

/-- Equal head orders can still separate hidden exponent indices. The
pooled decoder uses only the original source and a checked public inverse. -/
theorem decodedHead_original_distinct_index_gcd {ι : Type*} [DecidableEq ι]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (S : Finset ι)
    (alpha : ZMod (p*q)) (x a : ι → ZMod (p*q)) (L n : ℕ)
    {i : ι} (hi : i ∈ S) {k l : ℕ} (hk : k<L) (hl : l<L)
    (hLq : L ≤ q) (hkl : k ≠ l)
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x i)=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha)^k)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) (x i)=
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha)^l)
    (hnP : n=(zeroIndices S (fun j => ZMod.castHom (dvd_mul_right p q) (ZMod p)
      (SemiprimeIntervalJet.intervalProduct alpha (x j) L))).card)
    (hnQ : n=(zeroIndices S (fun j => ZMod.castHom (dvd_mul_left q p) (ZMod q)
      (SemiprimeIntervalJet.intervalProduct alpha (x j) L))).card)
    (denom : (ZMod (p*q))ˣ) (hdenom : (denom : ZMod (p*q))=
      ((taggedDeformation S
        (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
        (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L) a).coeff n).derivative.eval (a i)) :
    (p*q).gcd (decodedHead ((taggedMarked S
      (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
      (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L)
      (fun j => -SemiprimeIntervalJet.baseDerivative alpha (x j) L) a).coeff (n-1))
        (a i) denom-(k : ZMod (p*q))).val=p := by
  apply SemiprimeIntervalJet.distinct_index_gcd hp hq hk hl hLq hkl
  · exact decodedHead_original_row_root
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)) S alpha x a L n hi hk hP hnP denom hdenom
  · exact decodedHead_original_row_root
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)) S alpha x a L n hi hl hQ hnQ denom hdenom

/-- Explicit slots in a dense bivariate prefix through outer order B.
This is a representation cost, not a lower bound for all algorithms. -/
def densePrefixSlots (B : ℕ) : List (ℕ × ℕ) :=
  (List.range (B+1)).flatMap (fun j => (List.range (j+1)).map (fun k => (j, k)))

/-- The fully retained prefix has a quadratic number of slots even
though a single head has only B+1 coefficients. -/
theorem densePrefixSlots_length (B : ℕ) :
    2*(densePrefixSlots B).length=(B+1)*(B+2) := by
  induction B with
  | zero => simp [densePrefixSlots]
  | succ B ih =>
      have hstep : (densePrefixSlots (B+1)).length=(densePrefixSlots B).length+(B+2) := by
        unfold densePrefixSlots
        rw [List.range_succ]
        simp
      rw [hstep]
      nlinarith

/-- Keeping both dense prefixes allocates a square number of slots,
despite the linear degree bounds on the two final head polynomials. -/
theorem dense_combined_prefix_length {m : ℕ} (hm : 0 < m) :
    (densePrefixSlots m).length+(densePrefixSlots (m-1)).length=(m+1)^2 := by
  have hQ := densePrefixSlots_length m
  have hH := densePrefixSlots_length (m-1)
  have he : m-1+1=m := by omega
  rw [he] at hH
  nlinarith

/-- The locator head itself has at most one degree per zero row. This
output bound does not provide a construction with the same cost. -/
theorem tagged_head_degree_le {R ι : Type*} [CommRing R] [Nontrivial R]
    [DecidableEq ι] (S : Finset ι) (r v a : ι → R) :
    ((taggedDeformation S r v a).coeff (zeroIndices S r).card).natDegree ≤
      (zeroIndices S r).card := by
  rw [tagged_head_coeff]
  calc
    _ ≤ (C ((∏ i ∈ zeroIndices S r, v i)*
        ∏ i ∈ S \ zeroIndices S r, r i)).natDegree+
      (SemiprimeCartesianCompletion.rootPolynomial (zeroIndices S r) a).natDegree :=
        natDegree_mul_le
    _ = (zeroIndices S r).card := by
      rw [natDegree_C, zero_add]
      exact natDegree_finsetProd_X_sub_C_eq_card (zeroIndices S r) a

/-- The marked head has one less degree than the zero count. It retains
individual markings in a linear-size final polynomial payload. -/
theorem tagged_marked_head_degree_le {R ι : Type*} [CommRing R]
    [DecidableEq ι] (S : Finset ι) (r v w a : ι → R)
    (hm : 0 < (zeroIndices S r).card) :
    ((taggedMarked S r v w a).coeff ((zeroIndices S r).card-1)).natDegree ≤
      (zeroIndices S r).card-1 := by
  have hprod (T : Finset ι) :
      (∏ j ∈ T, C (v j)*(X-C (a j))).natDegree ≤ T.card := by
    calc
      _ ≤ ∑ j ∈ T, (C (v j)*(X-C (a j))).natDegree := natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ (C (v j)).natDegree+(X-C (a j)).natDegree := natDegree_mul_le
          _ ≤ 0+1 := Nat.add_le_add (by simp) (natDegree_X_sub_C_le (a j))
          _ = 1 := rfl
      _ = T.card := by simp
  rw [tagged_marked_head_coeff S r v w a hm]
  have hsum := natDegree_sum_le_of_forall_le (zeroIndices S r)
    (fun i => C (w i)*∏ j ∈ (zeroIndices S r).erase i, C (v j)*(X-C (a j)))
    (n := (zeroIndices S r).card-1)
  have hs : (∑ i ∈ zeroIndices S r, C (w i)*
      ∏ j ∈ (zeroIndices S r).erase i, C (v j)*(X-C (a j))).natDegree ≤
      (zeroIndices S r).card-1 := by
    apply hsum
    intro i hi
    calc
      _ ≤ (C (w i)).natDegree+
        (∏ j ∈ (zeroIndices S r).erase i, C (v j)*(X-C (a j))).natDegree := natDegree_mul_le
      _ ≤ (zeroIndices S r).card-1 := by
        rw [natDegree_C, zero_add, ← Finset.card_erase_of_mem hi]
        exact hprod _
  exact (natDegree_mul_le.trans (by simpa only [natDegree_C, add_zero] using hs))

/-- Small literal source rows used to test information loss in pooling.
They test the decoder, rather than the global centre-free coverage theorem. -/
def controlTargets (i : ℕ) : ZMod 35 := if i=1 then 32 else 9

/-- Original interval residuals for the two-row pooling control. -/
def controlResidual (i : ℕ) : ZMod 35 :=
  SemiprimeIntervalJet.intervalProduct 2 (controlTargets i) 3

/-- Original target slopes, including the target rescaling. -/
def controlSlope (i : ℕ) : ZMod 35 :=
  controlTargets i*SemiprimeIntervalJet.targetDerivative 2 (controlTargets i) 3

/-- Original exponent markings from the logarithmic base derivative. -/
def controlWeight (i : ℕ) : ZMod 35 :=
  -SemiprimeIntervalJet.baseDerivative 2 (controlTargets i) 3

/-- Kernel-checked row data from the original finite source products. -/
theorem control_original_rows :
    controlResidual 1=0 ∧ controlResidual 2=0 ∧
    controlSlope 1=31 ∧ controlSlope 2=24 ∧
    controlWeight 1=6 ∧ controlWeight 2=3 := by
  norm_num [controlResidual, controlSlope, controlWeight, controlTargets,
    SemiprimeIntervalJet.intervalProduct, SemiprimeIntervalJet.targetDerivative,
    SemiprimeIntervalJet.baseDerivative, SemiprimeIntervalJet.cofactor,
    Finset.range_add_one, Finset.erase_insert_of_ne]
  reduce_mod_char
  norm_num

/-- Both local fields have the same row labels but opposite index labels.
Their individual indices differ despite equal sums. -/
theorem control_local_indices :
    (32 : ZMod 5)=(2 : ZMod 5)^1 ∧ (32 : ZMod 7)=(2 : ZMod 7)^2 ∧
    (9 : ZMod 5)=(2 : ZMod 5)^2 ∧ (9 : ZMod 7)=(2 : ZMod 7)^1 ∧
    (16 : ZMod 5)=(1 : ZMod 5) ∧ (16 : ZMod 7)=(2 : ZMod 7) ∧
    (22 : ZMod 5)=(2 : ZMod 5) ∧ (22 : ZMod 7)=(1 : ZMod 7) ∧
    (16+22 : ZMod 35)=(3 : ZMod 35) := by
  norm_num
  reduce_mod_char
  norm_num

/-- The control has exactly the two zero source rows in the public ring. -/
theorem control_zero_indices :
    zeroIndices ({1, 2} : Finset ℕ) controlResidual=({1, 2} : Finset ℕ) := by
  classical
  ext i
  simp only [zeroIndices, Finset.mem_filter]
  constructor
  · exact And.left
  intro hi
  refine ⟨hi, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  obtain h1 | h2 := hi
  · subst i
    exact control_original_rows.1
  · subst i
    exact control_original_rows.2.1

/-- Raw heads from the two original source rows, before normalization. -/
theorem control_raw_heads :
    (taggedDeformation ({1, 2} : Finset ℕ) controlResidual controlSlope
      (fun i => (i : ZMod 35))).coeff 2=
        C (9 : ZMod 35)*((X-C 1)*(X-C 2)) ∧
    (taggedMarked ({1, 2} : Finset ℕ) controlResidual controlSlope controlWeight
      (fun i => (i : ZMod 35))).coeff 1=C (27 : ZMod 35)*X+C 4 := by
  have hcard : (zeroIndices ({1, 2} : Finset ℕ) controlResidual).card=2 := by
    rw [control_zero_indices]
    norm_num
  have hQ := tagged_head_coeff ({1, 2} : Finset ℕ) controlResidual controlSlope
    (fun i => (i : ZMod 35))
  have hH := tagged_marked_head_coeff ({1, 2} : Finset ℕ) controlResidual controlSlope
    controlWeight (fun i => (i : ZMod 35)) (by rw [hcard]; norm_num)
  rw [hcard, control_zero_indices] at hQ hH
  obtain ⟨_, _, hv1, hv2, hw1, hw2⟩ := control_original_rows
  constructor
  · rw [hQ]
    norm_num [SemiprimeCartesianCompletion.rootPolynomial, hv1, hv2, map_ofNat]
    reduce_mod_char
  · rw [hH]
    norm_num [hv1, hv2, hw1, hw2, Finset.erase_insert_of_ne, map_ofNat]
    ring_nf
    reduce_mod_char

/-- Public normalization by the inverse of the head scale. -/
noncomputable def controlLocator : (ZMod 35)[X] :=
  C 4*(taggedDeformation ({1, 2} : Finset ℕ) controlResidual controlSlope
    (fun i => (i : ZMod 35))).coeff 2

/-- The companion uses the identical public scale. -/
noncomputable def controlMarkedHead : (ZMod 35)[X] :=
  C 4*(taggedMarked ({1, 2} : Finset ℕ) controlResidual controlSlope controlWeight
    (fun i => (i : ZMod 35))).coeff 1

/-- The normalized payload retains both row labels and their markings. -/
theorem control_normalized_heads :
    (4*9 : ZMod 35)=1 ∧
    controlLocator=X^2-C 3*X+C 2 ∧ controlMarkedHead=C 3*X+C 16 := by
  rw [controlLocator, controlMarkedHead, control_raw_heads.1, control_raw_heads.2]
  norm_num [map_ofNat]
  ring_nf
  reduce_mod_char
  norm_num

/-- Opposite local indices remain individually decodable while their
unlabelled sum agrees in both fields. Each row yields proper integer gcds. -/
theorem control_equal_sum_retains_individual_factors :
    controlMarkedHead.eval (1 : ZMod 35)=
      (16 : ZMod 35)*controlLocator.derivative.eval 1 ∧
    controlMarkedHead.eval (2 : ZMod 35)=
      (22 : ZMod 35)*controlLocator.derivative.eval 2 ∧
    (16+22 : ZMod 35)=3 ∧
    Nat.gcd 35 15=5 ∧ Nat.gcd 35 14=7 ∧
    Nat.gcd 35 20=5 ∧ Nat.gcd 35 21=7 := by
  rw [control_normalized_heads.2.1, control_normalized_heads.2.2]
  norm_num [derivative_sub, derivative_add, derivative_mul]
  reduce_mod_char
  norm_num

/-- The original first-jet product erases every channel in this control. -/
theorem control_first_jet_loss :
    controlResidual 1*controlResidual 2=0 ∧
    controlSlope 1*controlResidual 2+controlResidual 1*controlSlope 2=0 ∧
    controlWeight 1*controlResidual 2+controlResidual 1*controlWeight 2=0 := by
  exact SemiprimeSharedIntervalJet.two_zero_rows_erase_first_jet
    _ _ _ _ control_original_rows.1 control_original_rows.2.1

/-- The public normalized locator supplies checked unit denominators. -/
theorem control_decoder_denominators :
    controlLocator.derivative.eval (1 : ZMod 35)=34 ∧
    controlLocator.derivative.eval (2 : ZMod 35)=1 ∧
    ((ZMod.unitOfCoprime 34 (by norm_num : Nat.Coprime 34 35) : (ZMod 35)ˣ) : ZMod 35)=
      controlLocator.derivative.eval 1 := by
  rw [control_normalized_heads.2.1, ZMod.coe_unitOfCoprime]
  norm_num [derivative_sub, derivative_add, derivative_mul]
  reduce_mod_char
  norm_num

/-- Kernel-checked execution of the public head decoder on both original
rows. The equal sum has not replaced either individual source index. -/
theorem control_decoded_heads :
    decodedHead controlMarkedHead (1 : ZMod 35)
      (ZMod.unitOfCoprime 34 (by norm_num : Nat.Coprime 34 35))=16 ∧
    decodedHead controlMarkedHead (2 : ZMod 35) 1=22 := by
  rw [control_normalized_heads.2.2]
  norm_num [decodedHead]
  have hneg : ZMod.unitOfCoprime 34 (by norm_num : Nat.Coprime 34 35)=
      (-1 : (ZMod 35)ˣ) := by
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    norm_num
    reduce_mod_char
  rw [hneg]
  norm_num
  reduce_mod_char

/-- A locator head vanishes at every actual zero-row tag, over any ring. -/
theorem tagged_head_eval_of_zero_tag {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v a : ι → R) {i : ι} (hi : i ∈ zeroIndices S r) :
    ((taggedDeformation S r v a).coeff (zeroIndices S r).card).eval (a i)=0 := by
  rw [tagged_head_coeff, eval_mul, eval_C]
  simp only [SemiprimeCartesianCompletion.rootPolynomial, eval_prod,
    eval_sub, eval_X, eval_C]
  have hzero : (∏ j ∈ zeroIndices S r, (a i-a j))=0 :=
    Finset.prod_eq_zero hi (sub_self _)
  rw [hzero, mul_zero]

/-- Distinct row tags and simple zero slopes identify exactly the zero
source rows in the locator head. No label orientation is discarded. -/
theorem tagged_head_eval_zero_iff {R ι : Type*} [CommRing R] [IsDomain R]
    [DecidableEq ι] (S : Finset ι) (r v a : ι → R)
    (hv : ∀ j ∈ zeroIndices S r, v j ≠ 0)
    (ha : Set.InjOn a (S : Set ι)) {i : ι} (hi : i ∈ S) :
    ((taggedDeformation S r v a).coeff (zeroIndices S r).card).eval (a i)=0 ↔
      i ∈ zeroIndices S r := by
  have hscale := deformation_head_coeff_ne_zero S r v hv
  rw [deformation_head_coeff] at hscale
  rw [tagged_head_coeff, eval_mul, eval_C, mul_eq_zero]
  simp only [hscale, false_or, SemiprimeCartesianCompletion.rootPolynomial,
    eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨j, hj, he⟩
    have hij := ha hi (zeroIndices_subset S r hj) he
    rwa [hij]
  · intro hz
    exact ⟨i, hz, rfl⟩

/-- Reduction commutes with every outer coefficient of the tag product. -/
theorem taggedDeformation_coeff_map {R F ι : Type*} [CommRing R] [CommRing F]
    (f : R →+* F) (S : Finset ι) (r v a : ι → R) (n : ℕ) :
    ((taggedDeformation S r v a).coeff n).map f=
      (taggedDeformation S (fun j => f (r j)) (fun j => f (v j))
        (fun j => f (a j))).coeff n := by
  rw [← taggedDeformation_map f S r v a, coeff_map]
  rfl

/-- Equal zero counts with different row labels still yield a proper
factor by evaluating the same public head at an original row tag. -/
theorem different_zero_labels_gcd {ι : Type*} [DecidableEq ι]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (S : Finset ι)
    (r v a : ι → ZMod (p*q)) (n : ℕ)
    (hnP : n=(zeroIndices S (fun j =>
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (r j))).card)
    (hnQ : n=(zeroIndices S (fun j =>
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (r j))).card)
    {i : ι} (hi : i ∈ zeroIndices S (fun j =>
      ZMod.castHom (dvd_mul_right p q) (ZMod p) (r j)))
    (hni : i ∉ zeroIndices S (fun j =>
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (r j)))
    (hvQ : ∀ j ∈ zeroIndices S (fun j =>
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (r j)),
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (v j) ≠ 0)
    (haQ : Set.InjOn (fun j =>
      ZMod.castHom (dvd_mul_left q p) (ZMod q) (a j)) (S : Set ι)) :
    (p*q).gcd (((taggedDeformation S r v a).coeff n).eval (a i)).val=p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply SemiprimeCentreFreeCover.separating_residue_gcd hp hq
  · rw [← eval_map_apply, taggedDeformation_coeff_map, hnP]
    exact tagged_head_eval_of_zero_tag S
      (fun j => ZMod.castHom (dvd_mul_right p q) (ZMod p) (r j))
      (fun j => ZMod.castHom (dvd_mul_right p q) (ZMod p) (v j))
      (fun j => ZMod.castHom (dvd_mul_right p q) (ZMod p) (a j)) hi
  · rw [← eval_map_apply, taggedDeformation_coeff_map, hnQ]
    intro he
    exact hni ((tagged_head_eval_zero_iff S
      (fun j => ZMod.castHom (dvd_mul_left q p) (ZMod q) (r j))
      (fun j => ZMod.castHom (dvd_mul_left q p) (ZMod q) (v j))
      (fun j => ZMod.castHom (dvd_mul_left q p) (ZMod q) (a j))
        hvQ haQ (zeroIndices_subset S _ hi)).mp he)

end RiemannGaussian.SemiprimeTaggedPooling
