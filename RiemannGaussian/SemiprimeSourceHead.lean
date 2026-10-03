/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeTaggedPooling

/-!
# Original source heads and public homogeneous extraction

At the zero-row count, coefficients of a product of full source polynomials
depend only on their constant and linear terms. The marked coefficient one
order below depends only on constant markings. Higher terms do not contribute
at these precise orders; nonzero slopes make them the first surviving heads.
Public row GCD classification allows homogeneous head construction without
a dense deformation prefix; the original row-residual construction cost
still remains. No universal sixth-root bit-operation theorem is claimed.
-/

namespace RiemannGaussian.SemiprimeSourceHead

open scoped BigOperators
open Polynomial
open SemiprimeTaggedPooling

/-- Retain each complete source polynomial rather than replacing it by
its first jet. The coefficient variable is the public deformation. -/
noncomputable def sourceProduct {R ι : Type*} [CommRing R]
    (S : Finset ι) (P : ι → R[X]) : R[X] := ∏ i ∈ S, P i

/-- Complete marked source, including every marking polynomial and every
omitted original source factor. No residual inverse is used. -/
noncomputable def sourceMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P W : ι → R[X]) : R[X] :=
  ∑ i ∈ S, W i*sourceProduct (S.erase i) P

/-- A zero constant term factors out one X exactly; divX is an explicit
coefficient shift, rather than division by a possibly zero scalar. -/
theorem sourceProduct_zero_factorization {R ι : Type*} [CommRing R]
    [DecidableEq ι] (S : Finset ι) (P : ι → R[X]) :
    sourceProduct S P=X^(zeroIndices S (fun i => (P i).coeff 0)).card*
      ((∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX)*
        sourceProduct (S \ zeroIndices S (fun i => (P i).coeff 0)) P) := by
  classical
  have hz : (∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), P i)=
      X^(zeroIndices S (fun i => (P i).coeff 0)).card*
        ∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX := by
    calc
      _ = ∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), X*(P i).divX := by
        apply Finset.prod_congr rfl
        intro i hi
        have h0 := (Finset.mem_filter.mp hi).2
        change (P i).coeff 0=0 at h0
        have h := X_mul_divX_add (P i)
        rw [h0, map_zero, add_zero] at h
        exact h.symm
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const]
  unfold sourceProduct
  rw [← Finset.prod_sdiff (zeroIndices_subset S (fun i => (P i).coeff 0)), hz]
  ring

/-- Arbitrarily high terms in source rows cannot contribute below the
number of rows with zero constant coefficient, even after marking. -/
theorem weighted_source_coeff_below {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P : ι → R[X]) (W : R[X]) {n : ℕ}
    (hn : n<(zeroIndices S (fun i => (P i).coeff 0)).card) :
    (W*sourceProduct S P).coeff n=0 := by
  rw [sourceProduct_zero_factorization]
  rw [show W*(X^(zeroIndices S (fun i => (P i).coeff 0)).card*
      ((∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX)*
        sourceProduct (S \ zeroIndices S (fun i => (P i).coeff 0)) P))=
      X^(zeroIndices S (fun i => (P i).coeff 0)).card*
      (W*((∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX)*
        sourceProduct (S \ zeroIndices S (fun i => (P i).coeff 0)) P)) by ring]
  rw [coeff_X_pow_mul']
  exact if_neg (by omega)

/-- At the first possible order, only linear zero-row terms and constant
nonzero-row terms survive. The entire source and scale are retained. -/
theorem weighted_source_head_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P : ι → R[X]) (W : R[X]) :
    (W*sourceProduct S P).coeff (zeroIndices S (fun i => (P i).coeff 0)).card=
      W.coeff 0*(∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).coeff 1)*
        ∏ i ∈ S \ zeroIndices S (fun i => (P i).coeff 0), (P i).coeff 0 := by
  rw [sourceProduct_zero_factorization]
  rw [show W*(X^(zeroIndices S (fun i => (P i).coeff 0)).card*
      ((∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX)*
        sourceProduct (S \ zeroIndices S (fun i => (P i).coeff 0)) P))=
      X^(zeroIndices S (fun i => (P i).coeff 0)).card*
      (W*((∏ i ∈ zeroIndices S (fun i => (P i).coeff 0), (P i).divX)*
        sourceProduct (S \ zeroIndices S (fun i => (P i).coeff 0)) P)) by ring]
  rw [coeff_X_pow_mul', if_pos (le_refl _), Nat.sub_self]
  simp only [mul_coeff_zero, sourceProduct, coeff_zero_prod, coeff_divX, zero_add]
  ring

/-- The full source has the same head as its linearized row deformation. -/
theorem source_head_eq_first_jet {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P : ι → R[X]) :
    (sourceProduct S P).coeff (zeroIndices S (fun i => (P i).coeff 0)).card=
      (deformation S (fun i => (P i).coeff 0) (fun i => (P i).coeff 1)).coeff
        (zeroIndices S (fun i => (P i).coeff 0)).card := by
  have h := weighted_source_head_coeff S P 1
  simpa only [one_mul, coeff_one_zero, deformation_head_coeff] using h

/-- The full marked source has the same head as constant markings of the
linearized row deformation. All higher marking terms drop out there. -/
theorem source_marked_head_eq_first_jet {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P W : ι → R[X])
    (hm : 0 < (zeroIndices S (fun i => (P i).coeff 0)).card) :
    (sourceMarked S P W).coeff ((zeroIndices S (fun i => (P i).coeff 0)).card-1)=
      (markedDeformation S (fun i => (P i).coeff 0) (fun i => (P i).coeff 1)
        (fun i => (W i).coeff 0)).coeff
          ((zeroIndices S (fun i => (P i).coeff 0)).card-1) := by
  classical
  rw [markedDeformation_head_coeff S _ _ _ hm]
  simp only [sourceMarked, finsetSum_coeff]
  have hsum : (∑ i ∈ zeroIndices S (fun j => (P j).coeff 0),
      (W i*sourceProduct (S.erase i) P).coeff
        ((zeroIndices S (fun j => (P j).coeff 0)).card-1))=
      ∑ i ∈ S, (W i*sourceProduct (S.erase i) P).coeff
        ((zeroIndices S (fun j => (P j).coeff 0)).card-1) := by
    apply Finset.sum_subset (zeroIndices_subset S _)
    intro i _ hn
    apply weighted_source_coeff_below
    rw [zeroIndices_erase, Finset.erase_eq_of_notMem hn]
    omega
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : (zeroIndices (S.erase i) (fun j => (P j).coeff 0)).card=
      (zeroIndices S (fun j => (P j).coeff 0)).card-1 := by
    rw [zeroIndices_erase, Finset.card_erase_of_mem hi]
  rw [← hc, weighted_source_head_coeff, nonzeroIndices_erase_of_zero S _ hi,
    zeroIndices_erase]

/-- Full deformation of an original interval row under x↦x(1+e*t).
This uses original collision factors, rather than precomputed row jets. -/
noncomputable def rowSource {R : Type*} [CommRing R] (alpha x t : R) (L : ℕ) : R[X] :=
  deformation (Finset.range L) (fun u => x-alpha^u) (fun _ => x*t)

/-- Full original exponent-marked interval source under the same shift. -/
noncomputable def rowMark {R : Type*} [CommRing R] (alpha x t : R) (L : ℕ) : R[X] :=
  markedDeformation (Finset.range L) (fun u => x-alpha^u) (fun _ => x*t)
    (fun u => (u : R)*alpha^u)

/-- The complete row deformation has the original residual as constant. -/
theorem rowSource_coeff_zero {R : Type*} [CommRing R] (alpha x t : R) (L : ℕ) :
    (rowSource alpha x t L).coeff 0=SemiprimeIntervalJet.intervalProduct alpha x L := by
  exact deformation_coeff_zero _ _ _

/-- A first coefficient is the ordinary first derivative evaluated at
zero, without assuming characteristic zero. -/
theorem derivative_eval_zero_eq_coeff_one {R : Type*} [CommRing R] (P : R[X]) :
    P.derivative.eval 0=P.coeff 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  simp

/-- The full row's linear coefficient is its original target slope. -/
theorem rowSource_coeff_one {R : Type*} [CommRing R] (alpha x t : R) (L : ℕ) :
    (rowSource alpha x t L).coeff 1=
      x*SemiprimeIntervalJet.targetDerivative alpha x L*t := by
  rw [← derivative_eval_zero_eq_coeff_one]
  simp only [rowSource, deformation, derivative_prod_finset, derivative_add,
    derivative_C, derivative_C_mul, derivative_X, zero_add, mul_one,
    eval_finsetSum, eval_mul, eval_prod, eval_add, eval_C, eval_X, mul_zero, add_zero]
  simp only [SemiprimeIntervalJet.targetDerivative, SemiprimeIntervalJet.cofactor]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full marking has the original exponent derivative as constant. -/
theorem rowMark_coeff_zero {R : Type*} [CommRing R] (alpha x t : R) (L : ℕ) :
    (rowMark alpha x t L).coeff 0=-SemiprimeIntervalJet.baseDerivative alpha x L := by
  simp only [rowMark, markedDeformation, finsetSum_coeff, coeff_C_mul,
    deformation_coeff_zero, SemiprimeIntervalJet.baseDerivative, neg_neg,
    SemiprimeIntervalJet.cofactor]

/-- The tag variable remains in the coefficient ring of the complete
original interval deformation. The outer variable is the source shift. -/
noncomputable def taggedRowSource {R : Type*} [CommRing R]
    (alpha x a : R) (L : ℕ) : R[X][X] := rowSource (C alpha) (C x) (X-C a) L

/-- Complete original row marking with the identical public tag shift. -/
noncomputable def taggedRowMark {R : Type*} [CommRing R]
    (alpha x a : R) (L : ℕ) : R[X][X] := rowMark (C alpha) (C x) (X-C a) L

/-- The full tagged row has its literal original residual as constant. -/
theorem taggedRowSource_coeff_zero {R : Type*} [CommRing R]
    (alpha x a : R) (L : ℕ) :
    (taggedRowSource alpha x a L).coeff 0=C (SemiprimeIntervalJet.intervalProduct alpha x L) := by
  unfold taggedRowSource
  rw [rowSource_coeff_zero, ← SemiprimeIntervalJet.intervalProduct_map]

/-- The full tagged row has precisely the earlier tagged target slope
as its linear term; all remaining source terms are still retained. -/
theorem taggedRowSource_coeff_one {R : Type*} [CommRing R]
    (alpha x a : R) (L : ℕ) :
    (taggedRowSource alpha x a L).coeff 1=
      C (x*SemiprimeIntervalJet.targetDerivative alpha x L)*(X-C a) := by
  unfold taggedRowSource
  rw [rowSource_coeff_one, ← SemiprimeIntervalJet.targetDerivative_map, map_mul]

/-- Complete row markings retain the earlier original exponent weight. -/
theorem taggedRowMark_coeff_zero {R : Type*} [CommRing R]
    (alpha x a : R) (L : ℕ) :
    (taggedRowMark alpha x a L).coeff 0=C (-SemiprimeIntervalJet.baseDerivative alpha x L) := by
  unfold taggedRowMark
  rw [rowMark_coeff_zero, ← SemiprimeIntervalJet.baseDerivative_map, map_neg]

/-- Complete original collision product under the public row-tag shift.
No row jet or hidden-field collision set is supplied as an input. -/
noncomputable def fullSource {R ι : Type*} [CommRing R]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ) : R[X][X] :=
  sourceProduct S (fun i => taggedRowSource alpha (x i) (a i) L)

/-- Complete exponent-marked companion of the same original source. -/
noncomputable def fullMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ) : R[X][X] :=
  sourceMarked S (fun i => taggedRowSource alpha (x i) (a i) L)
    (fun i => taggedRowMark alpha (x i) (a i) L)

/-- Higher original row terms cancel out of the first possible source
head, over any commutative ring and without residual division. -/
theorem fullSource_head_eq_tagged {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ) :
    (fullSource S alpha x a L).coeff
      (zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card=
      (taggedDeformation S
        (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)
        (fun i => x i*SemiprimeIntervalJet.targetDerivative alpha (x i) L) a).coeff
          (zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card := by
  have h := source_head_eq_first_jet S (fun i => taggedRowSource alpha (x i) (a i) L)
  simpa only [fullSource, taggedRowSource_coeff_zero, taggedRowSource_coeff_one,
    zeroIndices_const, taggedDeformation] using h

/-- Higher source and marking terms cancel out of the marked head too,
with every original exponent weight and nonzero-row scale retained. -/
theorem fullMarked_head_eq_tagged {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ)
    (hm : 0 < (zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card) :
    (fullMarked S alpha x a L).coeff
      ((zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card-1)=
      (taggedMarked S
        (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)
        (fun i => x i*SemiprimeIntervalJet.targetDerivative alpha (x i) L)
        (fun i => -SemiprimeIntervalJet.baseDerivative alpha (x i) L) a).coeff
          ((zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card-1) := by
  have hh : 0 < (zeroIndices S
      (fun i => (taggedRowSource alpha (x i) (a i) L).coeff 0)).card := by
    simpa only [taggedRowSource_coeff_zero, zeroIndices_const] using hm
  have h := source_marked_head_eq_first_jet S
    (fun i => taggedRowSource alpha (x i) (a i) L)
    (fun i => taggedRowMark alpha (x i) (a i) L) hh
  simpa only [fullMarked, taggedRowSource_coeff_zero, taggedRowSource_coeff_one,
    taggedRowMark_coeff_zero, zeroIndices_const, taggedMarked] using h

/-- A GCD of the whole modulus means a zero residual in the public ring. -/
theorem residual_zero_of_gcd_eq_modulus {N : ℕ} [NeZero N] (r : ZMod N)
    (h : N.gcd r.val=N) : r=0 := by
  have hd : N ∣ r.val := by
    have hh := Nat.gcd_dvd_right N r.val
    rwa [h] at hh
  have hz := (ZMod.natCast_eq_zero_iff r.val N).mpr hd
  rwa [ZMod.natCast_zmod_val] at hz

/-- A unit GCD supplies a public unit certificate for the residual. -/
theorem residual_isUnit_of_gcd_eq_one {N : ℕ} [NeZero N] (r : ZMod N)
    (h : N.gcd r.val=1) : IsUnit r := by
  have hc : r.val.Coprime N := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    exact h
  simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime r.val N).mpr hc

/-- If each public GCD is one or the modulus, every nonzero original
residual is a unit. This is a checked classification, not hidden advice. -/
theorem public_gcd_classification {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (r : ι → ZMod N)
    (h : ∀ i ∈ S, N.gcd (r i).val=1 ∨ N.gcd (r i).val=N) :
    ∀ i ∈ S, r i ≠ 0 → IsUnit (r i) := by
  intro i hi hn
  obtain h1 | hN := h i hi
  · exact residual_isUnit_of_gcd_eq_one _ h1
  · exact (hn (residual_zero_of_gcd_eq_modulus _ hN)).elim

/-- With classified unit residuals, public zero rows are exactly the zero
rows in every nontrivial local ring. Proper row GCDs were already exposed. -/
theorem zeroIndices_map_of_units {R F ι : Type*} [CommRing R] [CommRing F] [Nontrivial F]
    (f : R →+* F) (S : Finset ι) (r : ι → R)
    (hu : ∀ i ∈ S, r i ≠ 0 → IsUnit (r i)) :
    zeroIndices S (fun i => f (r i))=zeroIndices S r := by
  classical
  ext i
  simp only [zeroIndices, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hf⟩
    refine ⟨hi, ?_⟩
    by_contra hn
    exact ((hu i hi hn).map f).ne_zero hf
  · rintro ⟨hi, hz⟩
    exact ⟨hi, by rw [hz, map_zero]⟩

/-- Two disjoint product subtrees combine without repeating source rows. -/
theorem sourceProduct_union {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S T : Finset ι) (P : ι → R[X]) (h : Disjoint S T) :
    sourceProduct (S ∪ T) P=sourceProduct S P*sourceProduct T P := by
  exact Finset.prod_union h

/-- One original source row extends the product by one factor. -/
theorem sourceProduct_insert {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P : ι → R[X]) (i : ι) (hi : i ∉ S) :
    sourceProduct (insert i S) P=P i*sourceProduct S P := by
  exact Finset.prod_insert hi

/-- Marked product rule for one source row, with no scalar division. -/
theorem sourceMarked_insert {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (P W : ι → R[X]) (i : ι) (hi : i ∉ S) :
    sourceMarked (insert i S) P W=
      W i*sourceProduct S P+P i*sourceMarked S P W := by
  classical
  calc
    _ = W i*sourceProduct S P+
        ∑ j ∈ S, W j*sourceProduct ((insert i S).erase j) P := by
      simp only [sourceMarked, Finset.sum_insert hi, Finset.erase_insert hi]
    _ = W i*sourceProduct S P+
        ∑ j ∈ S, P i*(W j*sourceProduct (S.erase j) P) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hi hj
      rw [Finset.erase_insert_of_ne hji.symm, sourceProduct_insert _ _ _]
      · ring
      · exact fun hn => hi (Finset.mem_of_mem_erase hn)
    _ = _ := by simp only [sourceMarked, Finset.mul_sum]

/-- A balanced marked product tree needs only the two child products and
markings. This keeps all cofactors without constructing each separately. -/
theorem sourceMarked_union {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S T : Finset ι) (P W : ι → R[X]) (h : Disjoint S T) :
    sourceMarked (S ∪ T) P W=
      sourceMarked S P W*sourceProduct T P+sourceProduct S P*sourceMarked T P W := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty => intro _; simp [sourceMarked, sourceProduct]
  | @insert i S hi ih =>
      intro h
      have hiT : i ∉ T := by
        intro ht
        exact Finset.disjoint_left.mp h (Finset.mem_insert_self _ _) ht
      have hST : Disjoint S T := h.mono_left (Finset.subset_insert _ _)
      rw [Finset.insert_union, sourceMarked_insert _ _ _ _ (by simp [hi, hiT]),
        sourceProduct_union _ _ _ hST, ih hST,
        sourceMarked_insert _ _ _ _ hi, sourceProduct_insert _ _ _ hi]
      ring

/-- Homogeneous row-tag factors of the zero rows alone. -/
noncomputable def homogeneousProduct {R ι : Type*} [CommRing R]
    (Z : Finset ι) (v a : ι → R) : R[X] :=
  sourceProduct Z (fun i => C (v i)*(X-C (a i)))

/-- The same small marked product tree retains each zero-row index weight. -/
noncomputable def homogeneousMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (Z : Finset ι) (v w a : ι → R) : R[X] :=
  sourceMarked Z (fun i => C (v i)*(X-C (a i))) (fun i => C (w i))

/-- Public head construction after row GCD classification. The zero set
is computed in the public ring, never supplied by either hidden field. -/
noncomputable def publicHeadProduct {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v a : ι → R) : R[X] :=
  C (∏ i ∈ S \ zeroIndices S r, r i)*homogeneousProduct (zeroIndices S r) v a

/-- Public marked head from the same classified rows and nonzero scale. -/
noncomputable def publicHeadMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) : R[X] :=
  C (∏ i ∈ S \ zeroIndices S r, r i)*homogeneousMarked (zeroIndices S r) v w a

/-- Homogeneous construction obtains the exact tag-product head without
retaining any lower bivariate deformation coefficients. -/
theorem publicHeadProduct_eq_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v a : ι → R) :
    publicHeadProduct S r v a=
      (taggedDeformation S r v a).coeff (zeroIndices S r).card := by
  rw [tagged_head_coeff]
  simp only [publicHeadProduct, homogeneousProduct, sourceProduct,
    Finset.prod_mul_distrib, ← map_prod, map_mul,
    SemiprimeCartesianCompletion.rootPolynomial]
  ring

/-- The small marked product tree obtains the exact earlier marked head,
including every nonzero original row factor and every index marking. -/
theorem publicHeadMarked_eq_coeff {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (r v w a : ι → R) (hm : 0 < (zeroIndices S r).card) :
    publicHeadMarked S r v w a=
      (taggedMarked S r v w a).coeff ((zeroIndices S r).card-1) := by
  rw [tagged_marked_head_coeff S r v w a hm]
  simp only [publicHeadMarked, homogeneousMarked, sourceMarked, sourceProduct]
  ring

/-- The public GCD trace checks one original residual per source row. -/
noncomputable def rowGcdTrace {ι : Type*} (N : ℕ) (S : Finset ι) (r : ι → ZMod N) : List ℕ :=
  S.toList.map (fun i => N.gcd (r i).val)

/-- Classification costs exactly one GCD query per row. Constructing the
original residuals remains a separate charged stage. -/
theorem rowGcdTrace_length {ι : Type*} (N : ℕ) (S : Finset ι) (r : ι → ZMod N) :
    (rowGcdTrace N S r).length=S.card := by
  simp [rowGcdTrace]

/-- Coefficient-slot budget of a complete binary homogeneous head tree.
Its two outputs at a node with M leaves have at most M+1 and M slots.
This is a representation budget, not a verified machine bit-cost model. -/
def homogeneousTreeSlots : ℕ → ℕ
  | 0 => 3
  | d+1 => 2*homogeneousTreeSlots d+2*(2^(d+1))+1

/-- The homogeneous tree's total slot budget is quasilinear in its leaf
count, unlike the square dense deformation prefix. Padding uses identities. -/
theorem homogeneousTreeSlots_exact (d : ℕ) :
    homogeneousTreeSlots d+1=(2*d+4)*2^d := by
  induction d with
  | zero => norm_num [homogeneousTreeSlots]
  | succ d ih =>
      rw [homogeneousTreeSlots, pow_succ]
      nlinarith

/-- A checked larger representation control compares the full tree's
cumulative slot budget with the dense prefix's allocated capacity. -/
theorem control_tree_slot_budget :
    homogeneousTreeSlots 5=447 ∧
    (densePrefixSlots 32).length+(densePrefixSlots 31).length=1089 ∧
    (447 : ℕ)<1089 := by
  have hT := homogeneousTreeSlots_exact 5
  have hD := dense_combined_prefix_length (m := 32) (by norm_num)
  norm_num at hT hD
  exact ⟨by omega, hD, by norm_num⟩

/-- The homogeneous public head is also the full original source head. -/
theorem public_original_head_eq_fullSource {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ) :
    publicHeadProduct S
      (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)
      (fun i => x i*SemiprimeIntervalJet.targetDerivative alpha (x i) L) a=
      (fullSource S alpha x a L).coeff
        (zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card := by
  rw [publicHeadProduct_eq_coeff, fullSource_head_eq_tagged]

/-- The homogeneous marked head is the full original marked source head. -/
theorem public_original_marked_eq_fullMarked {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ)
    (hm : 0 < (zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card) :
    publicHeadMarked S
      (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)
      (fun i => x i*SemiprimeIntervalJet.targetDerivative alpha (x i) L)
      (fun i => -SemiprimeIntervalJet.baseDerivative alpha (x i) L) a=
      (fullMarked S alpha x a L).coeff
        ((zeroIndices S (fun i => SemiprimeIntervalJet.intervalProduct alpha (x i) L)).card-1) := by
  rw [publicHeadMarked_eq_coeff _ _ _ _ _ hm, fullMarked_head_eq_tagged _ _ _ _ _ hm]

/-- Public residual classification makes its zero count valid in every
nontrivial local ring; the head decoder returns the original exponent. -/
theorem publicHead_original_root {R F ι : Type*} [CommRing R] [CommRing F] [Nontrivial F]
    [DecidableEq ι] (f : R →+* F) (S : Finset ι) (alpha : R) (x a : ι → R) (L : ℕ)
    (hu : ∀ j ∈ S, SemiprimeIntervalJet.intervalProduct alpha (x j) L ≠ 0 →
      IsUnit (SemiprimeIntervalJet.intervalProduct alpha (x j) L))
    {i : ι} (hi : i ∈ S) {k : ℕ} (hk : k<L) (hroot : f (x i)=(f alpha)^k)
    (denom : Rˣ) (hdenom : (denom : R)=
      (publicHeadProduct S (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
        (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L) a).derivative.eval (a i)) :
    f (decodedHead (publicHeadMarked S
      (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
      (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L)
      (fun j => -SemiprimeIntervalJet.baseDerivative alpha (x j) L) a) (a i) denom)=(k : F) := by
  classical
  have hZ := zeroIndices_map_of_units f S
    (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L) hu
  have hm : 0 < (zeroIndices S
      (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)).card := by
    rw [← hZ]
    apply Finset.card_pos.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    change f (SemiprimeIntervalJet.intervalProduct alpha (x i) L)=0
    rw [SemiprimeIntervalJet.intervalProduct_map, hroot]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hk) (sub_self _)
  rw [publicHeadMarked_eq_coeff _ _ _ _ _ hm]
  apply decodedHead_original_row_root f S alpha x a L _ hi hk hroot
  · rw [hZ]
  · rwa [publicHeadProduct_eq_coeff] at hdenom

/-- After checked public classification, different original local
indices yield the same proper integer gcd as the earlier row decoder. -/
theorem publicHead_original_distinct_index_gcd {ι : Type*} [DecidableEq ι]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (S : Finset ι)
    (alpha : ZMod (p*q)) (x a : ι → ZMod (p*q)) (L : ℕ)
    (hu : ∀ j ∈ S, SemiprimeIntervalJet.intervalProduct alpha (x j) L ≠ 0 →
      IsUnit (SemiprimeIntervalJet.intervalProduct alpha (x j) L))
    {i : ι} (hi : i ∈ S) {k l : ℕ} (hk : k<L) (hl : l<L)
    (hLq : L ≤ q) (hkl : k ≠ l)
    (hP : ZMod.castHom (dvd_mul_right p q) (ZMod p) (x i)=
      (ZMod.castHom (dvd_mul_right p q) (ZMod p) alpha)^k)
    (hQ : ZMod.castHom (dvd_mul_left q p) (ZMod q) (x i)=
      (ZMod.castHom (dvd_mul_left q p) (ZMod q) alpha)^l)
    (denom : (ZMod (p*q))ˣ) (hdenom : (denom : ZMod (p*q))=
      (publicHeadProduct S (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
        (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L) a).derivative.eval (a i)) :
    (p*q).gcd (decodedHead (publicHeadMarked S
      (fun j => SemiprimeIntervalJet.intervalProduct alpha (x j) L)
      (fun j => x j*SemiprimeIntervalJet.targetDerivative alpha (x j) L)
      (fun j => -SemiprimeIntervalJet.baseDerivative alpha (x j) L) a)
        (a i) denom-(k : ZMod (p*q))).val=p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  apply SemiprimeIntervalJet.distinct_index_gcd hp hq hk hl hLq hkl
  · exact publicHead_original_root
      (ZMod.castHom (dvd_mul_right p q) (ZMod p)) S alpha x a L hu hi hk hP denom hdenom
  · exact publicHead_original_root
      (ZMod.castHom (dvd_mul_left q p) (ZMod q)) S alpha x a L hu hi hl hQ denom hdenom

/-- The homogeneous public tree recovers the raw checked two-row heads
without retaining a bivariate deformation prefix. -/
theorem control_public_heads :
    publicHeadProduct ({1, 2} : Finset ℕ) controlResidual controlSlope
      (fun i => (i : ZMod 35))=C (9 : ZMod 35)*((X-C 1)*(X-C 2)) ∧
    publicHeadMarked ({1, 2} : Finset ℕ) controlResidual controlSlope controlWeight
      (fun i => (i : ZMod 35))=C (27 : ZMod 35)*X+C 4 := by
  have hm : (zeroIndices ({1, 2} : Finset ℕ) controlResidual).card=2 := by
    rw [control_zero_indices]
    norm_num
  constructor
  · rw [publicHeadProduct_eq_coeff, hm]
    exact control_raw_heads.1
  · rw [publicHeadMarked_eq_coeff _ _ _ _ _ (by rw [hm]; norm_num), hm]
    exact control_raw_heads.2

/-- The same small heads are coefficients of the complete original
collision deformation, not only the earlier first-jet approximation. -/
theorem control_full_source_heads :
    (fullSource ({1, 2} : Finset ℕ) (2 : ZMod 35) controlTargets
      (fun i => (i : ZMod 35)) 3).coeff 2=C (9 : ZMod 35)*((X-C 1)*(X-C 2)) ∧
    (fullMarked ({1, 2} : Finset ℕ) (2 : ZMod 35) controlTargets
      (fun i => (i : ZMod 35)) 3).coeff 1=C (27 : ZMod 35)*X+C 4 := by
  have hm : (zeroIndices ({1, 2} : Finset ℕ) controlResidual).card=2 := by
    rw [control_zero_indices]
    norm_num
  have hQ := public_original_head_eq_fullSource ({1, 2} : Finset ℕ)
    (2 : ZMod 35) controlTargets (fun i => (i : ZMod 35)) 3
  have hH := public_original_marked_eq_fullMarked ({1, 2} : Finset ℕ)
    (2 : ZMod 35) controlTargets (fun i => (i : ZMod 35)) 3
    (by change 0 < (zeroIndices ({1, 2} : Finset ℕ) controlResidual).card; rw [hm]; norm_num)
  change publicHeadProduct _ controlResidual controlSlope _=_ at hQ
  change publicHeadMarked _ controlResidual controlSlope controlWeight _=_ at hH
  change _=(fullSource _ _ _ _ _).coeff (zeroIndices _ controlResidual).card at hQ
  change _=(fullMarked _ _ _ _ _).coeff ((zeroIndices _ controlResidual).card-1) at hH
  rw [hm] at hQ hH
  exact ⟨hQ.symm.trans control_public_heads.1, hH.symm.trans control_public_heads.2⟩

end RiemannGaussian.SemiprimeSourceHead
