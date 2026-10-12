/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeScatteredColumnObstruction
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Cleared Cauchy determinants erase the original collision mask

The division-free row clearing of a square Cauchy matrix is a matrix of
deleted-node products. Unit differences within each node set force its
determinant to be a unit, regardless of cross-set collisions. Original
distinct integer seed offsets and distinct original babies have these
unit differences on the actual long branch. Repeated seed offsets instead
give identical rows and a globally zero determinant.

This is an arithmetic obstruction to that scalar acquisition route, not
a complexity lower bound for arbitrary implicit circuits or resultants.
-/

namespace RiemannGaussian.SemiprimeCauchyAcquisitionObstruction

open scoped BigOperators
open Polynomial Matrix SemiprimeDenseRowCarries SemiprimeGlobalPhaseCancellation
open SemiprimeQuotientRows SemiprimeLocalOrderRouting SemiprimeCentreFreeCover
open SemiprimeSeedSumAcquisition SemiprimeIntervalJet SemiprimeBulkNorm

/-- The literal row-cleared Cauchy matrix; no cross-set inverse is used. -/
noncomputable def clearedCauchy {R : Type*} [CommRing R] {n : ℕ}
    (x y : Fin n→R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ∏ l∈Finset.univ.erase j, (x i-y l)

/-- Evaluation factorization needs a common degree cap, not triangular polynomial degrees. -/
theorem polynomial_eval_matrix_factor {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n→R) (P : Fin n→R[X]) (hdeg : ∀ j, (P j).natDegree<n) :
    Matrix.of (fun i j => (P j).eval (v i))=
      vandermonde v*Matrix.of (fun i j : Fin n => (P j).coeff i) := by
  ext i j
  simp_rw [Matrix.mul_apply,Matrix.of_apply,eval,eval₂_eq_sum]
  simp only [Matrix.vandermonde]
  have hs : (P j).support⊆Finset.range n := supp_subset_range (hdeg j)
  rw [Polynomial.sum_eq_of_subset _ (fun k => zero_mul ((v i)^k)) hs,
    ←Fin.sum_univ_eq_sum_range]
  congr 1
  ext k
  rw [mul_comm,Matrix.of_apply,RingHom.id_apply]

/-- Pairwise unit gaps make the Vandermonde determinant a unit over any commutative ring. -/
theorem vandermonde_det_isUnit {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n→R) (hv : ∀ i j, i≠j→IsUnit (v i-v j)) :
    IsUnit (vandermonde v).det := by
  rw [det_vandermonde]
  apply IsUnit.prod_iff.mpr
  intro i _
  apply IsUnit.prod_iff.mpr
  intro j hj
  exact hv j i (Finset.mem_Ioi.mp hj).ne'

/-- Clearing gives a unit even if some original Cauchy denominators are nonunits. -/
theorem clearedCauchy_det_isUnit {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (x y : Fin n→R) (hx : ∀ i j, i≠j→IsUnit (x i-x j))
    (hy : ∀ i j, i≠j→IsUnit (y i-y j)) : IsUnit (clearedCauchy x y).det := by
  classical
  let P : Fin n→R[X] := fun j => ∏ l∈Finset.univ.erase j, (X-C (y l))
  let H : Matrix (Fin n) (Fin n) R := fun i j => (P j).coeff i
  have hdeg (j : Fin n) : (P j).natDegree<n := by
    have hd := natDegree_finsetProd_X_sub_C_eq_card (Finset.univ.erase j) y
    change (P j).natDegree=(Finset.univ.erase j).card at hd
    simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,
      Fintype.card_fin] at hd
    have hn := j.isLt
    omega
  have heval (v : Fin n→R) : clearedCauchy v y=vandermonde v*H := by
    calc
      clearedCauchy v y=Matrix.of (fun i j => (P j).eval (v i)) := by
        ext i j
        simp only [clearedCauchy,P,Matrix.of_apply,eval_prod,eval_sub,eval_X,eval_C]
      _=vandermonde v*Matrix.of (fun i j : Fin n => (P j).coeff i) :=
        polynomial_eval_matrix_factor v P hdeg
      _=vandermonde v*H := by congr 1
  have hdiag : clearedCauchy y y=diagonal (fun j => ∏ l∈Finset.univ.erase j, (y j-y l)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [clearedCauchy]
    · have hz : (clearedCauchy y y) i j=0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩)
        simp
      simp [hz,diagonal,hij]
  have hu : IsUnit (clearedCauchy y y).det := by
    rw [hdiag,det_diagonal]
    apply IsUnit.prod_iff.mpr
    intro j _
    apply IsUnit.prod_iff.mpr
    intro l hl
    exact hy j l (Finset.mem_erase.mp hl).1.symm
  rw [heval y,det_mul] at hu
  rw [heval x,det_mul]
  exact (vandermonde_det_isUnit x hx).mul (isUnit_of_mul_isUnit_right hu)

/-- Literal reciprocal certificates identify the fraction determinant with its row clearing. -/
theorem clearedCauchy_eq_row_scaling {R : Type*} [CommRing R] {n : ℕ}
    (x y : Fin n→R) (A : Matrix (Fin n) (Fin n) R)
    (hinv : ∀ i j, (x i-y j)*A i j=1) :
    clearedCauchy x y=diagonal (fun i => ∏ j, (x i-y j))*A := by
  classical
  ext i j
  rw [diagonal_mul]
  change _=(∏ l, (x i-y l))*A i j
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ j),mul_assoc,hinv,mul_one]
  rfl

/-- Row factors retained by a full rectangular clearing are exactly an unpaid norm channel. -/
theorem row_scaled_clearedCauchy_unit_iff {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (x y c : Fin n→R) (hx : ∀ i j, i≠j→IsUnit (x i-x j))
    (hy : ∀ i j, i≠j→IsUnit (y i-y j)) :
    IsUnit (diagonal c*clearedCauchy x y).det ↔ IsUnit (∏ i, c i) := by
  rw [det_mul,det_diagonal]
  exact ⟨fun h => isUnit_of_mul_isUnit_left h,
    fun h => h.mul (clearedCauchy_det_isUnit x y hx hy)⟩

/-- A reciprocal certificate cannot exist over a nonunit cross difference. -/
theorem nonunit_cross_has_no_reciprocal {R : Type*} [CommRing R] (z : R)
    (hz : ¬IsUnit z) : ¬∃ a : R, z*a=1 := by
  rintro ⟨a,ha⟩
  exact hz (isUnit_iff_exists_inv.mpr ⟨a,ha⟩)

/-- Any extension specializing to a nonunit still has no reciprocal for that lift. -/
theorem specialization_nonunit_has_no_reciprocal {R A : Type*} [CommRing R] [CommRing A]
    (f : A→+*R) (z : A) (hz : ¬IsUnit (f z)) : ¬∃ a : A, z*a=1 := by
  rintro ⟨a,ha⟩
  apply nonunit_cross_has_no_reciprocal (f z) hz
  exact ⟨f a,by rw [←map_mul,ha,map_one]⟩

/-- A nonzero signed exponent gap below the order cannot vanish in the value ring. -/
theorem zpow_short_gap_ne_zero {R : Type*} [CommRing R] (u : Rˣ) (a b : ℤ)
    (hne : a≠b) (hbound : (a-b).natAbs<orderOf u) :
    ((u^a : Rˣ) : R)-((u^b : Rˣ) : R)≠0 := by
  intro hz
  have he : u^a=u^b := Units.ext (sub_eq_zero.mp hz)
  have hd := orderOf_dvd_sub_iff_zpow_eq_zpow.mpr he
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    (by simpa only [Int.natAbs_natCast] using hbound)
  exact hne (sub_eq_zero.mp hzero)

/-- Distinct literal original offsets have unit differences in both hidden fields. -/
theorem original_target_difference_isUnit {p q m j k : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hj : 1≤j) (hjm : j<m) (hk : 1≤k) (hkm : k<m)
    (hne : seedOffset (p*q) m j≠seedOffset (p*q) m k) :
    IsUnit (((progressionSeed (projectedUnit g m) (p*q) m j).step : ZMod (p*q))-
      ((progressionSeed (projectedUnit g m) (p*q) m k).step : ZMod (p*q))) := by
  have hjcop : j.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hjm)).symm
  have hkcop : k.Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkm)).symm
  rw [seed_step_offset _ hmprime.pos hjcop,seed_step_offset _ hmprime.pos hkcop]
  let a : ℤ := (p*q : ℕ)+seedOffset (p*q) m j
  let b : ℤ := (p*q : ℕ)+seedOffset (p*q) m k
  have hab : a≠b := by dsimp only [a,b]; omega
  have hb : (a-b).natAbs≤4*m^2 := by
    have hδj := seedOffset_bounds (N:=p*q) (by omega) hj hjm
    have hδk := seedOffset_bounds (N:=p*q) (by omega) hk hkm
    have h : |a-b|≤4*(m : ℤ)^2 := by
      dsimp only [a,b]
      rw [abs_le]
      constructor <;> omega
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hP : (a-b).natAbs<orderOf (leftUnit (projectedUnit g m)) := by
    have h := hlong.2.2.2.1.1
    nlinarith only [hb,h]
  have hQ : (a-b).natAbs<orderOf (rightUnit (projectedUnit g m)) := by
    have h := hlong.2.2.2.1.2
    nlinarith only [hb,h]
  apply isUnit_of_prime_reductions hp hq
  · have h := zpow_short_gap_ne_zero (leftUnit (projectedUnit g m)) a b hab hP
    simpa [leftUnit,←map_zpow,Units.coe_map,map_sub,a,b] using h
  · have h := zpow_short_gap_ne_zero (rightUnit (projectedUnit g m)) a b hab hQ
    simpa [rightUnit,←map_zpow,Units.coe_map,map_sub,a,b] using h

/-- Different original baby indices have unit differences on the actual long branch. -/
theorem original_baby_difference_isUnit {p q m r t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (hr : r<seedLength m) (ht : t<seedLength m) (hne : r≠t) :
    IsUnit (((seedBase (projectedUnit g m) m)^r : ZMod (p*q))-
      ((seedBase (projectedUnit g m) m)^t : ZMod (p*q))) := by
  have hperiods := long_seed_interval_periods hm g hlong
  apply isUnit_of_prime_reductions hp hq
  · intro hz
    rw [map_sub,map_pow,map_pow,sub_eq_zero] at hz
    exact hne (pow_injOn_Iio_orderOf (hr.trans_le hperiods.1) (ht.trans_le hperiods.1) hz)
  · intro hz
    rw [map_sub,map_pow,map_pow,sub_eq_zero] at hz
    exact hne (pow_injOn_Iio_orderOf (hr.trans_le hperiods.2) (ht.trans_le hperiods.2) hz)

/-- Every square block with deduplicated original offsets clears to a unit determinant. -/
theorem actual_clearedCauchy_det_isUnit {p q m s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (tags columns : Fin s→ℕ) (htags : ∀ i, 1≤tags i ∧ tags i<m)
    (hcolumns : ∀ i, columns i<seedLength m)
    (hoffsets : Function.Injective (fun i => seedOffset (p*q) m (tags i)))
    (hcolinj : Function.Injective columns) :
    IsUnit (clearedCauchy
      (fun i => ((progressionSeed (projectedUnit g m) (p*q) m (tags i)).step : ZMod (p*q)))
      (fun i => ((seedBase (projectedUnit g m) m)^(columns i) : ZMod (p*q)))).det := by
  let : Fact (1<p*q) := ⟨by nlinarith [hp.one_lt,hq.one_lt]⟩
  apply clearedCauchy_det_isUnit
  · intro i j hij
    exact original_target_difference_isUnit hp hq hm hmprime g hlong
      (htags i).1 (htags i).2 (htags j).1 (htags j).2 (by intro he; exact hij (hoffsets he))
  · intro i j hij
    exact original_baby_difference_isUnit hp hq hm g hlong (hcolumns i) (hcolumns j)
      (by intro he; exact hij (hcolinj he))

/-- A repeated public integer offset gives identical cleared rows and a globally zero scalar. -/
theorem equal_offsets_clearedCauchy_det_zero {p q m s : ℕ}
    (hmprime : m.Prime) (g : (ZMod (p*q))ˣ) (tags : Fin s→ℕ)
    (htags : ∀ i, 1≤tags i ∧ tags i<m) (y : Fin s→ZMod (p*q))
    (i j : Fin s) (hij : i≠j)
    (he : seedOffset (p*q) m (tags i)=seedOffset (p*q) m (tags j)) :
    (clearedCauchy
      (fun k => ((progressionSeed (projectedUnit g m) (p*q) m (tags k)).step : ZMod (p*q))) y).det=0 := by
  have hi : (tags i).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (htags i).1) (htags i).2)).symm
  have hj : (tags j).Coprime m :=
    (hmprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (htags j).1) (htags j).2)).symm
  apply Matrix.det_zero_of_row_eq hij
  ext k
  simp only [clearedCauchy,seed_step_offset _ hmprime.pos hi,
    seed_step_offset _ hmprime.pos hj,he]

/-- Such a scalar always has gcd one or N; offset repetition determines the branch. -/
theorem actual_clearedCauchy_gcd_dichotomy {p q m s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hm : 4≤m) (hmprime : m.Prime)
    (g : (ZMod (p*q))ˣ) (hlong : LongData g m)
    (tags columns : Fin s→ℕ) (htags : ∀ i, 1≤tags i ∧ tags i<m)
    (hcolumns : ∀ i, columns i<seedLength m) (hcolinj : Function.Injective columns) :
    let d := (clearedCauchy
      (fun i => ((progressionSeed (projectedUnit g m) (p*q) m (tags i)).step : ZMod (p*q)))
      (fun i => ((seedBase (projectedUnit g m) m)^(columns i) : ZMod (p*q)))).det
    (p*q).gcd d.val=1 ∨ (p*q).gcd d.val=p*q := by
  classical
  let : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  dsimp only
  by_cases hoffsets : Function.Injective (fun i => seedOffset (p*q) m (tags i))
  · exact Or.inl ((gcd_one_iff_unit _).mpr
      (actual_clearedCauchy_det_isUnit hp hq hm hmprime g hlong tags columns htags hcolumns hoffsets hcolinj))
  · obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp hoffsets
    right
    rw [equal_offsets_clearedCauchy_det_zero hmprime g tags htags _ i j hij he]
    simp

end RiemannGaussian.SemiprimeCauchyAcquisitionObstruction
