/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowSelectionTracked
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-! # Pivot-minor certificates for the actual executed selector

All states below are actual prefixes of `run`. No inverse, selected basis or
minor answer is supplied as a hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace RiemannGaussian.SemiprimeMaterializedSelectionHeight
open scoped BigOperators Matrix
open SemiprimeRowSelectionExecution

/-- Literal retained original-row matrix of a computed prefix. -/
def selectedMatrix {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    Matrix (Fin (run C ids).selected.length) (Fin n) ℤ :=
  fun i v => C ((run C ids).selected.get i) v

/-- Reindex the actual selected rows by the actual active pivot slots. This is
proof-only bookkeeping; it does not choose a new basis or run an inverse. -/
def pivotEquiv {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    Fin (run C ids).selected.length ≃ Active (run C ids) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,active_card]
    exact run_selected_length C ids)

/-- The integer square pivot minor, from selected ORIGINAL rows and columns. -/
def pivotMatrix {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    Matrix (Fin (run C ids).selected.length) (Fin (run C ids).selected.length) ℤ :=
  fun i j => selectedMatrix C ids i (pivotEquiv C ids j).val

/-- The same acquired integer minor viewed in the rational arithmetic field. -/
def rationalPivot {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    Matrix (Fin (run C ids).selected.length) (Fin (run C ids).selected.length) ℚ :=
  fun i j => (pivotMatrix C ids i j : ℚ)

/-- Zero active coordinates determine zero in the actual reduced workspace. -/
theorem zero_of_active_zero {m n : ℕ} (s : State m n) (hg : Good s)
    (row : Row n) (hm : row∈workSpan s)
    (hz : ∀ c : Active s,row c.val=0) : row=0 := by
  have hr := (residual_zero_iff s hg row).mpr hm
  funext v
  have hv := congrFun hr v
  rw [SemiprimeRowSelectionExecution.residual,cacheRow_apply] at hv
  have hs : (∑ c : Fin n,if s.active c then row c*s.rows c v else 0)=0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : s.active c=true
    · simp only [hc,ite_true,hz ⟨c,hc⟩,zero_mul]
    · simp [hc]
  simpa [hs] using hv

/-- Retained original rows of EVERY computed prefix are independent, including
empty/all-zero prefixes. -/
theorem prefix_selected_independent {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) :
    LinearIndependent ℚ (fun i : Fin (run C ids).selected.length =>
      originalRow C ((run C ids).selected.get i)) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin (run C ids).selected.length)=Module.finrank ℚ
    (Submodule.span ℚ (Set.range (fun i => originalRow C ((run C ids).selected.get i))))
  rw [← inputSpan_get,← run_selected_span,Fintype.card_fin]
  exact (run_selected_length C ids).trans
    (workSpan_finrank (run C ids) (run_good C ids)).symm

/-- Restricting the retained originals to the actual pivot columns preserves
independence; injectivity is proved on the computed workspace. -/
theorem pivot_rows_independent {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) :
    LinearIndependent ℚ (fun i j => (pivotMatrix C ids i j : ℚ)) := by
  apply linearIndependent_iff'.mpr
  intro t coeff he k hk
  let row : Row n := ∑ i∈t,coeff i • originalRow C ((run C ids).selected.get i)
  have hm : row∈workSpan (run C ids) := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    rw [run_selected_span]
    exact input_mem_span C _ _ (List.get_mem _ _)
  have hz : ∀ c : Active (run C ids),row c.val=0 := by
    intro c
    have hv := congrFun he ((pivotEquiv C ids).symm c)
    simpa [row,pivotMatrix,selectedMatrix,originalRow] using hv
  have hr := zero_of_active_zero _ (run_good C ids) row hm hz
  exact (linearIndependent_iff'.mp (prefix_selected_independent C ids)) t coeff hr k hk

/-- The computed pivot minor is genuinely nonsingular. -/
theorem pivot_det_ne_zero {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) :
    (rationalPivot C ids).det≠0 := by
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row (pivot_rows_independent C ids))

/-- Active computed rows, now reindexed by retained-original positions. -/
def workingMatrix {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    Matrix (Fin (run C ids).selected.length) (Fin n) ℚ :=
  fun i v => (run C ids).rows (pivotEquiv C ids i).val v

/-- The actual working matrix has identity entries at its pivot columns. -/
theorem working_pivot {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (i j : Fin (run C ids).selected.length) :
    workingMatrix C ids i (pivotEquiv C ids j).val=if i=j then 1 else 0 := by
  rw [workingMatrix,(run_good C ids).pivot _ _ (pivotEquiv C ids i).property
    (pivotEquiv C ids j).property]
  have he : (pivotEquiv C ids i).val=(pivotEquiv C ids j).val ↔ i=j := by
    constructor
    · intro h; exact (pivotEquiv C ids).injective (Subtype.ext h)
    · intro h; subst j; rfl
  simp only [he]

/-- The actual selected original matrix equals pivot minor times ACTUAL
working matrix. This is a consequence, not a supplied linear-system answer. -/
theorem pivot_mul_working {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) :
    rationalPivot C ids * workingMatrix C ids=
      fun i v => (selectedMatrix C ids i v : ℚ) := by
  ext i v
  let row : Row n := ∑ j : Fin (run C ids).selected.length,
    (pivotMatrix C ids i j : ℚ) • workingMatrix C ids j
  have hm : row∈workSpan (run C ids) := by
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (row_mem_workSpan _ _)
  have hs : (fun v => (selectedMatrix C ids i v : ℚ))∈workSpan (run C ids) := by
    rw [run_selected_span]
    exact input_mem_span C _ _ (List.get_mem _ _)
  have hz : row-(fun v => (selectedMatrix C ids i v : ℚ))=0 := by
    apply zero_of_active_zero _ (run_good C ids) _ (Submodule.sub_mem _ hm hs)
    intro c
    obtain ⟨j,rfl⟩ := (pivotEquiv C ids).surjective c
    simp only [Pi.sub_apply,row,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      working_pivot,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      pivotMatrix,sub_self]
  have hrow := sub_eq_zero.mp hz
  simpa only [row,Matrix.mul_apply,rationalPivot,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
    congrFun hrow v

/-- Every actual working entry is a Cramer ratio of original integer minors. -/
theorem working_cramer {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (i : Fin (run C ids).selected.length) (v : Fin n) :
    workingMatrix C ids i v=
      (rationalPivot C ids).cramer
        (fun j => (selectedMatrix C ids j v : ℚ)) i /
        (rationalPivot C ids).det := by
  let A : Matrix (Fin (run C ids).selected.length) (Fin (run C ids).selected.length) ℚ :=
    fun i j => (pivotMatrix C ids i j : ℚ)
  let x := fun i => workingMatrix C ids i v
  let b := fun j => (selectedMatrix C ids j v : ℚ)
  have hx : A *ᵥ x=b := by
    funext j
    exact congrFun (congrFun (pivot_mul_working C ids) j) v
  have hc : A.cramer b=A.det • x := by
    rw [← hx,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec]
  have hv := congrFun hc i
  have hd : A.det≠0 := pivot_det_ne_zero C ids
  change x i=A.cramer b i/A.det
  rw [hv,Pi.smul_apply,smul_eq_mul]
  exact (mul_div_cancel_left₀ (x i) hd).symm

/-- Common integer denominator of all stored active entries in this prefix. -/
def pivotDenominator {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) : ℤ :=
  (pivotMatrix C ids).det

/-- Integer Cramer numerator obtained by replacing a pivot column with one
actual original coefficient column. -/
def pivotNumerator {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (i : Fin (run C ids).selected.length) (v : Fin n) : ℤ :=
  ((pivotMatrix C ids).updateCol i (fun j => selectedMatrix C ids j v)).det

/-- Integer and rational views of the acquired pivot determinant agree. -/
theorem cast_pivotDenominator {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    (pivotDenominator C ids : ℚ)=(rationalPivot C ids).det := by
  exact (Int.castRingHom ℚ).map_det (pivotMatrix C ids)

/-- The actual integer pivot determinant is nonzero. -/
theorem pivotDenominator_ne_zero {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    pivotDenominator C ids≠0 := by
  intro h
  have he := cast_pivotDenominator C ids
  rw [h,Int.cast_zero] at he
  exact pivot_det_ne_zero C ids he.symm

/-- Cramer numerators too are casts of ORIGINAL integer minors. -/
theorem cast_pivotNumerator {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m))
    (i : Fin (run C ids).selected.length) (v : Fin n) :
    (pivotNumerator C ids i v : ℚ)=(rationalPivot C ids).cramer
      (fun j => (selectedMatrix C ids j v : ℚ)) i := by
  rw [Matrix.cramer_apply]
  have he : (Int.castRingHom ℚ).mapMatrix
      ((pivotMatrix C ids).updateCol i (fun j => selectedMatrix C ids j v))=
      (rationalPivot C ids).updateCol i (fun j => (selectedMatrix C ids j v : ℚ)) := by
    ext j k
    simp [RingHom.mapMatrix,Matrix.map_apply,Matrix.updateCol_apply,rationalPivot]
  change (Int.castRingHom ℚ) ((pivotMatrix C ids).updateCol i (fun j => selectedMatrix C ids j v)).det=_
  rw [RingHom.map_det,he]

/-- Every stored active entry has a proved integer-minor representation with
one denominator shared by the entire actual prefix state. -/
theorem working_integer_ratio {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (i : Fin (run C ids).selected.length) (v : Fin n) :
    workingMatrix C ids i v=(pivotNumerator C ids i v : ℚ)/(pivotDenominator C ids : ℚ) := by
  rw [cast_pivotNumerator,cast_pivotDenominator]
  exact working_cramer C ids i v

/-- Elementary Leibniz envelope for minors; its logarithm is polynomial in
matrix order and input bit height. -/
def minorBound (order height : ℕ) : ℕ := order.factorial*height^order

/-- Determinant magnitudes of bounded integer matrices obey the explicit
factorial-power envelope, including the empty matrix. -/
theorem integer_det_bound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (height : ℕ)
    (hA : ∀ i j,|A i j|≤(height : ℤ)) : A.det.natAbs≤ minorBound r height := by
  have hd := Matrix.det_le (abv := AbsoluteValue.abs) hA
  apply Int.ofNat_le.mp
  rw [Int.natCast_natAbs]
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul,minorBound,
    Nat.cast_mul,Nat.cast_pow] using hd

/-- The acquired common denominator satisfies the original-input minor bound. -/
theorem pivotDenominator_bound {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (height : ℕ) (hC : ∀ j v,|C j v|≤(height : ℤ)) :
    (pivotDenominator C ids).natAbs≤ minorBound (run C ids).selected.length height := by
  apply integer_det_bound
  intro i j
  exact hC _ _

/-- Replacing a column does not enlarge the ORIGINAL coefficient bound. -/
theorem pivotNumerator_bound {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (height : ℕ) (hC : ∀ j v,|C j v|≤(height : ℤ))
    (i : Fin (run C ids).selected.length) (v : Fin n) :
    (pivotNumerator C ids i v).natAbs≤ minorBound (run C ids).selected.length height := by
  apply integer_det_bound
  intro j k
  rw [Matrix.updateCol_apply]
  split_ifs <;> exact hC _ _

/-- Reducing a proved integer fraction cannot increase numerator magnitude or
denominator; no arbitrary circuit-height hypothesis is used. -/
theorem reduced_fraction_bounds (q : ℚ) (a b : ℤ) (hb : b≠0)
    (he : q=(a : ℚ)/(b : ℚ)) : q.num.natAbs≤a.natAbs ∧ q.den≤b.natAbs := by
  obtain ⟨c,ha,hb'⟩ := Rat.num_den_mk hb (by simpa only [Rat.divInt_eq_div] using he)
  have hc : c≠0 := by intro h; simp [h] at hb'; exact hb hb'
  have hcpos : 1≤c.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc)
  have han : a.natAbs=c.natAbs*q.num.natAbs := by rw [ha,Int.natAbs_mul]
  have hbn : b.natAbs=c.natAbs*q.den := by rw [hb',Int.natAbs_mul,Int.natAbs_natCast]
  constructor
  · have h := Nat.mul_le_mul_right q.num.natAbs hcpos
    simpa only [one_mul,← han] using h
  · have h := Nat.mul_le_mul_right q.den hcpos
    simpa only [one_mul,← hbn] using h

/-- Canonical rational numerator AND denominator of every actual stored active
entry have polynomial-bit factorial-power bounds from original integers. -/
theorem working_canonical_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (height : ℕ) (hC : ∀ j v,|C j v|≤(height : ℤ))
    (i : Fin (run C ids).selected.length) (v : Fin n) :
    (workingMatrix C ids i v).num.natAbs≤ minorBound (run C ids).selected.length height ∧
    (workingMatrix C ids i v).den≤ minorBound (run C ids).selected.length height := by
  have hr := reduced_fraction_bounds _ _ _ (pivotDenominator_ne_zero C ids) (working_integer_ratio C ids i v)
  exact ⟨hr.1.trans (pivotNumerator_bound C ids height hC i v),
    hr.2.trans (pivotDenominator_bound C ids height hC)⟩

/-- A polynomial binary exponent bounds the entire minor envelope whenever the
original integer coefficients fit b bits. This is not exponential in a circuit
size: the exponent is the quadratic expression r*(r+b). -/
theorem minorBound_le_two_pow (r height bits : ℕ) (hh : height≤2^bits) :
    minorBound r height≤2^(r*(r+bits)) := by
  have hf := Nat.factorial_le_pow r
  have hr : r≤2^r := (Nat.lt_two_pow_self (n := r)).le
  have hp := Nat.pow_le_pow_left hr r
  have hw := Nat.pow_le_pow_left hh r
  calc
    minorBound r height≤(2^r)^r*(2^bits)^r := Nat.mul_le_mul (hf.trans hp) hw
    _=2^(r*(r+bits)) := by rw [← Nat.pow_mul,← Nat.pow_mul,← Nat.pow_add]; congr 1; ring

/-- Explicit canonical numerator/denominator binary bounds for the ACTUAL
stored prefix, with original-coefficient bit height as the only data bound. -/
theorem working_binary_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ))
    (i : Fin (run C ids).selected.length) (v : Fin n) :
    (workingMatrix C ids i v).num.natAbs≤2^((run C ids).selected.length*((run C ids).selected.length+bits)) ∧
    (workingMatrix C ids i v).den≤2^((run C ids).selected.length*((run C ids).selected.length+bits)) := by
  have h := working_canonical_bounds C ids (2^bits) hC i v
  have hb := minorBound_le_two_pow (run C ids).selected.length (2^bits) bits le_rfl
  exact ⟨h.1.trans hb,h.2.trans hb⟩

/-- The actual retained rank never exceeds the number of original columns. -/
theorem prefix_rank_le_columns {m n : ℕ} (C : Fin m → Fin n → ℤ) (ids : List (Fin m)) :
    (run C ids).selected.length≤n := by
  rw [run_selected_length]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- ALL stored row slots, not just an abstract basis, have polynomial binary
height after every actual prefix. Inactive slots are the literal zero row. -/
theorem state_binary_bounds {m n : ℕ} (C : Fin m → Fin n → ℤ)
    (ids : List (Fin m)) (bits : ℕ) (hC : ∀ j v,|C j v|≤(2^bits : ℕ))
    (c v : Fin n) :
    ((run C ids).rows c v).num.natAbs≤2^(n*(n+bits)) ∧
    ((run C ids).rows c v).den≤2^(n*(n+bits)) := by
  by_cases hc : (run C ids).active c=true
  · let i := (pivotEquiv C ids).symm ⟨c,hc⟩
    have he : workingMatrix C ids i v=(run C ids).rows c v := by
      exact congrArg (fun z : Active (run C ids) => (run C ids).rows z.val v)
        ((pivotEquiv C ids).apply_symm_apply ⟨c,hc⟩)
    have h := working_binary_bounds C ids bits hC i v
    have hlen := prefix_rank_le_columns C ids
    have hb : 2^((run C ids).selected.length*((run C ids).selected.length+bits))≤2^(n*(n+bits)) := by
      gcongr
    rw [he] at h
    exact ⟨h.1.trans hb,h.2.trans hb⟩
  · have hz := (run_good C ids).inactive c (Bool.eq_false_iff.mpr hc)
    rw [hz]
    simp only [Pi.zero_apply,Rat.num_zero,Int.natAbs_zero,Rat.den_zero]
    constructor
    · exact Nat.zero_le _
    · exact Nat.one_le_two_pow

end RiemannGaussian.SemiprimeMaterializedSelectionHeight
