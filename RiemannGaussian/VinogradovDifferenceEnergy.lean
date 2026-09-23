/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMixedMoments
import Mathlib.Data.Nat.ModEq

/-!
# Exact residue energy and its truncated positive differences

The residue-class energy is expanded before any norm is taken on a
difference sum. Each positive displacement is an actual multiple of the
modulus, with the original endpoint mask. This is the finite input to the
classical mixed-moment differencing inequality.
-/

namespace RiemannGaussian.VinogradovDifferenceEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus VinogradovPartitionEnergy VinogradovShiftedMoment

/-- The literal sum of the energies in all colour classes. -/
def colourEnergy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (label : ι → κ) (f : ι → ℂ) : ℝ :=
  ∑ c, ‖∑ i, if label i = c then f i else 0‖ ^ 2

/-- Expanding all colour classes retains precisely the pairs with equal labels. -/
theorem colourEnergy_eq_pairs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (label : ι → κ) (f : ι → ℂ) :
    colourEnergy label f =
      ∑ i, ∑ j, if label i = label j then (f i * conj (f j)).re else 0 := by
  have he (c : κ) : ‖∑ i, if label i = c then f i else 0‖ ^ 2 =
      ∑ i, ∑ j, ((if label i = c then f i else 0) *
        conj (if label j = c then f j else 0)).re := by
    calc
      _ = ((∑ i, if label i = c then f i else 0) *
          conj (∑ i, if label i = c then f i else 0)).re := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
        exact Finset.sum_comm
  unfold colourEnergy
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (label i)]
  · by_cases h : label i = label j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro c hc hne
    simp [Ne.symm hne]
  · simp

private theorem symmetric_pairs (P : ℕ) (g : ℕ → ℕ → ℝ)
    (hg : ∀ i j, g i j = g j i) :
    (∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P, g i j) =
      (∑ i ∈ Finset.range P, g i i) +
        2 * ∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P,
          if i < j then g j i else 0 := by
  have he (i j : ℕ) : g i j =
      (if i = j then g i i else 0) +
      (if i < j then g j i else 0) + (if j < i then g i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt, hg i j]
    · subst j
      simp
    · simp [h, h.ne', h.not_gt]
  have hd : (∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P,
      if i = j then g i i else 0) = ∑ i ∈ Finset.range P, g i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hl : (∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P,
      if j < i then g i j else 0) =
      ∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P,
        if i < j then g j i else 0 := Finset.sum_comm
  calc
    _ = ∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P,
        ((if i = j then g i i else 0) +
          (if i < j then g j i else 0) + (if j < i then g i j else 0)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib, hd, hl]
      ring

/-- The positive same-residue pairs have exactly the displacements
`q,2q,...,floor(P/q)q`, with the literal endpoint inequality. -/
theorem positive_pairs_eq_shifts {P q : ℕ} (hq : 0 < q) (i : ℕ)
    (g : ℕ → ℕ → ℂ) :
    (∑ j ∈ (Finset.range P).filter (fun j => i < j ∧ i % q = j % q), g j i) =
      ∑ h ∈ (Finset.range (P / q)).filter (fun h => i + (h + 1) * q < P),
        g (i + (h + 1) * q) i := by
  symm
  refine Finset.sum_bij (fun h _ => i + (h + 1) * q) ?_ ?_ ?_ ?_
  · intro h hh
    have hb := (Finset.mem_filter.mp hh).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, ?_, ?_⟩
    · have hp : 0 < (h + 1) * q := Nat.mul_pos (by omega) hq
      omega
    · simp
  · intro h hh k hk he
    nlinarith
  · intro j hj
    obtain ⟨hjP, hij, hmod⟩ := Finset.mem_filter.mp hj
    have hdvd : q ∣ j - i := (Nat.modEq_iff_dvd' hij.le).mp hmod
    have hmul := Nat.div_mul_cancel hdvd
    have hpos : 1 ≤ (j - i) / q := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      rw [hz, zero_mul] at hmul
      omega
    have hle : (j - i) / q ≤ P / q :=
      Nat.div_le_div_right (by have := Finset.mem_range.mp hjP; omega)
    refine ⟨(j - i) / q - 1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · rw [Nat.sub_add_cancel hpos, hmul, Nat.add_sub_cancel' hij.le]
        exact Finset.mem_range.mp hjP
    · rw [Nat.sub_add_cancel hpos, hmul, Nat.add_sub_cancel' hij.le]
  · intro h hh
    rfl

/-- The residue energy of the actual interval `1,...,P`. -/
def residueEnergy {d : Type*} [Fintype d] (P q : ℕ) (hq : 0 < q)
    (v : ℕ → d → ℤ) (theta : UnitAddTorus d) : ℝ :=
  colourEnergy (fun x : Fin P => (⟨x.val % q, Nat.mod_lt _ hq⟩ : Fin q))
    (fun x => mFourier (v (x.val + 1)) theta)

/-- The entire vector of literal finite differences. -/
def differenceFrequency {d : Type*} (P h : ℕ) (v : ℕ → d → ℤ)
    (x : Fin P) : d → ℤ := v (x.val + h + 1) - v (x.val + 1)

/-- The exact upper endpoint mask after positive displacement `h`. -/
def boundaryWeight (P h : ℕ) (x : Fin P) : ℂ := if x.val + h < P then 1 else 0

/-- Every endpoint mask is bounded by one. -/
theorem boundaryWeight_bound (P h : ℕ) (x : Fin P) : ‖boundaryWeight P h x‖ ≤ 1 := by
  unfold boundaryWeight
  split <;> simp

/-- The original truncated difference sum. -/
def differenceSum {d : Type*} [Fintype d] (P h : ℕ) (v : ℕ → d → ℤ)
    (theta : UnitAddTorus d) : ℂ :=
  polynomial (differenceFrequency P h v) (boundaryWeight P h) theta

/-- Residue energy is pointwise nonnegative. -/
theorem residueEnergy_nonneg {d : Type*} [Fintype d] (P q : ℕ) (hq : 0 < q)
    (v : ℕ → d → ℤ) (theta : UnitAddTorus d) :
    0 ≤ residueEnergy P q hq v theta := by
  unfold residueEnergy colourEnergy
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- All residue energies are continuous. -/
theorem continuous_residueEnergy {d : Type*} [Fintype d] (P q : ℕ) (hq : 0 < q)
    (v : ℕ → d → ℤ) : Continuous (residueEnergy P q hq v) := by
  unfold residueEnergy colourEnergy
  apply continuous_finsetSum
  intro c hc
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_finsetSum
  intro i hi
  split_ifs <;> fun_prop

/-- Truncated difference sums are continuous on the full original torus. -/
theorem continuous_differenceSum {d : Type*} [Fintype d] (P h : ℕ)
    (v : ℕ → d → ℤ) : Continuous (differenceSum P h v) := continuous_polynomial _ _

/-- Exact signed expansion: the diagonal is `P`, and each positive
residue displacement keeps its complete truncated complex correlation. -/
theorem residueEnergy_eq_differences {d : Type*} [Fintype d]
    (P q : ℕ) (hq : 0 < q) (v : ℕ → d → ℤ) (theta : UnitAddTorus d) :
    residueEnergy P q hq v theta = (P : ℝ) +
      2 * ∑ h : Fin (P / q), (differenceSum P ((h.val + 1) * q) v theta).re := by
  let f (i : ℕ) : ℂ := mFourier (v (i + 1)) theta
  let g (i j : ℕ) : ℝ := if i % q = j % q then (f i * conj (f j)).re else 0
  have hg (i j : ℕ) : g i j = g j i := by
    dsimp [g]
    by_cases h : i % q = j % q
    · simp only [h, if_true]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp [h, Ne.symm h]
  have hpairs : residueEnergy P q hq v theta =
      ∑ i ∈ Finset.range P, ∑ j ∈ Finset.range P, g i j := by
    rw [residueEnergy, colourEnergy_eq_pairs]
    simp only [Fin.mk.injEq]
    change (∑ i : Fin P, ∑ j : Fin P, g i.val j.val) = _
    simp_rw [Fin.sum_univ_eq_sum_range]
    exact Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range P, g i j) P
  have hdiag : (∑ i ∈ Finset.range P, g i i) = (P : ℝ) := by
    simp only [g, if_true, Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm,
      f, norm_mFourier_apply, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hrow (i : ℕ) :
      (∑ j ∈ Finset.range P, if i < j then g j i else 0) =
        ∑ h ∈ Finset.range (P / q),
          if i + (h + 1) * q < P then (f (i + (h + 1) * q) * conj (f i)).re else 0 := by
    have he := congrArg Complex.re (positive_pairs_eq_shifts (P := P) hq i
      (fun j i => f j * conj (f i)))
    simp only [Complex.re_sum, Finset.sum_filter] at he
    convert he using 1
    · apply Finset.sum_congr rfl
      intro j hj
      dsimp [g]
      by_cases h : i < j
      · by_cases hc : i % q = j % q
        · simp [h, hc]
        · simp [h, hc, Ne.symm hc]
      · simp [h]
    · apply Finset.sum_congr rfl
      intro h hh
      split <;> simp
  rw [hpairs, symmetric_pairs P g hg, hdiag]
  congr 2
  simp_rw [hrow]
  rw [Finset.sum_comm, Fin.sum_univ_eq_sum_range
    (fun h => (differenceSum P ((h + 1) * q) v theta).re) (P / q)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold differenceSum polynomial differenceFrequency boundaryWeight
  rw [Complex.re_sum, Fin.sum_univ_eq_sum_range (fun i =>
    ((if i + (h + 1) * q < P then (1 : ℂ) else 0) *
      mFourier (v (i + (h + 1) * q + 1) - v (i + 1)) theta).re) P]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : i + (h + 1) * q < P
  · simp only [hb, if_true, one_mul, sub_eq_add_neg, mFourier_add, mFourier_neg, f]
  · simp only [hb, if_false, zero_mul, Complex.zero_re]

/-- Taking the norm only after each full difference sum yields the
pointwise estimate used by the quantitative mixed-moment step. -/
theorem residueEnergy_le {d : Type*} [Fintype d]
    (P q : ℕ) (hq : 0 < q) (v : ℕ → d → ℤ) (theta : UnitAddTorus d) :
    residueEnergy P q hq v theta ≤ (P : ℝ) +
      2 * ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖ := by
  rw [residueEnergy_eq_differences]
  gcongr with h
  exact Complex.re_le_norm _

end
end RiemannGaussian.VinogradovDifferenceEnergy
