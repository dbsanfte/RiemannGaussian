/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCanonicalMoments
import RiemannGaussian.ZetaHalfStripSource
import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact isolation of actual zeta zero modes in prime moments

Lagrange interpolation supplies a fixed finite filter for each selected
local zero. It kills every other local singular mode and zeta's pole. The
reflected canonical modes and the actual analytic residual remain explicit.
The coefficients depend on the complete local divisor; no estimate for the
resulting signed prime sum is assumed or asserted here.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

private theorem polynomial_filter_geometric (p : Polynomial ℂ) (b : ℂ) (n : ℕ) :
    (∑ k ∈ p.support, p.coeff k * b ^ (n + k + 1)) = b ^ (n + 1) * p.eval b := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show n + k + 1 = (n + 1) + k by omega, pow_add]
  ring

private theorem polynomial_filter_finite_modes {ι : Type*} (S : Finset ι)
    (p : Polynomial ℂ) (c b : ι → ℂ) (n : ℕ) :
    (∑ k ∈ p.support, p.coeff k * ∑ i ∈ S, c i * b i ^ (n + k + 1)) =
      ∑ i ∈ S, c i * (b i ^ (n + 1) * p.eval (b i)) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← polynomial_filter_geometric, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (r : Set.Ico (3 / 4 : ℝ) 1)

/-- The filter leaves the full analytic residual as a signed finite sum. -/
def adaptiveZetaResidualFilter (y : ℝ) (p : Polynomial ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ p.support, p.coeff k * adaptiveZetaResidualMoment r y (n + k)

/-- A polynomial filter acts on every actual geometric zero mode by
evaluation of that polynomial. All reflected modes are retained. -/
theorem zetaPrimeLogFilter_eq_adaptive_modes (y : ℝ) (p : Polynomial ℂ) (n : ℕ) :
    zetaPrimeLogFilter p n (3 / 2 + I * y) =
      ((1 / 2 + I * (y : ℂ))⁻¹) ^ (n + 1) * p.eval ((1 / 2 + I * (y : ℂ))⁻¹) -
      adaptiveZetaResidualFilter r y p n -
      ∑ i ∈ adaptiveZetaZeroSupport r y,
        (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          ((-i⁻¹) ^ (n + 1) * p.eval (-i⁻¹) -
            (-conj i / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2) ^ (n + 1) *
              p.eval (-conj i / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2)) := by
  unfold zetaPrimeLogFilter
  simp_rw [zetaPrimeLogMoment_eq_adaptive_modes r y, mul_sub, Finset.sum_sub_distrib]
  rw [polynomial_filter_geometric]
  congr 1
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [polynomial_filter_finite_modes, polynomial_filter_finite_modes]

/-- The exact polynomial selecting one actual local zero, with zeta's
pole included among the modes to be annihilated. -/
def adaptiveZetaZeroModeFilter (y : ℝ) (i : ℂ) : Polynomial ℂ :=
  Lagrange.basis (insert (-(1 / 2 + I * (y : ℂ))) (adaptiveZetaZeroSupport r y))
    (fun j : ℂ ↦ -j⁻¹) i

private theorem inverse_mode_injective : Function.Injective (fun j : ℂ ↦ -j⁻¹) :=
  neg_injective.comp inv_injective

private theorem adaptive_pole_not_mem (y : ℝ) :
    -(1 / 2 + I * (y : ℂ)) ∉ adaptiveZetaZeroSupport r y := by
  intro hi
  have h := adaptiveZetaDivisor_re_lt_neg_half r y
    ((mem_adaptiveZetaZeroSupport r y _).mp hi)
  norm_num at h

/-- The selected zero mode has coefficient exactly one. -/
theorem adaptiveZetaZeroModeFilter_eval_self (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) :
    (adaptiveZetaZeroModeFilter r y i).eval (-i⁻¹) = 1 := by
  unfold adaptiveZetaZeroModeFilter
  exact Lagrange.eval_basis_self (v := fun j : ℂ ↦ -j⁻¹) (i := i)
    inverse_mode_injective.injOn (Finset.mem_insert_of_mem hi)

/-- Every other actual local zero mode is killed exactly. -/
theorem adaptiveZetaZeroModeFilter_eval_other (y : ℝ) {i j : ℂ}
    (hij : i ≠ j) (hj : j ∈ adaptiveZetaZeroSupport r y) :
    (adaptiveZetaZeroModeFilter r y i).eval (-j⁻¹) = 0 := by
  unfold adaptiveZetaZeroModeFilter
  exact Lagrange.eval_basis_of_ne (v := fun j : ℂ ↦ -j⁻¹) hij (Finset.mem_insert_of_mem hj)

/-- Zeta's pole is killed exactly, without any height restriction. -/
theorem adaptiveZetaZeroModeFilter_eval_pole (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) :
    (adaptiveZetaZeroModeFilter r y i).eval ((1 / 2 + I * (y : ℂ))⁻¹) = 0 := by
  unfold adaptiveZetaZeroModeFilter
  have hne : i ≠ -(1 / 2 + I * (y : ℂ)) := by
    intro he
    exact adaptive_pole_not_mem r y (he ▸ hi)
  simpa only [inv_neg, neg_neg] using Lagrange.eval_basis_of_ne
    (s := insert (-(1 / 2 + I * (y : ℂ))) (adaptiveZetaZeroSupport r y))
    (v := fun j : ℂ ↦ -j⁻¹) hne (Finset.mem_insert_self _ _)

/-- The degree counts distinct local zeros, while multiplicities remain
in their amplitudes. The extra node used to cancel the pole is included. -/
theorem adaptiveZetaZeroModeFilter_natDegree (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) :
    (adaptiveZetaZeroModeFilter r y i).natDegree = (adaptiveZetaZeroSupport r y).card := by
  rw [adaptiveZetaZeroModeFilter, Lagrange.natDegree_basis inverse_mode_injective.injOn
    (Finset.mem_insert_of_mem hi), Finset.card_insert_of_notMem (adaptive_pole_not_mem r y)]
  omega

/-- Exact isolation of all local singular modes and the pole requires
at least as many polynomial degrees as there are distinct local zeros.
This is an algebraic degree minimum, not a bound for arithmetic work. -/
theorem adaptiveZetaZeroModeFilter_minimal_natDegree (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) (p : Polynomial ℂ)
    (hself : p.eval (-i⁻¹) = 1)
    (hother : ∀ j ∈ adaptiveZetaZeroSupport r y, i ≠ j → p.eval (-j⁻¹) = 0)
    (hpole : p.eval ((1 / 2 + I * (y : ℂ))⁻¹) = 0) :
    (adaptiveZetaZeroSupport r y).card ≤ p.natDegree := by
  let S := insert (-(1 / 2 + I * (y : ℂ))) (adaptiveZetaZeroSupport r y)
  have hiS : i ∈ S := Finset.mem_insert_of_mem hi
  have hcard : (S.erase i).card = (adaptiveZetaZeroSupport r y).card := by
    rw [Finset.card_erase_of_mem hiS]
    change (insert (-(1 / 2 + I * (y : ℂ))) (adaptiveZetaZeroSupport r y)).card - 1 = _
    rw [Finset.card_insert_of_notMem (adaptive_pole_not_mem r y)]
    omega
  by_contra! hlt
  have hd : p.degree < (S.erase i).card := lt_of_le_of_lt p.degree_le_natDegree
    (by exact_mod_cast (show p.natDegree < (S.erase i).card by simpa only [hcard] using hlt))
  have hz := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (S.erase i)
    (v := fun j : ℂ ↦ -j⁻¹) inverse_mode_injective.injOn hd (by
      intro j hj
      obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
      rcases Finset.mem_insert.mp hjS with rfl | hj
      · simpa only [inv_neg, neg_neg] using hpole
      · exact hother j hj hji.symm)
  simp [hz] at hself

/-- The minimum-degree exact isolator is unique. Thus its coefficients
are determined by the actual local zero geometry, not numerical tuning. -/
theorem adaptiveZetaZeroModeFilter_unique (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) (p : Polynomial ℂ)
    (hdeg : p.natDegree ≤ (adaptiveZetaZeroSupport r y).card)
    (hself : p.eval (-i⁻¹) = 1)
    (hother : ∀ j ∈ adaptiveZetaZeroSupport r y, i ≠ j → p.eval (-j⁻¹) = 0)
    (hpole : p.eval ((1 / 2 + I * (y : ℂ))⁻¹) = 0) :
    p = adaptiveZetaZeroModeFilter r y i := by
  let S := insert (-(1 / 2 + I * (y : ℂ))) (adaptiveZetaZeroSupport r y)
  have hcard : S.card = (adaptiveZetaZeroSupport r y).card + 1 :=
    Finset.card_insert_of_notMem (adaptive_pole_not_mem r y)
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S
    (v := fun j : ℂ ↦ -j⁻¹) inverse_mode_injective.injOn
  · apply lt_of_le_of_lt p.degree_le_natDegree
    exact_mod_cast (show p.natDegree < S.card by omega)
  · apply lt_of_le_of_lt (adaptiveZetaZeroModeFilter r y i).degree_le_natDegree
    exact_mod_cast (show (adaptiveZetaZeroModeFilter r y i).natDegree < S.card by
      rw [adaptiveZetaZeroModeFilter_natDegree r y hi]
      omega)
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp only [inv_neg, neg_neg, hpole, adaptiveZetaZeroModeFilter_eval_pole r y hi]
    · by_cases hij : i = j
      · subst j
        rw [hself, adaptiveZetaZeroModeFilter_eval_self r y hi]
      · rw [hother j hj hij, adaptiveZetaZeroModeFilter_eval_other r y hij hj]

/-- The reflected modes remain an exact finite complex sum after filtering. -/
def adaptiveZetaReflectedFilter (y : ℝ) (p : Polynomial ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ adaptiveZetaZeroSupport r y,
    (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) j : ℂ) *
      ((-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2) ^ (n + 1) *
        p.eval (-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2))

/-- One exact filter isolates the selected actual zero in the literal
prime moments, with its full multiplicity and both error channels shown. -/
theorem zetaPrimeLogFilter_isolate_adaptive_zero (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) (n : ℕ) :
    zetaPrimeLogFilter (adaptiveZetaZeroModeFilter r y i) n (3 / 2 + I * y) =
      -(divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          (-i⁻¹) ^ (n + 1) -
        adaptiveZetaResidualFilter r y (adaptiveZetaZeroModeFilter r y i) n +
        adaptiveZetaReflectedFilter r y (adaptiveZetaZeroModeFilter r y i) n := by
  rw [zetaPrimeLogFilter_eq_adaptive_modes r, adaptiveZetaZeroModeFilter_eval_pole r y hi,
    mul_zero]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ j ∈ adaptiveZetaZeroSupport r y,
      (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) j : ℂ) *
        ((-j⁻¹) ^ (n + 1) * (adaptiveZetaZeroModeFilter r y i).eval (-j⁻¹))) =
      (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
        (-i⁻¹) ^ (n + 1) := by
    rw [Finset.sum_eq_single i]
    · rw [adaptiveZetaZeroModeFilter_eval_self r y hi, mul_one]
    · intro j hj hji
      rw [adaptiveZetaZeroModeFilter_eval_other r y hji.symm hj, mul_zero, mul_zero]
    · exact fun h ↦ (h hi).elim
  rw [hs]
  unfold adaptiveZetaReflectedFilter
  ring

/-- Any fixed finite filter preserves decay of the normalized actual
analytic residual. Its coefficients need not obey a uniform size bound. -/
theorem tendsto_adaptiveZetaResidualFilter_mul_pow (y : ℝ) (p : Polynomial ℂ)
    {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < adaptiveZetaCanonicalRadius r y) :
    Tendsto (fun n : ℕ ↦ a ^ (n + 1) * adaptiveZetaResidualFilter r y p n) atTop (𝓝 0) := by
  have hshift (k : ℕ) : Tendsto
      (fun n : ℕ ↦ a ^ (n + 1) * adaptiveZetaResidualMoment r y (n + k)) atTop (𝓝 0) := by
    have h := ((tendsto_adaptiveZetaResidualMoment_mul_pow r y ha).comp
      (tendsto_add_atTop_nat k)).const_mul ((a ^ k)⁻¹)
    simp only [mul_zero] at h
    convert h using 1
    funext n
    simp only [Function.comp_apply, pow_add]
    field_simp
  have h := tendsto_finsetSum p.support (fun k _ ↦ (hshift k).const_mul (p.coeff k))
  have he : (fun n : ℕ ↦ a ^ (n + 1) * adaptiveZetaResidualFilter r y p n) =
      (fun n ↦ ∑ k ∈ p.support,
        p.coeff k * (a ^ (n + 1) * adaptiveZetaResidualMoment r y (n + k))) := by
    funext n
    rw [adaptiveZetaResidualFilter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

/-- Every reflected canonical mode lies strictly below the scale of
any selected point inside the disc. -/
theorem norm_mul_adaptiveZetaReflectedMode_lt_one (y : ℝ) {a j : ℂ}
    (ha : ‖a‖ < adaptiveZetaCanonicalRadius r y) (hj : j ∈ adaptiveZetaZeroSupport r y) :
    ‖a * (-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2)‖ < 1 := by
  have hR := adaptiveZetaCanonicalRadius_pos r y
  have hjR : ‖j‖ < adaptiveZetaCanonicalRadius r y := by
    simpa only [mem_ball, dist_zero_right] using
      (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain
        ((mem_adaptiveZetaZeroSupport r y j).mp hj)
  rw [norm_mul, norm_div, norm_neg, norm_conj, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, ← mul_div_assoc, div_lt_one (sq_pos_of_pos hR)]
  have h1 := mul_le_mul_of_nonneg_left hjR.le (norm_nonneg a)
  have h2 := mul_lt_mul_of_pos_right ha hR
  nlinarith

/-- The full reflected error, with every phase and multiplicity, tends
to zero after normalization by a selected interior zero's scale. -/
theorem tendsto_adaptiveZetaReflectedFilter_mul_pow (y : ℝ) (p : Polynomial ℂ)
    {a : ℂ} (ha : ‖a‖ < adaptiveZetaCanonicalRadius r y) :
    Tendsto (fun n : ℕ ↦ a ^ (n + 1) * adaptiveZetaReflectedFilter r y p n) atTop (𝓝 0) := by
  have ht (j : ℂ) (hj : j ∈ adaptiveZetaZeroSupport r y) : Tendsto (fun n : ℕ ↦
      a ^ (n + 1) *
        ((divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) j : ℂ) *
          ((-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2) ^ (n + 1) *
            p.eval (-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2)))) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (norm_mul_adaptiveZetaReflectedMode_lt_one r y ha hj)).comp
        (tendsto_add_atTop_nat 1)).mul_const
          ((divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) j : ℂ) *
            p.eval (-conj j / (adaptiveZetaCanonicalRadius r y : ℂ) ^ 2))
    simp only [zero_mul] at h
    convert h using 1
    funext n
    simp only [Function.comp_apply, mul_pow]
    ring
  simpa only [adaptiveZetaReflectedFilter, Finset.mul_sum, Finset.sum_const_zero] using
    tendsto_finsetSum (adaptiveZetaZeroSupport r y) ht

/-- The fixed exact filter of actual prime moments recovers the negative
analytic multiplicity of a selected local zero in the normalized limit.
No separation estimate uniform over hypothetical zeros is needed. -/
theorem tendsto_zetaPrimeLogFilter_selected_zero (y : ℝ) {i : ℂ}
    (hi : i ∈ adaptiveZetaZeroSupport r y) :
    Tendsto (fun n : ℕ ↦ (-i) ^ (n + 1) *
      zetaPrimeLogFilter (adaptiveZetaZeroModeFilter r y i) n (3 / 2 + I * y))
      atTop (𝓝 (-(divisor (localZetaPoleRemoved y)
        (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ))) := by
  have hi0 := adaptiveZetaDivisor_point_ne_zero r y ((mem_adaptiveZetaZeroSupport r y i).mp hi)
  have hin : ‖-i‖ < adaptiveZetaCanonicalRadius r y := by
    simpa only [norm_neg, mem_ball, dist_zero_right] using
      (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y))).supportWithinDomain
        ((mem_adaptiveZetaZeroSupport r y i).mp hi)
  have hr := tendsto_adaptiveZetaResidualFilter_mul_pow r y
    (adaptiveZetaZeroModeFilter r y i) (neg_ne_zero.mpr hi0) hin
  have hc := tendsto_adaptiveZetaReflectedFilter_mul_pow r y (adaptiveZetaZeroModeFilter r y i) hin
  have he (n : ℕ) : (-i) ^ (n + 1) *
      zetaPrimeLogFilter (adaptiveZetaZeroModeFilter r y i) n (3 / 2 + I * y) =
      -(divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) -
        (-i) ^ (n + 1) * adaptiveZetaResidualFilter r y (adaptiveZetaZeroModeFilter r y i) n +
        (-i) ^ (n + 1) * adaptiveZetaReflectedFilter r y (adaptiveZetaZeroModeFilter r y i) n := by
    rw [zetaPrimeLogFilter_isolate_adaptive_zero r y hi, mul_add, mul_sub]
    have hc : (-i) ^ (n + 1) * (-i⁻¹) ^ (n + 1) = 1 := by
      rw [← mul_pow, neg_mul_neg, mul_inv_cancel₀ hi0, one_pow]
    calc
      _ = -(divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℂ) *
          ((-i) ^ (n + 1) * (-i⁻¹) ^ (n + 1)) -
          (-i) ^ (n + 1) * adaptiveZetaResidualFilter r y (adaptiveZetaZeroModeFilter r y i) n +
          (-i) ^ (n + 1) * adaptiveZetaReflectedFilter r y (adaptiveZetaZeroModeFilter r y i) n := by ring
      _ = _ := by rw [hc, mul_one]
  simp_rw [he]
  simpa only [sub_zero, add_zero] using (tendsto_const_nhds.sub hr).add hc

/-- The exact filter associated with any selected zero right of the
critical line. Its coefficients are mathematically defined by the full
actual local divisor, independently of the derivative order. -/
def zetaRightHalfZeroModeFilter (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Polynomial ℂ :=
  adaptiveZetaZeroModeFilter (zetaRightHalfDiscParameter rho hrho) rho.1.im
    ((rho.1.re - 3 / 2 : ℝ) : ℂ)

private theorem rightHalfZero_mem_support (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ((rho.1.re - 3 / 2 : ℝ) : ℂ) ∈
      adaptiveZetaZeroSupport (zetaRightHalfDiscParameter rho hrho) rho.1.im := by
  rw [mem_adaptiveZetaZeroSupport, divisor_adaptiveZetaPoleRemoved_nontrivialZero]
  exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'

/-- Every hypothetical zero right of the critical line forces a fixed
finite filter of actual prime moments to recover its negative multiplicity
at the exponential scale given by its distance from the safe center. -/
theorem tendsto_zetaRightHalfZeroModeFilter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun n : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (n + 1) *
      zetaPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) n (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := tendsto_zetaPrimeLogFilter_selected_zero (zetaRightHalfDiscParameter rho hrho)
    rho.1.im (rightHalfZero_mem_support rho hrho)
  rw [divisor_adaptiveZetaPoleRemoved_nontrivialZero] at h
  have he : -((rho.1.re - 3 / 2 : ℝ) : ℂ) = ((3 / 2 - rho.1.re : ℝ) : ℂ) := by push_cast; ring
  simpa only [he, Int.cast_natCast, zetaRightHalfZeroModeFilter] using h

/-- The real signed arithmetic signal has the same strictly negative
limit; no absolute value is used to detect the zero. -/
theorem tendsto_zetaRightHalfZeroModeFilter_re (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun n : ℕ ↦ (3 / 2 - rho.1.re) ^ (n + 1) *
      (zetaPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) n (3 / 2 + I * rho.1.im)).re)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_zetaRightHalfZeroModeFilter rho hrho)
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.neg_re, Complex.natCast_re] using h

/-- Eventually the literal filtered prime moment has a negative source
of at least half the selected zero's full multiplicity at its exact scale. -/
theorem zetaRightHalfZeroModeFilter_eventually_negative (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ n : ℕ in atTop,
      (zetaPrimeLogFilter (zetaRightHalfZeroModeFilter rho hrho) n (3 / 2 + I * rho.1.im)).re <
        -(analyticZetaZeroMultiplicity rho : ℝ) / (2 * (3 / 2 - rho.1.re) ^ (n + 1)) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_zetaRightHalfZeroModeFilter_re rho hrho).eventually
    (gt_mem_nhds (by linarith : -(analyticZetaZeroMultiplicity rho : ℝ) <
      -(analyticZetaZeroMultiplicity rho : ℝ) / 2))
  filter_upwards [h] with n hn
  rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hu _))]
  nlinarith

end

end RiemannGaussian
