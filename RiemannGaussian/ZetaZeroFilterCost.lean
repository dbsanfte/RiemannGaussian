/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianZeroSeparation
import RiemannGaussian.ZetaMoebiusPoleJetFilter
import RiemannGaussian.ZetaPrimeBandChebyshev
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-!
# Geometry and coefficient cost of the actual zero-isolating filter

Mahler measure keeps the full product of normalized inverse-coordinate
factors. Their exact cost is expressed in the original zero distances,
before the Gaussian separation bound is applied. Mignotte's coefficient
estimate then controls the entire weighted coefficient sum. These are
conditioning estimates; the signed prime cancellation remains a separate
arithmetic obligation.
-/

namespace RiemannGaussian.ZetaZeroFilterCost
noncomputable section
open Complex Filter MeromorphicOn Metric Polynomial Set Topology
open ZetaGaussianAllHeight
open scoped Classical

/-- The complete weighted coefficient allowance, with no degree truncation. -/
def coefficientCost (p : Polynomial ℂ) (R : ℝ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ * R ^ k

/-- Mignotte's binomial estimate controls the whole coefficient allowance
at every nonnegative weight, by the exact Mahler measure. -/
theorem coefficientCost_le (p : Polynomial ℂ) {R : ℝ} (hR : 0 ≤ R) :
    coefficientCost p R ≤ p.mahlerMeasure * (1 + R) ^ p.natDegree := by
  have he : coefficientCost p R =
      ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ * R ^ k := by
    exact p.sum_over_range (f := fun k c => ‖c‖ * R ^ k) (by simp)
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
        (p.natDegree.choose k : ℝ) * p.mahlerMeasure * R ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (p.norm_coeff_le_choose_mul_mahlerMeasure k)
        (pow_nonneg hR k)
    _ = _ := by
      rw [add_comm 1 R, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [one_pow]
      ring

/-- Inverting the spectral nodes preserves an exact physical-distance
formula for each factor's Mahler measure. -/
theorem inverse_factor_measure {i j : ℂ} (hi : i ≠ 0) (hj : j ≠ 0) :
    (Lagrange.basisDivisor (-i⁻¹) (-j⁻¹)).mahlerMeasure =
      ‖i‖ * max ‖j‖ 1 / ‖i - j‖ := by
  have he : -i⁻¹ - -j⁻¹ = (i - j) / (i * j) := by
    field_simp
    ring
  rw [Lagrange.basisDivisor, mahlerMeasure_mul, mahlerMeasure_const,
    mahlerMeasure_X_sub_C, norm_inv, norm_neg, he, norm_div, norm_mul, inv_div, norm_inv]
  have hx : ‖j‖ * max 1 ‖j‖⁻¹ = max ‖j‖ 1 := by
    rw [mul_max_of_nonneg _ _ (norm_nonneg j), mul_one,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj)]
  calc
    _ = ‖i‖ * (‖j‖ * max 1 ‖j‖⁻¹) / ‖i - j‖ := by ring
    _ = _ := by rw [hx]

/-- Mahler measure is multiplicative over any finite original factor family. -/
theorem measure_prod {ι : Type*} (S : Finset ι) (p : ι → Polynomial ℂ) :
    (∏ j ∈ S, p j).mahlerMeasure = ∏ j ∈ S, (p j).mahlerMeasure := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih => simp [Finset.prod_insert hj, mahlerMeasure_mul, ih]

/-- The full normalized Lagrange filter retains the product of all
actual physical distances; inversion introduces no untracked denominator. -/
theorem inverse_basis_measure (S : Finset ℂ) {i : ℂ} (hi : i ≠ 0)
    (hS : ∀ j ∈ S, j ≠ 0) :
    (Lagrange.basis S (fun j : ℂ => -j⁻¹) i).mahlerMeasure =
      ∏ j ∈ S.erase i, (‖i‖ * max ‖j‖ 1 / ‖i - j‖) := by
  rw [Lagrange.basis, measure_prod]
  exact Finset.prod_congr rfl (fun j hj => inverse_factor_measure hi (hS j (Finset.mem_of_mem_erase hj)))

/-- Every point of the complete adaptive divisor lies in the actual unit disc. -/
theorem support_norm_lt_one (r : Ico (3 / 4 : ℝ) 1) (t : ℝ) {j : ℂ}
    (hj : j ∈ adaptiveZetaZeroSupport r t) : ‖j‖ < 1 := by
  have hm := (divisor (localZetaPoleRemoved t) (ball 0 (adaptiveZetaCanonicalRadius r t))).supportWithinDomain
    ((mem_adaptiveZetaZeroSupport r t j).mp hj)
  exact (show ‖j‖ < adaptiveZetaCanonicalRadius r t by simpa using hm).trans
    (adaptiveZetaCanonicalRadius_spec r t).2.1

/-- A divisor point is a genuine translated nontrivial zero, not merely
an interpolation node with an assumed analytic interpretation. -/
theorem support_is_zero (r : Ico (3 / 4 : ℝ) 1) (t : ℝ) {j : ℂ}
    (hj : j ∈ adaptiveZetaZeroSupport r t) :
    IsNontrivialZetaZero (3 / 2 + I * t + j) := by
  have hn := support_norm_lt_one r t hj
  apply isNontrivialZetaZero_of_poleRemoved_eq_zero
  · have h := (abs_le.mp (Complex.abs_re_le_norm j)).1
    norm_num
    linarith
  · exact adaptiveZetaPoleRemoved_eq_zero_of_divisor_ne_zero r t
      ((mem_adaptiveZetaZeroSupport r t j).mp hj)

/-- The actual selected zero has a nonzero local coordinate of norm less than one. -/
theorem selected_coordinate (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) :
    ((ρ.1.re - 3 / 2 : ℝ) : ℂ) ≠ 0 ∧ ‖((ρ.1.re - 3 / 2 : ℝ) : ℂ)‖ < 1 := by
  have hu : 0 < 3 / 2 - ρ.1.re := by linarith [ρ.re_lt_one]
  constructor
  · exact Complex.ofReal_ne_zero.mpr (by linarith)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith

/-- The selected coordinate belongs to the exact local divisor used to
define its original filter, with all multiplicity premises discharged. -/
theorem selected_mem_support (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) :
    ((ρ.1.re - 3 / 2 : ℝ) : ℂ) ∈
      adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im := by
  rw [mem_adaptiveZetaZeroSupport, divisor_adaptiveZetaPoleRemoved_nontrivialZero]
  exact_mod_cast (analyticZetaZeroMultiplicity_positive ρ).ne'

private theorem width_le_one (t : ℝ) : explicitWidth t ≤ 1 :=
  (ZetaGaussianScaledBandBudget.width_bounds (le_max_left _ _)).2.trans
    (by norm_num [GaussianStripProfile.width])

/-- Gaussian separation controls the complete inverse-coordinate factor
for every other actual zero in the filter's full local divisor. -/
theorem zero_factor_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im)
    {j : ℂ} (hj : j ∈ adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im)
    (hji : j ≠ ((ρ.1.re - 3 / 2 : ℝ) : ℂ)) :
    (Lagrange.basisDivisor (-((ρ.1.re - 3 / 2 : ℝ) : ℂ)⁻¹) (-j⁻¹)).mahlerMeasure ≤
      2 / explicitWidth ρ.1.im := by
  let τ : NontrivialZetaZero := ⟨3 / 2 + I * ρ.1.im + j,
    support_is_zero (zetaRightHalfDiscParameter ρ hρ) ρ.1.im hj⟩
  have he : τ.1 - ρ.1 = j - ((ρ.1.re - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [τ]
      ring
    · simp [τ]
  have hne : ρ ≠ τ := by
    intro h
    have hzero : τ.1 - ρ.1 = 0 := by rw [← h]; simp
    rw [he] at hzero
    exact hji (sub_eq_zero.mp hzero)
  have hd := ZetaGaussianZeroSeparation.inverse_distance_bound ρ τ ht hne
    ((min_le_right _ _).trans hdepth)
  rw [he, norm_sub_rev] at hd
  have hj0 := adaptiveZetaDivisor_point_ne_zero (zetaRightHalfDiscParameter ρ hρ) ρ.1.im
    ((mem_adaptiveZetaZeroSupport _ _ _).mp hj)
  rw [inverse_factor_measure (selected_coordinate ρ hρ).1 hj0,
    max_eq_right (support_norm_lt_one _ _ hj).le, mul_one]
  exact (div_le_div_of_nonneg_right (selected_coordinate ρ hρ).2.le (norm_nonneg _)).trans hd.le

/-- The pole factor keeps its large ordinate in both numerator and
denominator; its complete cost is at most two at every eligible height. -/
theorem pole_factor_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) :
    (Lagrange.basisDivisor (-((ρ.1.re - 3 / 2 : ℝ) : ℂ)⁻¹)
      (-(-(1 / 2 + I * (ρ.1.im : ℂ)))⁻¹)).mahlerMeasure ≤ 2 := by
  let i : ℂ := ((ρ.1.re - 3 / 2 : ℝ) : ℂ)
  let j : ℂ := -(1 / 2 + I * (ρ.1.im : ℂ))
  have hi := selected_coordinate ρ hρ
  have hj : j ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp [j] at h
    rw [h] at ht
    norm_num at ht
  have hd : 1 ≤ ‖i - j‖ := by
    have h := Complex.abs_im_le_norm (i - j)
    have him : (i - j).im = ρ.1.im := by simp [i, j]
    rw [him] at h
    linarith
  have hsum : ‖j‖ ≤ ‖i‖ + ‖i - j‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le i (i - j)
  have hmax : max ‖j‖ 1 ≤ 2 * ‖i - j‖ := max_le (by linarith [hi.2]) (by linarith)
  change (Lagrange.basisDivisor (-i⁻¹) (-j⁻¹)).mahlerMeasure ≤ 2
  rw [inverse_factor_measure hi.1 hj]
  apply (div_le_iff₀ (by linarith : 0 < ‖i - j‖)).mpr
  have h := mul_le_mul hi.2.le hmax (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _))
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using h

/-- The full original zero-mode filter has a product bound, with every
local zero and the pole included. No single-factor estimate substitutes
for the cost of the complete normalized polynomial. -/
theorem zero_filter_measure_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im) :
    (zetaRightHalfZeroModeFilter ρ hρ).mahlerMeasure ≤
      (2 / explicitWidth ρ.1.im) ^
        (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im).card := by
  let r := zetaRightHalfDiscParameter ρ hρ
  let i : ℂ := ((ρ.1.re - 3 / 2 : ℝ) : ℂ)
  let b : ℂ := -(1 / 2 + I * (ρ.1.im : ℂ))
  let S := insert b (adaptiveZetaZeroSupport r ρ.1.im)
  have hi : i ∈ S := Finset.mem_insert_of_mem (selected_mem_support ρ hρ)
  have hb : b ∉ adaptiveZetaZeroSupport r ρ.1.im := by
    intro h
    have he := adaptiveZetaDivisor_re_lt_neg_half r ρ.1.im ((mem_adaptiveZetaZeroSupport _ _ _).mp h)
    norm_num [b] at he
  have hcard : (S.erase i).card = (adaptiveZetaZeroSupport r ρ.1.im).card := by
    rw [Finset.card_erase_of_mem hi]
    dsimp only [S]
    rw [Finset.card_insert_of_notMem hb]
    omega
  have hf (j : ℂ) (hj : j ∈ S.erase i) :
      (Lagrange.basisDivisor (-i⁻¹) (-j⁻¹)).mahlerMeasure ≤ 2 / explicitWidth ρ.1.im := by
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (pole_factor_bound ρ hρ ht).trans
      exact (le_div_iff₀ (explicitWidth_pos _)).mpr (by linarith [width_le_one ρ.1.im])
    · exact zero_factor_bound ρ hρ ht hdepth hj hji
  change (∏ j ∈ S.erase i, Lagrange.basisDivisor (-i⁻¹) (-j⁻¹)).mahlerMeasure ≤ _
  rw [measure_prod]
  have h := Finset.prod_le_prod (fun j _ => (Lagrange.basisDivisor (-i⁻¹) (-j⁻¹)).mahlerMeasure_nonneg) hf
  simpa only [Finset.prod_const, hcard] using h

/-- A complete unit-disc zero count is paid by the actual global Poisson
mass. Its cost is explicit and independent of the local zero geometry. -/
theorem unit_disc_card_bound (t : ℝ) (S : Finset NontrivialZetaZero)
    (hS : ∀ ρ ∈ S, ‖(3 / 2 + I * (t : ℂ)) - ρ.1‖ < 1) :
    (S.card : ℝ) ≤ 2 * ZetaGaussianPhaseAllowance.xiAllowance (3 / 2) t := by
  let s : ℂ := 3 / 2 + I * t
  have hs : 1 ≤ s.re := by norm_num [s]
  have hp (ρ : NontrivialZetaZero) (hρ : ρ ∈ S) : 1 / 2 ≤ zetaGlobalPoissonSummand s ρ := by
    have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity ρ := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
    have hd : 1 / 2 < s.re - ρ.1.re := by norm_num [s]; linarith [ρ.re_lt_one]
    have hz : 0 < Complex.normSq (s - ρ.1) := Complex.normSq_pos.mpr
      (Complex.ne_zero_of_re_pos (by simp only [Complex.sub_re]; linarith))
    have hn : Complex.normSq (s - ρ.1) ≤ 1 := by
      rw [← Complex.sq_norm]
      have h := hS ρ hρ
      nlinarith [norm_nonneg (s - ρ.1)]
    rw [zetaGlobalPoissonSummand, le_div_iff₀ hz]
    have h := mul_le_mul_of_nonneg_right hm (show 0 ≤ s.re - ρ.1.re by linarith)
    nlinarith
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hb := sum_zetaGlobalPoissonSummand_le hs S
  have hc := ZetaGaussianPhaseAllowance.xi_le_allowance (σ := 3 / 2) (by norm_num) t
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  change (logDeriv riemannXi s).re ≤ _ at hc
  linarith

/-- Every adaptive filter has an explicit logarithmic bound for the
number of its actual local zero nodes, including nodes near its outer radius. -/
theorem support_card_bound (r : Ico (3 / 4 : ℝ) 1) (t : ℝ) :
    ((adaptiveZetaZeroSupport r t).card : ℝ) ≤
      2 * ZetaGaussianPhaseAllowance.xiAllowance (3 / 2) t := by
  let S := adaptiveZetaZeroSupport r t
  let f : {j // j ∈ S} → NontrivialZetaZero :=
    fun j => ⟨3 / 2 + I * t + j.1, support_is_zero r t j.2⟩
  have hf : Function.Injective f := by
    intro j k h
    apply Subtype.ext
    have he := congrArg (fun ρ : NontrivialZetaZero => ρ.1) h
    exact add_left_cancel he
  have h := unit_disc_card_bound t (S.attach.image f) (by
    intro ρ hρ
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hρ
    have he : (3 / 2 + I * (t : ℂ)) - (f j).1 = -j.1 := by dsimp [f]; ring
    rw [he, norm_neg]
    exact support_norm_lt_one r t j.2)
  simpa only [Finset.card_image_of_injective _ hf, Finset.card_attach] using h

/-- A natural degree allowance evaluated solely from the safe real Euler
constant and the actual height, with the extra pole-jet factor included. -/
def degreeAllowance (t : ℝ) : ℕ :=
  ⌈2 * ZetaGaussianPhaseAllowance.xiAllowance (3 / 2) t⌉₊ + 1

/-- The degree allowance contains only one fixed real Euler derivative
and one height logarithm, with its integer rounding retained exactly. -/
theorem degreeAllowance_eq (t : ℝ) :
    degreeAllowance t =
      ⌈4 + 2 * (-logDeriv riemannZeta ((3 / 2 : ℝ) : ℂ)).re + Real.log (3 / 2 + |t|)⌉₊ + 1 := by
  unfold degreeAllowance ZetaGaussianPhaseAllowance.xiAllowance
  congr 2
  ring

/-- The complete local node count, plus the extra pole factor, fits the
same height-only degree allowance. -/
theorem support_card_succ_le (r : Ico (3 / 4 : ℝ) 1) (t : ℝ) :
    (adaptiveZetaZeroSupport r t).card + 1 ≤ degreeAllowance t := by
  have h := (support_card_bound r t).trans (Nat.le_ceil _)
  have hn : (adaptiveZetaZeroSupport r t).card ≤
      ⌈2 * ZetaGaussianPhaseAllowance.xiAllowance (3 / 2) t⌉₊ := by exact_mod_cast h
  exact Nat.add_le_add_right hn 1

/-- The promoted actual filter has at most one more degree than its
exact local zero count. No coefficient estimate is used to infer the degree. -/
theorem pole_jet_degree_le (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) :
    (zetaRightHalfPoleJetFilter ρ hρ).natDegree ≤
      (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im).card + 1 := by
  let p := zetaRightHalfZeroModeFilter ρ hρ
  let b := (((3 / 2 - ρ.1.re : ℝ) : ℂ)⁻¹)
  let c := ((3 / 2 + I * (ρ.1.im : ℂ)) - 1)⁻¹
  have h0 := Polynomial.natDegree_mul_le (p := Polynomial.C (b - c)⁻¹) (q := (Polynomial.X - Polynomial.C c) * p)
  have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X - Polynomial.C c) (q := p)
  simp only [Polynomial.natDegree_C, zero_add] at h0
  rw [Polynomial.natDegree_X_sub_C] at h1
  have hd : p.natDegree = (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im).card :=
    adaptiveZetaZeroModeFilter_natDegree _ _ (selected_mem_support ρ hρ)
  change (Polynomial.C (b - c)⁻¹ * ((Polynomial.X - Polynomial.C c) * p)).natDegree ≤ _
  omega

/-- The complete pole-jet filter has a bounded Mahler product, including
both occurrences of the pole root and every distinct local zero. -/
theorem pole_jet_measure_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im) :
    (zetaRightHalfPoleJetFilter ρ hρ).mahlerMeasure ≤
      (2 / explicitWidth ρ.1.im) ^
        ((adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im).card + 1) := by
  have hb : (((3 / 2 - ρ.1.re : ℝ) : ℂ)⁻¹) = -((ρ.1.re - 3 / 2 : ℝ) : ℂ)⁻¹ := by
    have he : ((3 / 2 - ρ.1.re : ℝ) : ℂ) = -((ρ.1.re - 3 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, inv_neg]
  have hc : ((3 / 2 + I * (ρ.1.im : ℂ)) - 1)⁻¹ = -(-(1 / 2 + I * (ρ.1.im : ℂ)))⁻¹ := by
    simp only [inv_neg, neg_neg]
    congr 1
    ring
  have he : zetaRightHalfPoleJetFilter ρ hρ =
      Lagrange.basisDivisor (-((ρ.1.re - 3 / 2 : ℝ) : ℂ)⁻¹)
        (-(-(1 / 2 + I * (ρ.1.im : ℂ)))⁻¹) * zetaRightHalfZeroModeFilter ρ hρ := by
    simp only [zetaRightHalfPoleJetFilter, zetaPoleJetLift, hb, hc, Lagrange.basisDivisor, mul_assoc]
  rw [he, mahlerMeasure_mul]
  have hd := explicitWidth_pos ρ.1.im
  have hp := (pole_factor_bound ρ hρ ht).trans
    ((le_div_iff₀ (explicitWidth_pos _)).mpr (show 2 * explicitWidth ρ.1.im ≤ 2 by
      linarith [width_le_one ρ.1.im]))
  have h := mul_le_mul hp (zero_filter_measure_bound ρ hρ ht hdepth)
    (zetaRightHalfZeroModeFilter ρ hρ).mahlerMeasure_nonneg (by positivity)
  simpa only [pow_succ, mul_comm] using h

/-- The full weighted coefficient cost of the actual pole-jet filter is
bounded using only the height and Gaussian width, with no unknown local
zero count or separation constant left in the estimate. -/
theorem actual_coefficient_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im)
    {R : ℝ} (hR : 0 ≤ R) :
    coefficientCost (zetaRightHalfPoleJetFilter ρ hρ) R ≤
      (2 * (1 + R) / explicitWidth ρ.1.im) ^ degreeAllowance ρ.1.im := by
  have hd := explicitWidth_pos ρ.1.im
  let K := (adaptiveZetaZeroSupport (zetaRightHalfDiscParameter ρ hρ) ρ.1.im).card + 1
  have hpower := pow_le_pow_right₀ (show 1 ≤ 1 + R by linarith) (pole_jet_degree_le ρ hρ)
  have h := mul_le_mul (pole_jet_measure_bound ρ hρ ht hdepth) hpower
    (by positivity : 0 ≤ (1 + R) ^ (zetaRightHalfPoleJetFilter ρ hρ).natDegree) (by positivity)
  have he : (2 / explicitWidth ρ.1.im) ^ K * (1 + R) ^ K =
      (2 * (1 + R) / explicitWidth ρ.1.im) ^ K := by rw [← mul_pow]; congr 1; ring
  change _ ≤ (2 / explicitWidth ρ.1.im) ^ K * (1 + R) ^ K at h
  rw [he] at h
  have hbase : 1 ≤ 2 * (1 + R) / explicitWidth ρ.1.im := by
    apply (le_div_iff₀ (explicitWidth_pos _)).mpr
    linarith [width_le_one ρ.1.im]
  exact ((coefficientCost_le _ hR).trans h).trans
    (pow_le_pow_right₀ hbase (support_card_succ_le _ _))

/-- A filter's two endpoint weights cost at most twice its complete
coefficient allowance at weight four. -/
theorem endpoint_constant_le (p : Polynomial ℂ) :
    zetaPrimeBandEndpointConstant p ≤ 2 * coefficientCost p 4 := by
  unfold zetaPrimeBandEndpointConstant coefficientCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 4) k
  nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (p.coeff k))]

/-- The actual filter's complete endpoint constant is explicit in the
height, with no hidden coefficient-dependent prefactor. -/
theorem actual_endpoint_constant_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im) :
    zetaPrimeBandEndpointConstant (zetaRightHalfPoleJetFilter ρ hρ) ≤
      2 * (10 / explicitWidth ρ.1.im) ^ degreeAllowance ρ.1.im := by
  have h := actual_coefficient_bound ρ hρ ht hdepth (R := 4) (by norm_num)
  norm_num only at h
  exact (endpoint_constant_le _).trans (mul_le_mul_of_nonneg_left h (by norm_num))

/-- Removing the exact pole factor gives the original polynomial back
as the full product with its monic quotient. -/
theorem pole_factorization {p : Polynomial ℂ} {c : ℂ} (hp : p.eval c = 0) :
    p = (Polynomial.X - Polynomial.C c) * (p /ₘ (Polynomial.X - Polynomial.C c)) := by
  rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    Polynomial.modByMonic_X_sub_C_eq_C_eval, hp, Polynomial.C_0, sub_zero]

/-- The shifted density primitive loses a pole factor without increasing
Mahler measure when the pole mode lies in the unit disc. -/
theorem primitive_measure_le (p : Polynomial ℂ) (s : ℂ)
    (hp : p.eval (s - 1)⁻¹ = 0) (hc : ‖(s - 1)⁻¹‖ ≤ 1) :
    (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p s).mahlerMeasure ≤ p.mahlerMeasure := by
  have he := congrArg Polynomial.mahlerMeasure (pole_factorization hp)
  rw [mahlerMeasure_mul, mahlerMeasure_X_sub_C, max_eq_left hc, one_mul] at he
  rw [zetaPrimeFilterPrimitivePolynomial, mahlerMeasure_mul, mahlerMeasure_mul,
    mahlerMeasure_const, norm_neg]
  have hx : (Polynomial.X : Polynomial ℂ).mahlerMeasure = 1 := by
    simpa using Polynomial.mahlerMeasure_X_sub_C (0 : ℂ)
  rw [hx, one_mul, ← he]
  exact mul_le_of_le_one_left p.mahlerMeasure_nonneg hc

/-- The same exact primitive does not increase the degree after its
moment shift. The zero polynomial is handled without a degree convention shortcut. -/
theorem primitive_degree_le (p : Polynomial ℂ) (s : ℂ)
    (hp : p.eval (s - 1)⁻¹ = 0) :
    (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p s).natDegree ≤ p.natDegree := by
  by_cases hp0 : p = 0
  · simp [hp0, zetaPrimeFilterPrimitivePolynomial]
  let q := p /ₘ (Polynomial.X - Polynomial.C (s - 1)⁻¹)
  have hq : q ≠ 0 := by
    intro h
    have he := pole_factorization hp
    change p = (Polynomial.X - Polynomial.C (s - 1)⁻¹) * q at he
    rw [h, mul_zero] at he
    exact hp0 he
  have he : p.natDegree = 1 + q.natDegree := by
    conv_lhs => rw [pole_factorization hp]
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq, Polynomial.natDegree_X_sub_C]
  have h0 := Polynomial.natDegree_mul_le (p := Polynomial.X)
    (q := Polynomial.C (-(s - 1)⁻¹) * q)
  have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C (-(s - 1)⁻¹)) (q := q)
  simp only [Polynomial.natDegree_X, Polynomial.natDegree_C, zero_add] at h0 h1
  change (Polynomial.X * (Polynomial.C (-(s - 1)⁻¹) * q)).natDegree ≤ _
  omega

/-- The shifted primitive's weighted coefficients obey the same full
height-only bound as the actual filter, including its exact pole cancellation. -/
theorem actual_primitive_coefficient_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im)
    {R : ℝ} (hR : 0 ≤ R) :
    coefficientCost (Polynomial.X * zetaPrimeFilterPrimitivePolynomial
      (zetaRightHalfPoleJetFilter ρ hρ) (3 / 2 + I * ρ.1.im)) R ≤
      (2 * (1 + R) / explicitWidth ρ.1.im) ^ degreeAllowance ρ.1.im := by
  let p := zetaRightHalfPoleJetFilter ρ hρ
  let s : ℂ := 3 / 2 + I * ρ.1.im
  let q := Polynomial.X * zetaPrimeFilterPrimitivePolynomial p s
  have hp : p.eval (s - 1)⁻¹ = 0 := (zetaRightHalfPoleJetFilter_pole_jet ρ hρ).1
  have hn : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have hi : (s - 1).im = ρ.1.im := by simp [s]
    rw [hi] at h
    linarith
  have hc : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hn
  have hM := (primitive_measure_le p s hp hc).trans (pole_jet_measure_bound ρ hρ ht hdepth)
  have hdeg := (primitive_degree_le p s hp).trans (pole_jet_degree_le ρ hρ)
  have hd := explicitWidth_pos ρ.1.im
  have h := mul_le_mul hM (pow_le_pow_right₀ (show 1 ≤ 1 + R by linarith) hdeg)
    (pow_nonneg (by linarith : 0 ≤ 1 + R) q.natDegree) (by positivity)
  rw [← mul_pow] at h
  have he : 2 / explicitWidth ρ.1.im * (1 + R) = 2 * (1 + R) / explicitWidth ρ.1.im := by ring
  rw [he] at h
  have hb : 1 ≤ 2 * (1 + R) / explicitWidth ρ.1.im := by
    apply (le_div_iff₀ hd).mpr
    linarith [width_le_one ρ.1.im]
  exact ((coefficientCost_le q hR).trans h).trans
    (pow_le_pow_right₀ hb (support_card_succ_le _ _))

/-- The original finite prime band and its full signed Chebyshev-error
integral have an explicit common geometric discrepancy, uniformly in the
order and all zeros in the stated layer. The signed bulk itself is retained. -/
theorem actual_band_discrepancy_bound (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im) (N : ℕ) :
    ‖zetaOrdinaryPrimeBandFilter (zetaRightHalfPoleJetFilter ρ hρ) N ρ.1.im -
      zetaPrimeBandChebyshevIntegral (zetaRightHalfPoleJetFilter ρ hρ) N ρ.1.im‖ ≤
      (1 / 2 : ℝ) ^ N *
        (2 * (Real.log 4 + 2) * (10 / explicitWidth ρ.1.im) ^ degreeAllowance ρ.1.im) := by
  have h := norm_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral_le
    (zetaRightHalfPoleJetFilter ρ hρ) N ρ.1.im (zetaRightHalfPoleJetFilter_pole_jet ρ hρ).1
  have hp := actual_endpoint_constant_bound ρ hρ ht hdepth
  have hq := (endpoint_constant_le (Polynomial.X * zetaPrimeFilterPrimitivePolynomial
    (zetaRightHalfPoleJetFilter ρ hρ) (3 / 2 + I * ρ.1.im))).trans
      (mul_le_mul_of_nonneg_left (actual_primitive_coefficient_bound ρ hρ ht hdepth
        (R := 4) (by norm_num)) (by norm_num))
  norm_num only at hq
  have hl : 0 ≤ Real.log 4 + 1 := by positivity
  have hw := mul_le_mul_of_nonneg_left hp hl
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith only [hq, hw]

/-- The same actual pole-jet filter still detects a full simple-zero
source in the signed centered carrier. Its coefficient and reduction
costs have been bounded above, not the signed bulk appearing in this limit. -/
theorem actual_centered_source_limit (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re)
    (ht : 1000000 ≤ |ρ.1.im|) (hdepth : 1 - ρ.1.re ≤ 3 / 2 * explicitWidth ρ.1.im) :
    Tendsto (fun N : ℕ => ((3 / 2 - ρ.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaPrimeBandChebyshevIntegral (zetaRightHalfPoleJetFilter ρ hρ) N ρ.1.im)
      atTop (𝓝 (-1)) := by
  let p := zetaRightHalfPoleJetFilter ρ hρ
  let u : ℂ := ((3 / 2 - ρ.1.re : ℝ) : ℂ)
  have hu : ‖u‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [ρ.re_lt_one])]
    linarith
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow p ρ.1.im hu
  have htail := hpow.mul (tendsto_zetaOrdinaryPrimeLogFilter_sub_band p ρ.1.im)
  have herr := hpow.mul (tendsto_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral p ρ.1.im
    (zetaRightHalfPoleJetFilter_pole_jet ρ hρ).1)
  have h := (((tendsto_zetaRightHalfPoleJetFilter ρ hρ).sub hp).sub htail).sub herr
  have hm := ZetaGaussianMultiplicityDepth.simple_of_near_edge ρ ht (by
    have hd := explicitWidth_pos ρ.1.im
    exact (min_le_right _ _).trans (hdepth.trans (by linarith)))
  rw [hm] at h
  simp only [Nat.cast_one, zero_mul, sub_zero, Function.comp_apply] at h
  convert h using 1
  funext N
  rw [zetaPrimeLogFilter_eq_prime_add_proper _ _ (by norm_num)]
  dsimp only [p, u]
  ring

end
end RiemannGaussian.ZetaZeroFilterCost
