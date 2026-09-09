/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPositiveCompositeResponse
import RiemannGaussian.ZetaMoebiusWronskianMoments

/-!
# All moments and mixed energies of the positive composite response

Every moment of the fixed zeta response is a genuinely convergent series
with nonnegative real weights and its full complex Dirichlet feature.
Arbitrary finite complex probes give an exact mixed energy identity.
The norm bound is downstream of that identity, and the existing filtered
Wronskian is transported to the same positive coefficients with all
cofactor derivatives retained.
-/

open Complex ComplexConjugate Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Absolute convergence of the fixed nonnegative arithmetic response
throughout the Euler half-plane. -/
theorem abscissaOfAbsConv_zetaPositiveComposite_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact (LSeriesHasSum_zetaPositiveCompositeResponse (by simpa using hy)).LSeriesSummable

private theorem response_eventuallyEq {s : ℂ} (hs : 1 < s.re) :
    zetaPositiveCompositeResponse =ᶠ[𝓝 s]
      LSeries (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ)) := by
  filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
  exact (LSeriesHasSum_zetaPositiveCompositeResponse hz).LSeries_eq.symm

/-- The meromorphic response is actually analytic at every Euler
evaluation point; its arithmetic convergence discharges the hypothesis. -/
theorem analyticAt_zetaPositiveCompositeResponse {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ zetaPositiveCompositeResponse s := by
  rw [analyticAt_congr (response_eventuallyEq hs)]
  apply LSeries_analyticOnNhd
  exact lt_of_le_of_lt abscissaOfAbsConv_zetaPositiveComposite_le_one (by exact_mod_cast hs)

/-- The real nonnegative weight of the complete factorial logarithmic moment. -/
def zetaPositiveCompositeLogWeight (k n : ℕ) : ℝ :=
  zetaPositiveCompositeArithmetic n * (Real.log n ^ k / (k.factorial : ℝ))

/-- Every moment keeps nonnegative arithmetic weights, at every integer. -/
theorem zetaPositiveCompositeLogWeight_nonneg (k n : ℕ) :
    0 ≤ zetaPositiveCompositeLogWeight k n := by
  exact mul_nonneg (zetaPositiveCompositeArithmetic_nonneg n)
    (div_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _) (Nat.cast_nonneg _))

/-- Every moment is the exact convergent complex arithmetic sum; neither
the Dirichlet phase nor the logarithmic order is discarded. -/
theorem hasSum_zetaPositiveCompositeMoment (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ (zetaPositiveCompositeLogWeight k n : ℂ) * zetaPrimeFeature s n)
      (signedTaylorMoment k zetaPositiveCompositeResponse s) := by
  rw [signedTaylorMoment_congr k (response_eventuallyEq hs)]
  have h := hasSum_signedTaylorMoment_LSeries (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ))
    (by simp) (lt_of_le_of_lt abscissaOfAbsConv_zetaPositiveComposite_le_one (by exact_mod_cast hs)) k
  simpa only [zetaPositiveCompositeLogWeight, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast] using h

private theorem feature_real (σ : ℝ) (n : ℕ) :
    zetaPrimeFeature (σ : ℂ) n = (Real.exp (-σ * Real.log n) : ℂ) := by
  unfold zetaPrimeFeature
  rw [show -((σ : ℂ) * (Real.log n : ℂ)) = ((-σ * Real.log n : ℝ) : ℂ) by push_cast; ring]
  exact (Complex.ofReal_exp _).symm

private theorem norm_feature (s : ℂ) (n : ℕ) :
    ‖zetaPrimeFeature s n‖ = Real.exp (-s.re * Real.log n) := by
  rw [zetaPrimeFeature, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, neg_mul]

/-- The scalar norm bound follows from the full convergent complex
identity, uniformly in the imaginary part and at every moment order. -/
theorem norm_zetaPositiveCompositeMoment_le_real (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖signedTaylorMoment k zetaPositiveCompositeResponse s‖ ≤
      (signedTaylorMoment k zetaPositiveCompositeResponse (s.re : ℂ)).re := by
  have hr := Complex.hasSum_re
    (hasSum_zetaPositiveCompositeMoment k (by simpa using hs : 1 < (s.re : ℂ).re))
  apply (hasSum_zetaPositiveCompositeMoment k hs).norm_le_of_bounded hr
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zetaPositiveCompositeLogWeight_nonneg k n), norm_feature, feature_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, le_refl]

/-- An unconditional inequality for the fixed actual zeta expression
at every complex Euler point. -/
theorem norm_zetaPositiveCompositeResponse_le_real {s : ℂ} (hs : 1 < s.re) :
    ‖zetaPositiveCompositeResponse s‖ ≤ (zetaPositiveCompositeResponse (s.re : ℂ)).re := by
  simpa [signedTaylorMoment] using norm_zetaPositiveCompositeMoment_le_real 0 hs

/-- The complete mixed complex moment matrix, for arbitrary probe sets. -/
def zetaPositiveCompositeMomentGram {ι : Type*} (k : ℕ) (s : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ signedTaylorMoment k zetaPositiveCompositeResponse (conj (s i) + s j)

/-- Each mixed matrix entry retains its convergent feature factorization. -/
theorem hasSum_zetaPositiveCompositeMomentGram_entry (k : ℕ) {s t : ℂ}
    (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    HasSum (fun n ↦ (zetaPositiveCompositeLogWeight k n : ℂ) *
      conj (zetaPrimeFeature s n) * zetaPrimeFeature t n)
      (signedTaylorMoment k zetaPositiveCompositeResponse (conj s + t)) := by
  have hst : 1 < (conj s + t).re := by simp only [Complex.add_re, Complex.conj_re]; linarith
  apply (hasSum_zetaPositiveCompositeMoment k hst).congr_fun
  intro n
  rw [mul_assoc, zetaPrimeFeature_mixed]

private theorem gram_atom_energy {ι : Type*} [Fintype ι]
    (k : ℕ) (s c : ι → ℂ) (n : ℕ) :
    (∑ i, ∑ j, conj (c i) * c j * ((zetaPositiveCompositeLogWeight k n : ℂ) *
      conj (zetaPrimeFeature (s i) n) * zetaPrimeFeature (s j) n)) =
      ((zetaPositiveCompositeLogWeight k n *
        Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Arbitrary finite complex probes and coefficients retain all cross
terms in one exact convergent arithmetic energy, for every moment order. -/
theorem hasSum_zetaPositiveCompositeMomentGram_energy_complex {ι : Type*} [Fintype ι]
    (k : ℕ) (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    HasSum (fun n ↦ ((zetaPositiveCompositeLogWeight k n *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n) : ℝ) : ℂ))
      (∑ i, ∑ j, conj (c i) * c j * zetaPositiveCompositeMomentGram k s i j) := by
  have h (i j : ι) := (hasSum_zetaPositiveCompositeMomentGram_entry k (hs i) (hs j)).mul_left
    (conj (c i) * c j)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.univ) (fun j _ ↦ h i j))
  exact hsum.congr_fun (fun n ↦ (gram_atom_energy k s c n).symm)

/-- The real energy identity follows only after the entire complex
matrix and its genuinely convergent series have been retained. -/
theorem hasSum_zetaPositiveCompositeMomentGram_energy {ι : Type*} [Fintype ι]
    (k : ℕ) (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    HasSum (fun n ↦ zetaPositiveCompositeLogWeight k n *
      Complex.normSq (∑ i, c i * zetaPrimeFeature (s i) n))
      (∑ i, ∑ j, conj (c i) * c j * zetaPositiveCompositeMomentGram k s i j).re := by
  simpa only [Complex.ofReal_re] using
    Complex.hasSum_re (hasSum_zetaPositiveCompositeMomentGram_energy_complex k s c hs)

/-- Every full mixed moment energy is nonnegative for arbitrary complex
coefficients. There is no restriction to a chosen phase or frequency family. -/
theorem zetaPositiveCompositeMomentGram_energy_nonneg {ι : Type*} [Fintype ι]
    (k : ℕ) (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * zetaPositiveCompositeMomentGram k s i j).re := by
  rw [← (hasSum_zetaPositiveCompositeMomentGram_energy k s c hs).tsum_eq]
  exact tsum_nonneg (fun n ↦ mul_nonneg (zetaPositiveCompositeLogWeight_nonneg k n)
    (Complex.normSq_nonneg _))

/-- The exact arithmetic kernel of any analytic cofactor times the
positive response, including every derivative of that cofactor. -/
theorem hasSum_signedTaylorMoment_mul_zetaPositiveCompositeResponse {A : ℂ → ℂ} {s : ℂ}
    (hs : 1 < s.re) (hA : AnalyticAt ℂ A s) (N : ℕ) :
    HasSum (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ) * zetaPrimeFeature s n *
      ∑ k ∈ Finset.range (N + 1), signedTaylorMoment k A s *
        ((Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ)))
      (signedTaylorMoment N (fun z ↦ A z * zetaPositiveCompositeResponse z) s) := by
  have he : (fun z ↦ A z * zetaPositiveCompositeResponse z) =ᶠ[𝓝 s]
      (fun z ↦ A z * LSeries (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ)) z) :=
    (Filter.EventuallyEq.refl _ _).mul (response_eventuallyEq hs)
  rw [signedTaylorMoment_congr N he]
  exact hasSum_signedTaylorMoment_mul_LSeries _ (by simp) hA
    (lt_of_le_of_lt abscissaOfAbsConv_zetaPositiveComposite_le_one (by exact_mod_cast hs)) N

/-- Only one derivative remains outside the nonnegative arithmetic
convolution in the existing filtered Wronskian. -/
def zetaWronskianPositiveCofactor (rho : NontrivialZetaZero) (s : ℂ) : ℂ :=
  zetaWronskianMomentWeight rho s *
    (-deriv riemannZeta s / (s - rho.1) ^ ((analyticZetaZeroMultiplicity rho : ℤ) - 1))

private theorem positive_cofactor_analytic (rho : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (zetaWronskianPositiveCofactor rho) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hsr : s ≠ rho.1 := by intro h; rw [h] at hs; linarith [NontrivialZetaZero.re_lt_one rho]
  have hz := analyticOn_riemannZeta s (by simpa using hs1)
  exact (analyticAt_zetaWronskianMomentWeight rho s).mul
    (hz.deriv.neg.div ((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hsr))
      (zpow_ne_zero _ (sub_ne_zero.mpr hsr)))

/-- The old composite moment is transported exactly to the universal
positive response, preserving the derivative cofactor and every phase. -/
theorem zetaWronskianCompositeMoment_eq_positiveResponse (rho : NontrivialZetaZero) (N : ℕ) :
    zetaWronskianCompositeMoment rho N =
      signedTaylorMoment N (fun s ↦ zetaWronskianPositiveCofactor rho s *
        zetaPositiveCompositeResponse s) (zetaWronskianMomentCenter rho) := by
  unfold zetaWronskianCompositeMoment
  congr 1
  funext s
  simp only [Pi.mul_apply, zetaMoebiusCompositeWronskian_eq_positiveResponse,
    zetaWronskianPositiveCofactor, mul_assoc]

/-- The complete remaining Wronskian source is a genuinely convergent
sum with the proved nonnegative coefficients. Its cofactor kernel remains
complex; this theorem does not assert that the filtered sum is positive. -/
theorem hasSum_zetaWronskianCompositeMoment_positive (rho : NontrivialZetaZero) (N : ℕ) :
    HasSum (fun n ↦ (zetaPositiveCompositeArithmetic n : ℂ) *
      zetaPrimeFeature (zetaWronskianMomentCenter rho) n *
        ∑ k ∈ Finset.range (N + 1),
          signedTaylorMoment k (zetaWronskianPositiveCofactor rho) (zetaWronskianMomentCenter rho) *
            ((Real.log n : ℂ) ^ (N - k) / ((N - k).factorial : ℂ)))
      (zetaWronskianCompositeMoment rho N) := by
  rw [zetaWronskianCompositeMoment_eq_positiveResponse]
  exact hasSum_signedTaylorMoment_mul_zetaPositiveCompositeResponse
    (by norm_num [zetaWronskianMomentCenter])
    (positive_cofactor_analytic rho (by norm_num [zetaWronskianMomentCenter])) N

end

end RiemannGaussian
