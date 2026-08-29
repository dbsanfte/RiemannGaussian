import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalizedLargeTime
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentGapDefect

/-!
# The first large-time coefficient of the localized infinite eta Gram

The large-proper-time localized Gram is controlled by powers of the
logarithmic-time difference `u - t`.  This module connects those product
moments to the already formalized one-variable paired-eta logarithmic
moments.

At a nontrivial zero of multiplicity `m`, every difference moment of order
strictly below `2m` vanishes.  The order-`2m` moment is the central binomial
coefficient times the squared norm of the first nonzero eta moment, with the
exact sign needed to cancel the sign in the Gaussian Taylor series.  Thus the
first formal large-time coefficient is explicit and strictly positive.

No zero-location conclusion is asserted here: complementary symmetry still
permits unequal raw coefficients after the completion weights are removed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complex product kernel whose real part is the `n`th polynomial
difference moment of the undamped localized eta Gram. -/
def pairedEtaComplexLogDifferenceKernel
    (n : ℕ) (sigma gamma : ℝ) (p : ℝ × ℝ) : ℂ :=
  (((p.1 - p.2 : ℝ) : ℂ) ^ n) *
    (Real.exp (-sigma * (p.1 + p.2)) : ℂ) *
    Complex.exp
      (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))

/-- The complex difference kernel is the product of the two tilted Laplace
integrands, with the polynomial difference inserted. -/
theorem pairedEtaComplexLogDifferenceKernel_eq_laplaceProduct
    (n : ℕ) (sigma gamma : ℝ) (p : ℝ × ℝ) :
    pairedEtaComplexLogDifferenceKernel n sigma gamma p =
      (((p.1 : ℂ) - (p.2 : ℂ)) ^ n) *
        Complex.exp
          (-((sigma : ℂ) + (gamma : ℂ) * Complex.I) * p.1) *
        starRingEnd ℂ
          (Complex.exp
            (-((sigma : ℂ) + (gamma : ℂ) * Complex.I) * p.2)) := by
  unfold pairedEtaComplexLogDifferenceKernel
  rw [Complex.ofReal_exp, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_add, Complex.conj_ofReal,
    Complex.conj_I, neg_mul]
  have hpoly : (((p.1 - p.2 : ℝ) : ℂ) ^ n) =
      ((p.1 : ℂ) - (p.2 : ℂ)) ^ n := by
    simp
  have hexp : Complex.exp ((-(sigma * (p.1 + p.2)) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ)) =
    Complex.exp (-((sigma : ℂ) + (gamma : ℂ) * Complex.I) * p.1) *
      Complex.exp (-((sigma : ℂ) + (gamma : ℂ) * -Complex.I) * p.2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im] <;>
      ring
  calc
    (((p.1 - p.2 : ℝ) : ℂ) ^ n) *
          Complex.exp ((-(sigma * (p.1 + p.2)) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ)) =
        (((p.1 : ℂ) - (p.2 : ℂ)) ^ n) *
          (Complex.exp ((-(sigma * (p.1 + p.2)) : ℝ) : ℂ) *
            Complex.exp
              (Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ))) := by
      rw [hpoly]
      ring
    _ = (((p.1 : ℂ) - (p.2 : ℂ)) ^ n) *
          (Complex.exp
              (-((sigma : ℂ) + (gamma : ℂ) * Complex.I) * p.1) *
            Complex.exp
              (-((sigma : ℂ) + (gamma : ℂ) * -Complex.I) * p.2)) := by
      rw [hexp]
    _ = _ := by
      rw [mul_assoc]
      congr 2 <;> ring_nf

/-- The real part of the complex difference kernel is exactly the polynomial
moment of the undamped localized real kernel. -/
theorem pairedEtaComplexLogDifferenceKernel_re
    (n : ℕ) (sigma gamma : ℝ) (p : ℝ × ℝ) :
    (pairedEtaComplexLogDifferenceKernel n sigma gamma p).re =
      (p.1 - p.2) ^ n *
        pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p := by
  unfold pairedEtaComplexLogDifferenceKernel
    pairedEtaUndampedLocalizedLaplaceKernel
  rw [← Complex.ofReal_pow]
  rw [show Complex.I * ((gamma * (p.2 - p.1) : ℝ) : ℂ) =
      ((gamma * (p.2 - p.1) : ℝ) : ℂ) * Complex.I by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- The binomial convolution giving the `n`th complex logarithmic-time
difference moment of the paired-eta product measure. -/
def pairedEtaComplexLogDifferenceMoment (n : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (j + n) * (n.choose j : ℂ) *
      pairedEtaLogLaplaceMoment j s *
      starRingEnd ℂ (pairedEtaLogLaplaceMoment (n - j) s)

/-- The complex difference kernel is integrable at every positive horizontal
tilt. -/
theorem integrable_pairedEtaComplexLogDifferenceKernel
    (n : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    Integrable (pairedEtaComplexLogDifferenceKernel n sigma gamma)
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
  let s : ℂ := (sigma : ℂ) + (gamma : ℂ) * Complex.I
  have hs : 0 < s.re := by simp [s, hsigma]
  have hfun : pairedEtaComplexLogDifferenceKernel n sigma gamma =
      fun p : ℝ × ℝ ↦
        ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ (j + n) * (n.choose j : ℂ) *
            (((p.1 : ℂ) ^ j * Complex.exp (-s * p.1)) *
              starRingEnd ℂ
                ((p.2 : ℂ) ^ (n - j) *
                  Complex.exp (-s * p.2))) := by
    funext p
    rw [pairedEtaComplexLogDifferenceKernel_eq_laplaceProduct]
    change (((p.1 : ℂ) - (p.2 : ℂ)) ^ n) *
        Complex.exp (-s * p.1) *
        starRingEnd ℂ (Complex.exp (-s * p.2)) = _
    rw [sub_pow, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    ring
  rw [hfun]
  apply integrable_finsetSum
  intro j hj
  have hleft := integrable_pairedEtaLogLaplaceMoment j hs
  have hrightBase := integrable_pairedEtaLogLaplaceMoment (n - j) hs
  have hright : Integrable (fun u : ℝ ↦
      starRingEnd ℂ
        ((u : ℂ) ^ (n - j) * Complex.exp (-s * u)))
      pairedEtaLogMeasure := by
    apply hrightBase.mono
    · exact (show Continuous (fun u : ℝ ↦
          starRingEnd ℂ
            ((u : ℂ) ^ (n - j) * Complex.exp (-s * u))) by
          fun_prop).aestronglyMeasurable
    · exact Eventually.of_forall fun u => by simp
  exact (hleft.mul_prod hright).const_mul
    ((-1 : ℂ) ^ (j + n) * (n.choose j : ℂ))

/-- Integrating the complex product kernel gives exactly the binomial
convolution of the one-variable eta log moments. -/
theorem integral_pairedEtaComplexLogDifferenceKernel_eq_moment
    (n : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    (∫ p : ℝ × ℝ,
        pairedEtaComplexLogDifferenceKernel n sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      pairedEtaComplexLogDifferenceMoment n
        ((sigma : ℂ) + (gamma : ℂ) * Complex.I) := by
  let s : ℂ := (sigma : ℂ) + (gamma : ℂ) * Complex.I
  have hs : 0 < s.re := by simp [s, hsigma]
  have hleft : ∀ j : ℕ, Integrable (fun t : ℝ ↦
      (t : ℂ) ^ j * Complex.exp (-s * t)) pairedEtaLogMeasure :=
    fun j => integrable_pairedEtaLogLaplaceMoment j hs
  have hright : ∀ j : ℕ, Integrable (fun u : ℝ ↦
      starRingEnd ℂ ((u : ℂ) ^ j * Complex.exp (-s * u)))
      pairedEtaLogMeasure := by
    intro j
    apply (hleft j).mono
    · exact (show Continuous (fun u : ℝ ↦
          starRingEnd ℂ ((u : ℂ) ^ j * Complex.exp (-s * u))) by
          fun_prop).aestronglyMeasurable
    · exact Eventually.of_forall fun u => by simp
  rw [show pairedEtaComplexLogDifferenceKernel n sigma gamma =
      fun p : ℝ × ℝ ↦
        ∑ j ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ (j + n) * (n.choose j : ℂ) *
            (((p.1 : ℂ) ^ j * Complex.exp (-s * p.1)) *
              starRingEnd ℂ
                ((p.2 : ℂ) ^ (n - j) *
                  Complex.exp (-s * p.2))) by
    funext p
    rw [pairedEtaComplexLogDifferenceKernel_eq_laplaceProduct]
    change (((p.1 : ℂ) - (p.2 : ℂ)) ^ n) *
        Complex.exp (-s * p.1) *
        starRingEnd ℂ (Complex.exp (-s * p.2)) = _
    rw [sub_pow, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    ring]
  rw [integral_finsetSum (Finset.range (n + 1))]
  · unfold pairedEtaComplexLogDifferenceMoment
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul,
      integral_prod_mul
        (μ := pairedEtaLogMeasure) (ν := pairedEtaLogMeasure)
        (fun t : ℝ ↦ (t : ℂ) ^ j * Complex.exp (-s * t))
        (fun u : ℝ ↦ starRingEnd ℂ
          ((u : ℂ) ^ (n - j) * Complex.exp (-s * u))),
      integral_conj]
    unfold pairedEtaLogLaplaceMoment
    dsimp only [s]
    ring
  · intro j hj
    exact (hleft j |>.mul_prod (hright (n - j))).const_mul
      ((-1 : ℂ) ^ (j + n) * (n.choose j : ℂ))

/-- The real polynomial difference moment of the undamped localized kernel
is the real part of the explicit complex moment convolution. -/
theorem integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_eq_re_moment
    (n : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) :
    (∫ p : ℝ × ℝ,
        (p.1 - p.2) ^ n *
          pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      (pairedEtaComplexLogDifferenceMoment n
        ((sigma : ℂ) + (gamma : ℂ) * Complex.I)).re := by
  have hint := integrable_pairedEtaComplexLogDifferenceKernel n hsigma gamma
  calc
    (∫ p : ℝ × ℝ,
        (p.1 - p.2) ^ n *
          pairedEtaUndampedLocalizedLaplaceKernel sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      ∫ p : ℝ × ℝ,
        (pairedEtaComplexLogDifferenceKernel n sigma gamma p).re
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun p =>
            (pairedEtaComplexLogDifferenceKernel_re n sigma gamma p).symm
    _ = (∫ p : ℝ × ℝ,
        pairedEtaComplexLogDifferenceKernel n sigma gamma p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)).re :=
      integral_re hint
    _ = _ := congrArg Complex.re
      (integral_pairedEtaComplexLogDifferenceKernel_eq_moment
        n hsigma gamma)

/-- At a zero of multiplicity `m`, every complex difference moment below
order `2m` vanishes. -/
theorem pairedEtaComplexLogDifferenceMoment_eq_zero_of_lt_twice_multiplicity
    (rho : NontrivialZetaZero) {n : ℕ}
    (hn : n < 2 * analyticZetaZeroMultiplicity rho) :
    pairedEtaComplexLogDifferenceMoment n rho.1 = 0 := by
  classical
  unfold pairedEtaComplexLogDifferenceMoment
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  by_cases hjm : j < analyticZetaZeroMultiplicity rho
  · rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hjm]
    ring
  · have hmj : analyticZetaZeroMultiplicity rho ≤ j := Nat.le_of_not_gt hjm
    have hsub : n - j < analyticZetaZeroMultiplicity rho := by omega
    rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hsub]
    simp

/-- The first nonzero complex difference moment is exactly the central
binomial coefficient times the signed squared norm of the leading eta
moment. -/
theorem pairedEtaComplexLogDifferenceMoment_twice_multiplicity
    (rho : NontrivialZetaZero) :
    pairedEtaComplexLogDifferenceMoment
        (2 * analyticZetaZeroMultiplicity rho) rho.1 =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        ((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℂ) *
        Complex.normSq
          (pairedEtaLogLaplaceMoment
            (analyticZetaZeroMultiplicity rho) rho.1) := by
  classical
  let m := analyticZetaZeroMultiplicity rho
  unfold pairedEtaComplexLogDifferenceMoment
  rw [Finset.sum_eq_single m]
  · change (-1 : ℂ) ^ (m + 2 * m) * ((2 * m).choose m : ℂ) *
        pairedEtaLogLaplaceMoment m rho.1 *
        starRingEnd ℂ (pairedEtaLogLaplaceMoment (2 * m - m) rho.1) =
      (-1 : ℂ) ^ m * ((2 * m).choose m : ℂ) *
        Complex.normSq (pairedEtaLogLaplaceMoment m rho.1)
    rw [show 2 * m - m = m by omega]
    calc
      (-1 : ℂ) ^ (m + 2 * m) * ((2 * m).choose m : ℂ) *
            pairedEtaLogLaplaceMoment m rho.1 *
            starRingEnd ℂ (pairedEtaLogLaplaceMoment m rho.1) =
          (-1 : ℂ) ^ (m + 2 * m) * ((2 * m).choose m : ℂ) *
            Complex.normSq (pairedEtaLogLaplaceMoment m rho.1) := by
        rw [show
          (-1 : ℂ) ^ (m + 2 * m) * ((2 * m).choose m : ℂ) *
                pairedEtaLogLaplaceMoment m rho.1 *
                starRingEnd ℂ (pairedEtaLogLaplaceMoment m rho.1) =
              (-1 : ℂ) ^ (m + 2 * m) * ((2 * m).choose m : ℂ) *
                (pairedEtaLogLaplaceMoment m rho.1 *
                  starRingEnd ℂ (pairedEtaLogLaplaceMoment m rho.1)) by ring,
          Complex.mul_conj]
      _ = _ := by
        congr 2
        rw [pow_add, pow_mul]
        norm_num
  · intro j hj hjne
    have hjle : j ≤ 2 * m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    by_cases hjm : j < m
    · rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hjm]
      ring
    · have hmj : m ≤ j := Nat.le_of_not_gt hjm
      have hmjStrict : m < j := lt_of_le_of_ne hmj (Ne.symm hjne)
      have hsub : 2 * m - j < m := by omega
      rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho hsub]
      simp
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_range]
    dsimp only [m]
    omega

/-- Every real polynomial difference moment occurring before the first
possible Gaussian coefficient vanishes at a nontrivial zero. -/
theorem
    integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_eq_zero_of_lt_twice_multiplicity
    (rho : NontrivialZetaZero) {n : ℕ}
    (hn : n < 2 * analyticZetaZeroMultiplicity rho) :
    (∫ p : ℝ × ℝ,
        (p.1 - p.2) ^ n *
          pairedEtaUndampedLocalizedLaplaceKernel
            rho.1.re rho.1.im p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) = 0 := by
  rw [integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_eq_re_moment
    n (NontrivialZetaZero.zero_lt_re rho) rho.1.im]
  rw [Complex.re_add_im rho.1,
    pairedEtaComplexLogDifferenceMoment_eq_zero_of_lt_twice_multiplicity
      rho hn]
  rfl

/-- The first nonzero real polynomial difference moment has the exact
central-binomial value and alternating sign. -/
theorem
    integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_twice_multiplicity
    (rho : NontrivialZetaZero) :
    (∫ p : ℝ × ℝ,
        (p.1 - p.2) ^ (2 * analyticZetaZeroMultiplicity rho) *
          pairedEtaUndampedLocalizedLaplaceKernel
            rho.1.re rho.1.im p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      (-1 : ℝ) ^ (analyticZetaZeroMultiplicity rho) *
        ((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℝ) *
        Complex.normSq
          (pairedEtaLogLaplaceMoment
            (analyticZetaZeroMultiplicity rho) rho.1) := by
  rw [integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_eq_re_moment
    (2 * analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho) rho.1.im]
  rw [Complex.re_add_im rho.1,
    pairedEtaComplexLogDifferenceMoment_twice_multiplicity rho]
  have hsigncast : (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho =
      (((-1 : ℝ) ^ analyticZetaZeroMultiplicity rho : ℝ) : ℂ) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_pow]
  rw [hsigncast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num

/-- The positive scalar multiplying `tau⁻ᵐ` in the formal large-time
Gaussian expansion at a zero of multiplicity `m`. -/
def pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
    (rho : NontrivialZetaZero) : ℝ :=
  (((2 * analyticZetaZeroMultiplicity rho).choose
      (analyticZetaZeroMultiplicity rho) : ℝ) *
    Complex.normSq
      (pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1)) /
    (4 ^ analyticZetaZeroMultiplicity rho *
      (analyticZetaZeroMultiplicity rho).factorial)

/-- Multiplying the first surviving real difference moment by the matching
Gaussian Taylor coefficient produces the positive leading coefficient. -/
theorem pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_eq
    (rho : NontrivialZetaZero) :
    ((-1 : ℝ) ^ (analyticZetaZeroMultiplicity rho) /
        (4 ^ analyticZetaZeroMultiplicity rho *
          (analyticZetaZeroMultiplicity rho).factorial)) *
      (∫ p : ℝ × ℝ,
        (p.1 - p.2) ^ (2 * analyticZetaZeroMultiplicity rho) *
          pairedEtaUndampedLocalizedLaplaceKernel
            rho.1.re rho.1.im p
        ∂(pairedEtaLogMeasure.prod pairedEtaLogMeasure)) =
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  rw [integral_pow_sub_mul_pairedEtaUndampedLocalizedLaplaceKernel_twice_multiplicity]
  unfold pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
  have hsign : (-1 : ℝ) ^
      (analyticZetaZeroMultiplicity rho * 2) = 1 := by
    rw [Nat.mul_comm, pow_mul]
    norm_num
  rw [div_mul_eq_mul_div]
  ring_nf
  rw [hsign]
  ring

/-- The real coefficient left after multiplying the first nonzero difference
moment by the matching Gaussian Taylor sign is strictly positive. -/
theorem pairedEtaLargeTimeLeadingDifferenceCoefficient_pos
    (rho : NontrivialZetaZero) :
    0 < ((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℝ) *
        Complex.normSq
          (pairedEtaLogLaplaceMoment
            (analyticZetaZeroMultiplicity rho) rho.1) := by
  have hchoose : 0 < (2 * analyticZetaZeroMultiplicity rho).choose
      (analyticZetaZeroMultiplicity rho) := by
    exact Nat.choose_pos (by omega)
  exact mul_pos (Nat.cast_pos.mpr hchoose)
    (Complex.normSq_pos.mpr
      (pairedEtaLogLaplaceMoment_multiplicity_ne_zero rho))

/-- The actual formal large-time Gaussian coefficient, including its power
of four and factorial denominator, is strictly positive. -/
theorem pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos
    (rho : NontrivialZetaZero) :
    0 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  unfold pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
  exact div_pos (pairedEtaLargeTimeLeadingDifferenceCoefficient_pos rho)
    (mul_pos (pow_pos (by norm_num) _)
      (Nat.cast_pos.mpr (Nat.factorial_pos _)))

/-- Completion symmetry preserves the leading large-time coefficient after
multiplication by the square of the exact completion-and-spectral weight.
This is the coefficient-level form of the complementary-zero coupling. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner
    (rho : NontrivialZetaZero) :
    (‖pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖(NontrivialZetaZero.conjugatePartner rho).1‖) ^ 2 *
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) =
      (‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖) ^ 2 *
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho := by
  have hnorm :=
    norm_pairedEtaLeadingLogLaplaceMoment_conjugatePartner rho
  have hsq := congrArg (fun x : ℝ ↦ x ^ 2) hnorm
  have hcore :
      (‖pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1‖ *
          ‖(NontrivialZetaZero.conjugatePartner rho).1‖) ^ 2 *
          Complex.normSq
            (pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1) =
        (‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖) ^ 2 *
          Complex.normSq
            (pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1) := by
    simpa only [Complex.normSq_eq_norm_sq, mul_pow] using hsq
  unfold pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
  simp only [analyticZetaZeroMultiplicity_conjugatePartner]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (‖pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1‖ *
          ‖(NontrivialZetaZero.conjugatePartner rho).1‖) ^ 2 *
        ((((2 * analyticZetaZeroMultiplicity rho).choose
            (analyticZetaZeroMultiplicity rho) : ℝ) *
          Complex.normSq
            (pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1)) *
          (((4 : ℝ) ^ analyticZetaZeroMultiplicity rho) *
            ((analyticZetaZeroMultiplicity rho).factorial : ℝ))⁻¹) =
      (((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℝ) *
        (((4 : ℝ) ^ analyticZetaZeroMultiplicity rho) *
          ((analyticZetaZeroMultiplicity rho).factorial : ℝ))⁻¹) *
        ((‖pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1‖ *
            ‖(NontrivialZetaZero.conjugatePartner rho).1‖) ^ 2 *
          Complex.normSq
            (pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho)
              (NontrivialZetaZero.conjugatePartner rho).1)) := by ring
    _ = (((2 * analyticZetaZeroMultiplicity rho).choose
          (analyticZetaZeroMultiplicity rho) : ℝ) *
        (((4 : ℝ) ^ analyticZetaZeroMultiplicity rho) *
          ((analyticZetaZeroMultiplicity rho).factorial : ℝ))⁻¹) *
        ((‖pairedEtaXiCompletionFactor rho.1‖ * ‖rho.1‖) ^ 2 *
          Complex.normSq
            (pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1)) := by
      rw [hcore]
    _ = _ := by ring

end

end RiemannGaussian
