import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionLogSlope
import RiemannGaussian.GaussianDigammaGauss

/-!
# High-ordinate rigidity of the eta reflection multiplier

The preceding module reduces horizontal variation of the eta reflection
multiplier to one explicit shifted-digamma and dyadic expression. Here that
expression is proved strictly positive throughout the complete open critical
strip whenever the absolute ordinate is at least `8`.

The proof is uniform and analytic. Euler's convergent digamma series gives a
positive vertical correction; four exact terms, together with the standard
checked Euler-constant bound, give a rational lower bound. Each dyadic term is
controlled by the elementary disk inequality
`1 / 2 < Re (1 - q)⁻¹` for `‖q‖ < 1`. A certified exponential bound for
`log pi` then closes the strict estimate.

Consequently the same-ordinate multiplier log norm is strictly increasing in
the horizontal coordinate at every such ordinate, and unit norm is equivalent
to the critical-line equation there. No theorem in this module asserts that
all nontrivial zeta zeros have absolute ordinate at least `8`, nor does it
force the multiplier to have unit norm at a zero. Those are separate open
inputs.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- On the positive real axis from `1` onward, the real digamma is bounded
below by its value `-EulerGamma` at `1`. -/
theorem re_digamma_of_one_le_of_re_pos
    {a : ℝ} (ha1 : 1 ≤ a) :
    -Real.eulerMascheroniConstant ≤ (Complex.digamma (a : ℂ)).re := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hlimA := Complex.continuous_re.tendsto _ |>.comp
    (Complex.digamma_tendsto_euler (s := (a : ℂ)) (by simpa using ha))
  have hlimOne := Complex.continuous_re.tendsto _ |>.comp
    (Complex.digamma_tendsto_euler (s := (1 : ℂ)) (by norm_num))
  have hle : ∀ n : ℕ,
      (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), ((1 : ℂ) + j)⁻¹).re ≤
        (Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), ((a : ℂ) + j)⁻¹).re := by
    intro n
    simp only [Complex.sub_re, Complex.re_sum]
    apply sub_le_sub_left
    apply Finset.sum_le_sum
    intro j hj
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpos1 : 0 < (1 : ℝ) + j := by positivity
    have hposa : 0 < a + j := by positivity
    have honeCast : (1 : ℂ) + (j : ℂ) = (((1 : ℝ) + j : ℝ) : ℂ) := by
      push_cast
      rfl
    have haCast : (a : ℂ) + (j : ℂ) = ((a + j : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [honeCast, haCast, Complex.re_inv_ofReal hpos1.ne',
      Complex.re_inv_ofReal hposa.ne']
    simpa [one_div] using
      (inv_le_inv₀ hposa hpos1).2 (by linarith : (1 : ℝ) + j ≤ a + j)
  have hlimits :
      (Complex.digamma (1 : ℂ)).re ≤
        (Complex.digamma (a : ℂ)).re :=
    le_of_tendsto_of_tendsto' hlimOne hlimA hle
  rw [Complex.digamma_one] at hlimits
  simpa using hlimits

private theorem ratio_sq_add_mono_parameter
    {x u v : ℝ} (hx : 0 < x) (hv : 0 ≤ v) (hvu : v ≤ u) :
    v / (x * (x ^ 2 + v)) ≤ u / (x * (x ^ 2 + u)) := by
  have hu : 0 ≤ u := hv.trans hvu
  have hdv : 0 < x * (x ^ 2 + v) := by positivity
  have hdu : 0 < x * (x ^ 2 + u) := by positivity
  rw [div_le_div_iff₀ hdv hdu]
  have hx3 : 0 ≤ x ^ 3 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hvu) hx3]

private theorem ratio_sq_add_anti_base
    {x X v : ℝ} (hx : 0 < x) (hxX : x ≤ X) (hv : 0 ≤ v) :
    v / (X * (X ^ 2 + v)) ≤ v / (x * (x ^ 2 + v)) := by
  have hX : 0 < X := hx.trans_le hxX
  have hsq : x ^ 2 ≤ X ^ 2 := by nlinarith
  have hden : x * (x ^ 2 + v) ≤ X * (X ^ 2 + v) := by
    exact mul_le_mul hxX (add_le_add hsq le_rfl) (by positivity) hX.le
  exact div_le_div_of_nonneg_left hv (by positivity) hden

/-- A Gauss-series digamma correction term has a uniform lower bound after
enlarging its real base and lowering the square of its ordinate. -/
theorem digammaRealDifferenceTerm_ge_uniform
    {a A b B : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hB : 0 ≤ B) (hBb : B ≤ b ^ 2) (j : ℕ) :
    B / ((A + j) * ((A + j) ^ 2 + B)) ≤
      Complex.digammaRealDifferenceTerm a b j := by
  have hx : 0 < a + (j : ℝ) := by positivity
  have hxX : a + (j : ℝ) ≤ A + j := by linarith
  unfold Complex.digammaRealDifferenceTerm
  rw [show 1 / (a + (j : ℝ)) -
      (a + j) / ((a + j) ^ 2 + b ^ 2) =
      b ^ 2 / ((a + j) * ((a + j) ^ 2 + b ^ 2)) by
    have hsum : 0 < (a + (j : ℝ)) ^ 2 + b ^ 2 := by positivity
    field_simp [hx.ne', hsum.ne']
    ring]
  exact (ratio_sq_add_anti_base hx hxX hB).trans
    (ratio_sq_add_mono_parameter hx hB hBb)

/-- Uniform explicit lower bound for the real digamma on
`1 ≤ Re z ≤ 3/2` and `4 ≤ |Im z|`. -/
theorem re_digamma_gt_23_over_50_of_four_le_abs_im
    {a b : ℝ} (ha1 : 1 ≤ a) (haA : a ≤ 3 / 2)
    (hb : 4 ≤ |b|) :
    23 / 50 <
      (Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I)).re := by
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hbSq : (16 : ℝ) ≤ b ^ 2 := by
    have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg b)).2 hb
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hsum := Complex.hasSum_digammaRealDifferenceTerm ha b
  have hfinite :
      (∑ j ∈ Finset.range 4,
          Complex.digammaRealDifferenceTerm a b j) ≤
        (Complex.digamma
            ((a : ℂ) + (b : ℂ) * Complex.I)).re -
          (Complex.digamma (a : ℂ)).re := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum (Finset.range 4)
      (fun j _hj => Complex.digammaRealDifferenceTerm_nonneg ha b j)
  have hterm (j : ℕ) :
      (16 : ℝ) /
          (((3 / 2 : ℝ) + j) * (((3 / 2 : ℝ) + j) ^ 2 + 16)) ≤
        Complex.digammaRealDifferenceTerm a b j :=
    digammaRealDifferenceTerm_ge_uniform ha haA (by norm_num) hbSq j
  have hfixed :
      (∑ j ∈ Finset.range 4,
          (16 : ℝ) /
            (((3 / 2 : ℝ) + j) * (((3 / 2 : ℝ) + j) ^ 2 + 16))) ≤
        ∑ j ∈ Finset.range 4,
          Complex.digammaRealDifferenceTerm a b j := by
    exact Finset.sum_le_sum fun j _hj => hterm j
  have hfixedValue :
      (113 / 100 : ℝ) <
        ∑ j ∈ Finset.range 4,
          (16 : ℝ) /
            (((3 / 2 : ℝ) + j) * (((3 / 2 : ℝ) + j) ^ 2 + 16)) := by
    norm_num [Finset.sum_range_succ]
  have hbase := re_digamma_of_one_le_of_re_pos ha1
  have heuler := Real.eulerMascheroniConstant_lt_two_thirds
  nlinarith

/-- The real part of the reciprocal disk resolvent is strictly greater than
one half inside the unit disk. -/
theorem half_lt_re_inv_one_sub_of_norm_lt_one
    {q : ℂ} (hq : ‖q‖ < 1) :
    1 / 2 < ((1 - q)⁻¹).re := by
  have hqne : 1 - q ≠ 0 := by
    intro h
    have hqone : q = 1 := by linear_combination -h
    rw [hqone, norm_one] at hq
    exact hq.false
  have hden : 0 < Complex.normSq (1 - q) :=
    Complex.normSq_pos.mpr hqne
  have hnormSq : Complex.normSq q < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg q]
  rw [Complex.inv_re]
  apply (lt_div_iff₀ hden).2
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, zero_sub]
  rw [Complex.normSq_apply] at hnormSq
  nlinarith [sq_nonneg q.im]

/-- Multiplying the disk-resolvent estimate by `log 2` gives the uniform
lower bound used for each dyadic term. -/
theorem re_log_two_div_one_sub_gt_half_log_two_of_norm_lt_one
    {q : ℂ} (hq : ‖q‖ < 1) :
    Real.log 2 / 2 < (Complex.log 2 / (1 - q)).re := by
  have hhalf := half_lt_re_inv_one_sub_of_norm_lt_one hq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlogC]
  conv_rhs => rw [div_eq_mul_inv, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

/-- The first dyadic power in the explicit reflection slope lies strictly
inside the unit disk when `Re s < 1`. -/
theorem norm_two_cpow_sub_one_lt_one
    {s : ℂ} (hslt : s.re < 1) :
    ‖(2 : ℂ) ^ (s - 1)‖ < 1 := by
  change ‖((2 : ℝ) : ℂ) ^ (s - 1)‖ < 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simpa using hslt)

/-- The second dyadic power in the explicit reflection slope lies strictly
inside the unit disk when `0 < Re s`. -/
theorem norm_two_cpow_neg_lt_one
    {s : ℂ} (hspos : 0 < s.re) :
    ‖(2 : ℂ) ^ (-s)‖ < 1 := by
  change ‖((2 : ℝ) : ℂ) ^ (-s)‖ < 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simpa using hspos)

private theorem log_pi_lt_23_over_20_reflection :
    Real.log Real.pi < 23 / 20 := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 20) 6
  have hpiExp : Real.pi < Real.exp (23 / 20) := by
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ < ∑ i ∈ Finset.range 6,
          (23 / 20 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (23 / 20) := hexponential
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpiExp

/-- At every ordinate of absolute value at least `8`, the explicit reflection
logarithmic slope has strictly positive real part across the whole open
critical strip. -/
theorem pairedEtaLaplaceReflectionDyadicLogSlope_re_pos_of_eight_le_abs_im
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1)
    (hy : 8 ≤ |s.im|) :
    0 < (pairedEtaLaplaceReflectionDyadicLogSlope s).re := by
  let a₁ : ℝ := 1 + s.re / 2
  let b₁ : ℝ := s.im / 2
  let a₂ : ℝ := 1 + (1 - s.re) / 2
  let b₂ : ℝ := -s.im / 2
  have ha₁one : 1 ≤ a₁ := by dsimp [a₁]; linarith
  have ha₁upper : a₁ ≤ 3 / 2 := by dsimp [a₁]; linarith
  have ha₂one : 1 ≤ a₂ := by dsimp [a₂]; linarith
  have ha₂upper : a₂ ≤ 3 / 2 := by dsimp [a₂]; linarith
  have hb₁ : 4 ≤ |b₁| := by
    dsimp [b₁]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hb₂ : 4 ≤ |b₂| := by
    dsimp [b₂]
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have harg₁ :
      1 + s / 2 = (a₁ : ℂ) + (b₁ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a₁, b₁]
  have harg₂ :
      1 + (1 - s) / 2 = (a₂ : ℂ) + (b₂ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [a₂, b₂]
  have hdigamma₁ :=
    re_digamma_gt_23_over_50_of_four_le_abs_im
      ha₁one ha₁upper hb₁
  have hdigamma₂ :=
    re_digamma_gt_23_over_50_of_four_le_abs_im
      ha₂one ha₂upper hb₂
  rw [← harg₁] at hdigamma₁
  rw [← harg₂] at hdigamma₂
  have hdyadic₁ :=
    re_log_two_div_one_sub_gt_half_log_two_of_norm_lt_one
      (norm_two_cpow_sub_one_lt_one hslt)
  have hdyadic₂ :=
    re_log_two_div_one_sub_gt_half_log_two_of_norm_lt_one
      (norm_two_cpow_neg_lt_one hspos)
  have hlogPi := log_pi_lt_23_over_20_reflection
  have hlogTwo := Real.log_two_gt_d9
  have havg :
      ((Complex.digamma (1 + s / 2) +
          Complex.digamma (1 + (1 - s) / 2)) / 2).re =
        ((Complex.digamma (1 + s / 2)).re +
          (Complex.digamma (1 + (1 - s) / 2)).re) / 2 := by
    rw [Complex.div_re]
    norm_num
    ring
  rw [show (pairedEtaLaplaceReflectionDyadicLogSlope s).re =
      -Real.log Real.pi +
        ((Complex.digamma (1 + s / 2)).re +
          (Complex.digamma (1 + (1 - s) / 2)).re) / 2 +
        (Complex.log 2 / (1 - (2 : ℂ) ^ (s - 1))).re +
        (Complex.log 2 / (1 - (2 : ℂ) ^ (-s))).re by
    unfold pairedEtaLaplaceReflectionDyadicLogSlope
    simp only [Complex.add_re, Complex.neg_re, Complex.log_ofReal_re]
    rw [havg]
  ]
  norm_num at hdigamma₁ hdigamma₂ hdyadic₁ hdyadic₂ ⊢
  nlinarith

/-- At absolute ordinate at least `8`, the same-ordinate multiplier log norm
is strictly increasing throughout the open critical strip. -/
theorem strictMonoOn_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs
    {y : ℝ} (hy : 8 ≤ |y|) :
    StrictMonoOn
      (fun sigma : ℝ => pairedEtaLaplaceReflectionLogNorm sigma y)
      (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (0 : ℝ) 1)
  · intro sigma hsigma
    exact (hasDerivAt_pairedEtaLaplaceReflectionLogNorm_dyadic
      hsigma.1 hsigma.2).continuousAt.continuousWithinAt
  · intro sigma hsigma
    have hsigma' : sigma ∈ Ioo (0 : ℝ) 1 := interior_subset hsigma
    rw [deriv_pairedEtaLaplaceReflectionLogNorm_eq_dyadicLogSlope_re
      hsigma'.1 hsigma'.2]
    apply pairedEtaLaplaceReflectionDyadicLogSlope_re_pos_of_eight_le_abs_im
    · simpa [Complex.mul_re] using hsigma'.1
    · simpa [Complex.mul_re] using hsigma'.2
    · simpa [Complex.mul_im] using hy

/-- Above the critical line in the horizontal coordinate, the high-ordinate
multiplier log norm is strictly positive. -/
theorem pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
    {sigma y : ℝ} (hhalf : 1 / 2 < sigma) (hslt : sigma < 1)
    (hy : 8 ≤ |y|) :
    0 < pairedEtaLaplaceReflectionLogNorm sigma y := by
  have hmono :=
    strictMonoOn_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs hy
  have h := hmono
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
    ⟨by linarith, hslt⟩ hhalf
  change pairedEtaLaplaceReflectionLogNorm (1 / 2) y <
    pairedEtaLaplaceReflectionLogNorm sigma y at h
  rw [pairedEtaLaplaceReflectionLogNorm_half] at h
  exact h

/-- Below the critical line in the horizontal coordinate, the high-ordinate
multiplier log norm is strictly negative. -/
theorem pairedEtaLaplaceReflectionLogNorm_neg_of_lt_half_of_eight_le_abs
    {sigma y : ℝ} (hspos : 0 < sigma) (hhalf : sigma < 1 / 2)
    (hy : 8 ≤ |y|) :
    pairedEtaLaplaceReflectionLogNorm sigma y < 0 := by
  have hmono :=
    strictMonoOn_pairedEtaLaplaceReflectionLogNorm_of_eight_le_abs hy
  have h := hmono ⟨hspos, by linarith⟩
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) hhalf
  change pairedEtaLaplaceReflectionLogNorm sigma y <
    pairedEtaLaplaceReflectionLogNorm (1 / 2) y at h
  rw [pairedEtaLaplaceReflectionLogNorm_half] at h
  exact h

/-- At high ordinate, vanishing of the multiplier log norm is equivalent to
the critical-line equation. -/
theorem pairedEtaLaplaceReflectionLogNorm_eq_zero_iff_re_eq_half_of_eight_le_abs
    {sigma y : ℝ} (hspos : 0 < sigma) (hslt : sigma < 1)
    (hy : 8 ≤ |y|) :
    pairedEtaLaplaceReflectionLogNorm sigma y = 0 ↔ sigma = 1 / 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy sigma (1 / 2) with hlt | heq | hgt
    · have hneg :=
        pairedEtaLaplaceReflectionLogNorm_neg_of_lt_half_of_eight_le_abs
          hspos hlt hy
      linarith
    · exact heq
    · have hpos :=
        pairedEtaLaplaceReflectionLogNorm_pos_of_half_lt_of_eight_le_abs
          hgt hslt hy
      linarith
  · rintro rfl
    exact pairedEtaLaplaceReflectionLogNorm_half y

/-- At absolute ordinate at least `8`, unit norm of the explicit reflection
multiplier is equivalent to the critical-line equation. -/
theorem norm_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half_of_eight_le_abs
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1)
    (hy : 8 ≤ |s.im|) :
    ‖pairedEtaLaplaceReflectionMultiplier s‖ = 1 ↔ s.re = 1 / 2 := by
  have hcoordinate : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s :=
    Complex.re_add_im s
  have hne : pairedEtaLaplaceReflectionMultiplier s ≠ 0 :=
    pairedEtaLaplaceReflectionMultiplier_ne_zero hspos hslt
  have hnormPos : 0 < ‖pairedEtaLaplaceReflectionMultiplier s‖ :=
    norm_pos_iff.mpr hne
  have hlogIff :=
    pairedEtaLaplaceReflectionLogNorm_eq_zero_iff_re_eq_half_of_eight_le_abs
      hspos hslt hy
  constructor
  · intro hnorm
    apply hlogIff.mp
    unfold pairedEtaLaplaceReflectionLogNorm
    rw [hcoordinate, hnorm, Real.log_one]
  · intro hre
    have hlogZero := hlogIff.mpr hre
    unfold pairedEtaLaplaceReflectionLogNorm at hlogZero
    rw [hcoordinate] at hlogZero
    exact Real.eq_one_of_pos_of_log_eq_zero hnormPos hlogZero

/-- Squared-norm form of high-ordinate horizontal rigidity. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half_of_eight_le_abs
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1)
    (hy : 8 ≤ |s.im|) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) = 1 ↔
      s.re = 1 / 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hnormNonneg : 0 ≤ ‖pairedEtaLaplaceReflectionMultiplier s‖ :=
    norm_nonneg _
  constructor
  · intro hsq
    apply (norm_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half_of_eight_le_abs
      hspos hslt hy).mp
    nlinarith
  · intro hre
    have hnorm :=
      (norm_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half_of_eight_le_abs
        hspos hslt hy).mpr hre
    rw [hnorm]
    norm_num

/-- For a nontrivial zero of absolute ordinate at least `8`, vanishing of the
actual first localized completion-distortion coefficient is equivalent to the
critical-line equation. This theorem does not assert that the coefficient
vanishes. -/
theorem pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_re_eq_half_of_eight_le_abs
    (rho : NontrivialZetaZero) (hy : 8 ≤ |rho.1.im|) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) = 0 ↔
      rho.1.re = 1 / 2 := by
  rw [pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_reflectionMultiplier_normSq_eq_one]
  exact normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_re_eq_half_of_eight_le_abs
    (NontrivialZetaZero.zero_lt_re rho)
    (NontrivialZetaZero.re_lt_one rho) hy

end
end RiemannGaussian
