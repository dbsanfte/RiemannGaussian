import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLaplaceHalfTurn
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The infinite positive Laplace measure underlying paired eta

Finite paired-eta roots were realized as zeros of finite positive Laplace
transforms. This module removes the truncation. It constructs one fixed
positive measure by restricting Lebesgue measure to the disjoint logarithmic
intervals

`(log (2n+1), log (2n+2)]`.

The complex exponential is proved genuinely integrable against this measure
throughout `Re s > 0`. Its integral is exactly the absolutely convergent sum
of the interval Laplace transforms, and multiplication by `s` recovers the
full paired eta core. Therefore every nontrivial zeta zero is an exact zero of
this single positive-measure Laplace transform. Its real and imaginary parts
give literal, absolutely convergent tilted cosine and sine cancellations.

This is an unconditional infinite arithmetic representation. It turns the
zero-location frontier into rigidity of one explicit positive measure; it
does not itself prove that rigidity.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The `n`th logarithmic interval carrying the positive paired-eta measure. -/
def pairedEtaLogInterval (n : ℕ) : Set ℝ :=
  Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2))

/-- The complete logarithmic support of the positive paired-eta measure. -/
def pairedEtaLogSupport : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval n

/-- Lebesgue measure restricted to the complete paired-eta logarithmic
support. -/
def pairedEtaLogMeasure : Measure ℝ :=
  volume.restrict pairedEtaLogSupport

/-- Distinct paired-eta logarithmic intervals are disjoint. -/
theorem pairwise_disjoint_pairedEtaLogInterval :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m)) := by
  suffices hordered : ∀ {n m : ℕ}, n < m →
      Disjoint (pairedEtaLogInterval n) (pairedEtaLogInterval m) by
    intro n m hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact hordered hnm
    · exact (hordered hmn).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro t htn htm
  have harg : (2 : ℝ) * n + 2 < 2 * m + 1 := by
    exact_mod_cast (show 2 * n + 2 < 2 * m + 1 by omega)
  have hlog : Real.log (2 * n + 2) < Real.log (2 * m + 1) :=
    Real.log_lt_log (by positivity) harg
  exact (not_lt_of_ge htn.2) (hlog.trans htm.1)

/-- The complete paired-eta logarithmic support is measurable. -/
theorem measurableSet_pairedEtaLogSupport :
    MeasurableSet pairedEtaLogSupport := by
  unfold pairedEtaLogSupport pairedEtaLogInterval
  exact MeasurableSet.iUnion fun _ ↦ measurableSet_Ioc

/-- The restricted measure is exactly the countable sum of the interval
restrictions. -/
theorem pairedEtaLogMeasure_eq_sum_restrict :
    pairedEtaLogMeasure =
      Measure.sum fun n : ℕ ↦ volume.restrict (pairedEtaLogInterval n) := by
  unfold pairedEtaLogMeasure pairedEtaLogSupport
  exact Measure.restrict_iUnion
    pairwise_disjoint_pairedEtaLogInterval
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

/-- The paired-eta logarithmic measure is dominated by Lebesgue measure. -/
theorem pairedEtaLogMeasure_le_volume :
    pairedEtaLogMeasure ≤ volume := by
  exact Measure.restrict_le_self

/-- The complete logarithmic support lies in positive time. -/
theorem pairedEtaLogSupport_subset_Ioi_zero :
    pairedEtaLogSupport ⊆ Ioi 0 := by
  intro t ht
  rw [pairedEtaLogSupport, mem_iUnion] at ht
  obtain ⟨n, hn⟩ := ht
  have hlogNonneg : 0 ≤ Real.log (2 * n + 1) := by
    apply Real.log_nonneg
    norm_num
  exact hlogNonneg.trans_lt hn.1

/-- The entire first interval `(0, log 2]` belongs to the logarithmic
support. -/
theorem Ioc_zero_log_two_subset_pairedEtaLogSupport :
    Ioc 0 (Real.log 2) ⊆ pairedEtaLogSupport := by
  intro t ht
  rw [pairedEtaLogSupport, mem_iUnion]
  refine ⟨0, ?_⟩
  simpa [pairedEtaLogInterval] using ht

/-- One logarithmic interval Laplace transform. -/
def pairedEtaLaplaceInterval (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
    Complex.exp (-s * t)

/-- The infinite positive-measure Laplace partition function underlying
paired eta. -/
def pairedEtaLaplacePartition (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaLaplaceInterval s n

/-- The logarithmic Laplace intervals are absolutely summable throughout the
positive half-plane. -/
theorem summable_pairedEtaLaplaceInterval
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaLaplaceInterval s) := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hsum := (summable_pairedEtaCoreSummand hs).div_const s
  apply hsum.congr
  intro n
  rw [pairedEtaCoreSummand_eq_mul_logLaplaceInterval]
  simp [pairedEtaLaplaceInterval, hs0]

/-- The positive real interval masses with exponential tilt are summable for
every positive tilt. -/
theorem summable_pairedEtaTiltedMassInterval
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ ↦
      ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
        Real.exp (-sigma * t)) := by
  have hcomplex : Summable (pairedEtaLaplaceInterval (sigma : ℂ)) :=
    summable_pairedEtaLaplaceInterval (by simpa using hsigma)
  have hre := Complex.reCLM.summable hcomplex
  apply hre.congr
  intro n
  simpa [pairedEtaLaplaceInterval] using
    (pairedEtaFiniteLaplaceInterval_re sigma 0 n)

/-- The complex Laplace kernel is genuinely integrable against the complete
paired-eta logarithmic measure throughout `Re s > 0`. -/
theorem integrable_exp_neg_mul_pairedEtaLogMeasure
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      pairedEtaLogMeasure := by
  rw [pairedEtaLogMeasure_eq_sum_restrict]
  apply integrable_sum_measure
  · intro n
    have hcont : Continuous (fun t : ℝ ↦ Complex.exp (-s * t)) := by
      fun_prop
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (hcont.intervalIntegrable _ _)
  · have hnorm := summable_pairedEtaTiltedMassInterval hs
    apply hnorm.congr
    intro n
    have hab : Real.log (2 * n + 1) ≤ Real.log (2 * n + 2) :=
      (pairedEtaFiniteLogInterval_pos n).le
    unfold pairedEtaLogInterval
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re]

/-- The integral against the complete positive logarithmic measure is exactly
the infinite interval Laplace partition. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) =
      pairedEtaLaplacePartition s := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure hs
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogMeasure_eq_sum_restrict,
    integral_sum_measure hint]
  unfold pairedEtaLaplacePartition pairedEtaLaplaceInterval
    pairedEtaLogInterval
  apply tsum_congr
  intro n
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos n).le).symm

/-- Multiplication by `s` recovers the full paired eta core from the infinite
positive Laplace partition. -/
theorem pairedEtaCore_eq_mul_laplacePartition
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s = s * pairedEtaLaplacePartition s := by
  unfold pairedEtaCore pairedEtaLaplacePartition
  calc
    ∑' n : ℕ, pairedEtaCoreSummand s n =
        ∑' n : ℕ, s * pairedEtaLaplaceInterval s n := by
      apply tsum_congr
      intro n
      exact pairedEtaCoreSummand_eq_mul_logLaplaceInterval s n
    _ = s * ∑' n : ℕ, pairedEtaLaplaceInterval s n :=
      (summable_pairedEtaLaplaceInterval hs).tsum_mul_left s

/-- The literal positive-measure integral recovers paired eta after
multiplication by `s`. -/
theorem pairedEtaCore_eq_mul_integral_exp_neg_mul_pairedEtaLogMeasure
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s =
      s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure := by
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hs]
  exact pairedEtaCore_eq_mul_laplacePartition hs

/-- The infinite positive-measure Laplace transform is paired eta divided by
its spectral parameter. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div
    {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) =
      pairedEtaCore s / s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  apply (eq_div_iff hs0).2
  rw [pairedEtaCore_eq_mul_integral_exp_neg_mul_pairedEtaLogMeasure hs]
  ring

/-- Away from the zeta pole, the fixed positive-measure Laplace transform is
the literal eta factor times zeta, divided by `s`. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_factor_riemannZeta_div
    {s : ℂ} (hs : 0 < s.re) (hsone : s ≠ 1) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) =
      ((1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) / s := by
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div hs,
    pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hsone]

/-- The complete exponentially tilted cosine moment of the positive
paired-eta logarithmic measure. -/
def pairedEtaTiltedCosineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.cos (y * t)
    ∂pairedEtaLogMeasure

/-- The complete exponentially tilted sine moment of the positive paired-eta
logarithmic measure. -/
def pairedEtaTiltedSineMoment (sigma y : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (-sigma * t) * Real.sin (y * t)
    ∂pairedEtaLogMeasure

/-- The complete tilted cosine kernel is genuinely integrable for every
positive tilt. -/
theorem integrable_pairedEtaTiltedCosineKernel
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ ↦
      Real.exp (-sigma * t) * Real.cos (y * t))
      pairedEtaLogMeasure := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  apply hint.re.congr
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

/-- The complete tilted sine kernel is genuinely integrable for every
positive tilt. -/
theorem integrable_pairedEtaTiltedSineKernel
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    Integrable (fun t : ℝ ↦
      Real.exp (-sigma * t) * Real.sin (y * t))
      pairedEtaLogMeasure := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have hnegative : Integrable (fun t : ℝ ↦
      -(Real.exp (-sigma * t) * Real.sin (y * t)))
      pairedEtaLogMeasure := by
    apply hint.im.congr
    filter_upwards with t
    exact pairedEtaFiniteLaplaceKernel_im sigma y t
  convert hnegative.neg using 1
  ext t
  simp

/-- The total exponentially tilted mass of the complete positive eta measure
is strictly positive. -/
theorem pairedEtaTiltedCosineMoment_zero_pos
    (sigma : ℝ) (hsigma : 0 < sigma) :
    0 < pairedEtaTiltedCosineMoment sigma 0 := by
  have hint := integrable_pairedEtaTiltedCosineKernel sigma 0 hsigma
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hint
  simp only [zero_mul, Real.cos_zero, mul_one] at hint
  unfold pairedEtaTiltedCosineMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [pairedEtaLogMeasure_eq_sum_restrict, integral_sum_measure hint]
  have hsum := summable_pairedEtaTiltedMassInterval hsigma
  calc
    0 < ∑' n : ℕ,
        ∫ t : ℝ in Real.log (2 * n + 1)..Real.log (2 * n + 2),
          Real.exp (-sigma * t) := by
      apply hsum.tsum_pos
      · intro n
        exact (intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos n)).le
      · exact intervalIntegral.intervalIntegral_pos_of_pos
          (by
            apply Continuous.intervalIntegrable
            fun_prop)
          (fun _ ↦ Real.exp_pos _)
          (pairedEtaFiniteLogInterval_pos 0)
    _ = ∑' n : ℕ,
        ∫ t : ℝ, Real.exp (-sigma * t)
          ∂volume.restrict (pairedEtaLogInterval n) := by
      apply tsum_congr
      intro n
      unfold pairedEtaLogInterval
      exact (intervalIntegral.integral_of_le
        (pairedEtaFiniteLogInterval_pos n).le)

/-- The real part of the infinite positive Laplace integral is its complete
tilted cosine moment. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_re
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).re =
      pairedEtaTiltedCosineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have hre :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).re
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).re := by
    simpa using integral_re hint
  rw [← hre]
  unfold pairedEtaTiltedCosineMoment
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_re sigma y t

/-- The imaginary part of the infinite positive Laplace integral is the
negative of its complete tilted sine moment. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_im
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    (∫ t : ℝ,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
        ∂pairedEtaLogMeasure).im =
      -pairedEtaTiltedSineMoment sigma y := by
  have hint := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)
  have him :
      (∫ t : ℝ,
        (Complex.exp
          (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)).im
          ∂pairedEtaLogMeasure) =
        (∫ t : ℝ,
          Complex.exp
            (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)
            ∂pairedEtaLogMeasure).im := by
    simpa using integral_im hint
  rw [← him]
  unfold pairedEtaTiltedSineMoment
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with t
  exact pairedEtaFiniteLaplaceKernel_im sigma y t

/-- The infinite positive Laplace partition splits exactly into its complete
tilted cosine and sine moments. -/
theorem pairedEtaLaplacePartition_eq_cosine_sub_I_sine
    (sigma y : ℝ) (hsigma : 0 < sigma) :
    pairedEtaLaplacePartition
        ((sigma : ℂ) + (y : ℂ) * Complex.I) =
      (pairedEtaTiltedCosineMoment sigma y : ℂ) -
        (pairedEtaTiltedSineMoment sigma y : ℂ) * Complex.I := by
  rw [← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    (s := (sigma : ℂ) + (y : ℂ) * Complex.I) (by
      norm_num
      exact hsigma)]
  apply Complex.ext
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_re sigma y hsigma]
    norm_num [Complex.mul_re]
  · rw [integral_exp_neg_mul_pairedEtaLogMeasure_im sigma y hsigma]
    norm_num [Complex.mul_im]

/-- Every nontrivial zeta zero is an exact zero of the one fixed infinite
positive-measure eta Laplace partition. -/
theorem pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaLaplacePartition rho.1 = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      hre rho.2.2.2, rho.2.1, mul_zero]
  have hmul : rho.1 * pairedEtaLaplacePartition rho.1 = 0 := by
    rw [← pairedEtaCore_eq_mul_laplacePartition hre, hcore]
  exact (mul_eq_zero.mp hmul).resolve_left (by
    intro hrho
    have := congrArg Complex.re hrho
    norm_num at this
    linarith)

/-- Every nontrivial zeta zero makes the literal infinite positive-measure
Laplace integral vanish exactly. -/
theorem integral_exp_neg_mul_pairedEtaLogMeasure_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    (∫ t : ℝ, Complex.exp (-rho.1 * t) ∂pairedEtaLogMeasure) = 0 := by
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition
    (NontrivialZetaZero.zero_lt_re rho),
    pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero]

/-- At every nontrivial zeta zero, both complete tilted Fourier moments of
the fixed positive paired-eta logarithmic measure vanish exactly. -/
theorem pairedEtaTiltedMoments_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaTiltedCosineMoment rho.1.re rho.1.im = 0 ∧
      pairedEtaTiltedSineMoment rho.1.re rho.1.im = 0 := by
  have hre : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hzeroCoordinates :
      pairedEtaLaplacePartition
        (((rho.1.re : ℝ) : ℂ) + ((rho.1.im : ℝ) : ℂ) * Complex.I) = 0 := by
    simpa only [Complex.re_add_im] using
      pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho
  have hsplit :=
    pairedEtaLaplacePartition_eq_cosine_sub_I_sine
      rho.1.re rho.1.im hre
  rw [hzeroCoordinates] at hsplit
  constructor
  · have hreal := congrArg Complex.re hsplit
    norm_num [Complex.mul_re] at hreal
    exact hreal.symm
  · have himag := congrArg Complex.im hsplit
    norm_num [Complex.mul_im] at himag
    exact himag

end

end RiemannGaussian
