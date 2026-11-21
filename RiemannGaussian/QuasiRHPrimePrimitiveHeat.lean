import RiemannGaussian.RosserSchoenfeldExplicitFormula
import Mathlib.LinearAlgebra.Lagrange
import RiemannGaussian.SuzukiLocalCancellationScaleAverage

/-! # Gaussian averages of the finite von Mangoldt primitive

Modulating the normalized prime discrepancy tests any real frequency. The error
from the trivial zeros and the endpoint is uniform in that frequency.
-/

namespace RiemannGaussian.QuasiRHPrimePrimitiveHeat
noncomputable section
open MeasureTheory ProbabilityTheory

/-- The normalized discrepancy of the finite prime-power sum, extended by zero
to negative logarithmic time. -/
def discrepancy (t : ℝ) : ℂ :=
  if 0 ≤ t then (Real.exp (-(1/2 : ℝ)*t) : ℂ) *
    (RosserSchoenfeldExplicitFormula.mainTerm t - RosserSchoenfeldPrimePrimitive.value t)
  else 0

/-- The residue of the twice-integrated prime-power sum at a nontrivial zero. -/
def coefficient (ρ : NontrivialZetaZero) : ℂ :=
  (analyticZetaZeroMultiplicity ρ : ℂ) / ρ.1^2

private theorem summable_coeff : Summable (fun ρ => ‖coefficient ρ‖) := by
  simpa only [coefficient, norm_div, norm_pow, Complex.norm_natCast] using
    RosserSchoenfeldZeroMass.norm_square_mass_summable

private theorem mass_lt : (∑' ρ, ‖coefficient ρ‖) < 463/10000 := by
  simpa only [coefficient, norm_div, norm_pow, Complex.norm_natCast] using
    RosserSchoenfeldZeroMass.norm_square_mass_lt

/-- The exponential mode after centering on the critical line and translating
the Fourier frequency by a real ordinate. -/
def rate (ρ : NontrivialZetaZero) (y : ℝ) : ℂ := ρ.1-1/2-(y:ℂ)*Complex.I

private theorem rate_re (ρ : NontrivialZetaZero) (y : ℝ) :
    (rate ρ y).re = ρ.1.re-1/2 := by simp [rate]

private theorem mode_norm (ρ : NontrivialZetaZero) (y t : ℝ) :
    ‖coefficient ρ * Complex.exp (rate ρ y * t)‖ =
      ‖coefficient ρ‖ * Real.exp ((ρ.1.re-1/2)*t) := by
  simp [Complex.norm_exp, Complex.mul_re, rate_re]

private theorem mode_bound (ρ : NontrivialZetaZero) (y t : ℝ) :
    ‖coefficient ρ * Complex.exp (rate ρ y * t)‖ ≤
      ‖coefficient ρ‖ * (Real.exp (1*t) + Real.exp ((-1)*t)) := by
  rw [mode_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rcases le_total 0 t with ht | ht
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [ρ.re_lt_one]) ht)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith [ρ.zero_lt_re]) ht)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- The full absolutely convergent modulated zero series before averaging. -/
def modes (y t : ℝ) : ℂ := ∑' ρ, coefficient ρ * Complex.exp (rate ρ y * t)

private theorem summable_modes (y t : ℝ) :
    Summable (fun ρ => ‖coefficient ρ * Complex.exp (rate ρ y * t)‖) :=
  (summable_coeff.mul_right _).of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => mode_bound ρ y t)

private theorem centered_mode (ρ : NontrivialZetaZero) (t : ℝ) :
    coefficient ρ * Complex.exp (rate ρ 0 * t) =
      (Real.exp (-(1/2 : ℝ)*t) : ℂ) *
      (RosserSchoenfeldZeroPrimitive.term ρ t + coefficient ρ) := by
  have he : Complex.exp (rate ρ 0 * t) =
      (Real.exp (-(1/2 : ℝ)*t) : ℂ) * Complex.exp (ρ.1*t) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp [rate]
    ring
  rw [he]
  unfold coefficient RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
  ring

private theorem modes_zero_eq {t : ℝ} (ht : 0 ≤ t) :
    modes 0 t = (Real.exp (-(1/2 : ℝ)*t) : ℂ) *
      (RosserSchoenfeldZeroPrimitive.value t + ∑' ρ, coefficient ρ) := by
  unfold modes
  simp_rw [centered_mode]
  rw [tsum_mul_left, (RosserSchoenfeldZeroPrimitive.summable_term ht).tsum_add summable_coeff.of_norm]
  rfl

/-- Beyond time one the elementary corrections have a definite sign.
The first trivial zero alone dominates the complete constant from the
nontrivial zero primitive. -/
theorem discrepancy_re_le_modes {u : ℝ} (hu : 1 ≤ u) : (discrepancy u).re ≤ (modes 0 u).re := by
  have hu0 : 0 ≤ u := by linarith
  have ht (n : ℕ) : 0 ≤ (RosserSchoenfeldTrivialPrimitive.term n u).re := by
    change 0 ≤ (1-Real.exp (-2*((n:ℝ)+1)*u))/(4*((n:ℝ)+1)^2)
    apply div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr _)) (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hu0]
  have hs := (RosserSchoenfeldTrivialPrimitive.summable_norm_term hu0).of_norm
  have hfirst : (RosserSchoenfeldTrivialPrimitive.term 0 u).re ≤
      (RosserSchoenfeldTrivialPrimitive.value u).re := by
    rw [RosserSchoenfeldTrivialPrimitive.value, Complex.re_tsum hs]
    exact (Complex.reCLM.summable hs).le_tsum 0 (fun n _ => ht n)
  have he : Real.exp (-(2*u)) ≤ 1/2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (2*u)])
  have htr : 1/8 ≤ (RosserSchoenfeldTrivialPrimitive.value u).re := by
    simp only [RosserSchoenfeldTrivialPrimitive.term, Complex.ofReal_re, Nat.cast_zero, zero_add,
      mul_one, one_pow, neg_mul] at hfirst
    linarith
  have hsre := Complex.abs_re_le_norm (∑' ρ, coefficient ρ)
  have hco := (norm_tsum_le_tsum_norm summable_coeff).trans_lt mass_lt
  have hh : 0 ≤ (RosserSchoenfeldTrivialPrimitive.value u + ∑' ρ, coefficient ρ).re := by
    rw [Complex.add_re]
    linarith [neg_abs_le (∑' ρ, coefficient ρ).re]
  rw [modes_zero_eq hu0]
  simp only [discrepancy, hu0, ↓reduceIte, RosserSchoenfeldExplicitFormula.prime_eq_spectral hu0,
    RosserSchoenfeldExplicitFormula.spectral, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.ofReal_re, Complex.sub_re, Complex.add_re] at hh ⊢
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith

/-- A pointwise error estimate for the actual finite-prime discrepancy, valid
on both sides of the endpoint at time zero. -/
theorem norm_discrepancy_sub_modes (t : ℝ) :
    ‖discrepancy t - modes 0 t‖ ≤ Real.exp (-(1/2 : ℝ)*t) := by
  by_cases ht : 0 ≤ t
  · simp only [discrepancy, ht, ↓reduceIte]
    rw [modes_zero_eq ht,
      RosserSchoenfeldExplicitFormula.prime_eq_spectral ht]
    unfold RosserSchoenfeldExplicitFormula.spectral
    rw [← mul_sub]
    rw [show RosserSchoenfeldExplicitFormula.mainTerm t -
        (RosserSchoenfeldExplicitFormula.mainTerm t - RosserSchoenfeldZeroPrimitive.value t +
        RosserSchoenfeldTrivialPrimitive.value t) -
        (RosserSchoenfeldZeroPrimitive.value t + ∑' ρ, coefficient ρ) =
        -(RosserSchoenfeldTrivialPrimitive.value t + ∑' ρ, coefficient ρ) by ring]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_of_le_one_right (Real.exp_pos _).le
    apply (norm_add_le ..).trans
    have hh := (norm_tsum_le_tsum_norm summable_coeff).trans_lt mass_lt
    nlinarith [RosserSchoenfeldTrivialPrimitive.norm_value_le ht, Real.pi_lt_four, Real.pi_pos]
  · simp only [discrepancy, ht, ↓reduceIte, zero_sub, norm_neg]
    have h (ρ : NontrivialZetaZero) : ‖coefficient ρ * Complex.exp (rate ρ 0 * t)‖ ≤
        ‖coefficient ρ‖ * Real.exp (-(1/2 : ℝ)*t) := by
      rw [mode_norm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith [ρ.zero_lt_re]) (le_of_not_ge ht))
    apply ((norm_tsum_le_tsum_norm (summable_modes 0 t)).trans
      ((summable_modes 0 t).tsum_le_tsum h (summable_coeff.mul_right _))).trans
    rw [tsum_mul_right]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (by linarith [mass_lt])


private def twist (y t : ℝ) : ℂ := Complex.exp (-((y:ℂ)*Complex.I)*t)

private theorem norm_twist (y t : ℝ) : ‖twist y t‖ = 1 := by
  simp [twist, Complex.norm_exp, Complex.mul_re]

private theorem twist_modes (y t : ℝ) : twist y t * modes 0 t = modes y t := by
  unfold modes
  rw [← tsum_mul_left]
  apply tsum_congr
  intro ρ
  rw [mul_left_comm, twist, ← Complex.exp_add]
  congr 2
  simp [rate]
  ring

private theorem measurable_modes (y : ℝ) : Measurable (modes y) := by
  apply Measurable.tsum
  intro ρ
  fun_prop

private theorem measurable_discrepancy : Measurable discrepancy := by
  unfold discrepancy
  apply Measurable.ite measurableSet_Ici
  · have hc := RosserSchoenfeldPrimePrimitive.continuous_value
    unfold RosserSchoenfeldExplicitFormula.mainTerm
    fun_prop
  · exact measurable_const

/-- The absolutely convergent zero series is integrable for each Gaussian time and frequency. -/
theorem integrable_modes (T : ℝ) (v : NNReal) (y : ℝ) :
    Integrable (modes y) (gaussianReal T v) := by
  have hg := ((integrable_exp_mul_gaussianReal (μ := T) (v := v) 1).add
    (integrable_exp_mul_gaussianReal (-1))).const_mul (∑' ρ, ‖coefficient ρ‖)
  apply hg.mono' (measurable_modes y).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  apply ((norm_tsum_le_tsum_norm (summable_modes y u)).trans
    ((summable_modes y u).tsum_le_tsum (fun ρ => mode_bound ρ y u) (summable_coeff.mul_right _))).trans_eq
  exact tsum_mul_right

/-- The Fourier coefficient of the actual normalized prime discrepancy under a
Gaussian of mean T and variance v. -/
def primeAverage (T : ℝ) (v : NNReal) (y : ℝ) : ℂ :=
  ∫ u : ℝ, twist y u * discrepancy u ∂gaussianReal T v

private theorem integral_modes (T : ℝ) (v : NNReal) (y : ℝ) :
    (∫ u, modes y u ∂gaussianReal T v) =
      ∑' ρ, coefficient ρ * Complex.exp (rate ρ y * T + (v:ℂ) * rate ρ y ^ 2 / 2) := by
  let μ := gaussianReal T v
  let g (u : ℝ) := Real.exp (1*u) + Real.exp ((-1)*u)
  let F (ρ : NontrivialZetaZero) (u : ℝ) := coefficient ρ * Complex.exp (rate ρ y*u)
  have hg : Integrable g μ := (integrable_exp_mul_gaussianReal 1).add
    (integrable_exp_mul_gaussianReal (-1))
  have hi (ρ : NontrivialZetaZero) : Integrable (F ρ) μ :=
    (hg.const_mul ‖coefficient ρ‖).mono' (by dsimp [F]; fun_prop)
      (Filter.Eventually.of_forall (fun u => mode_bound ρ y u))
  have hs : Summable (fun ρ => ∫ u, ‖F ρ u‖ ∂μ) := by
    apply (summable_coeff.mul_right (∫ u, g u ∂μ)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    intro ρ
    rw [← integral_const_mul]
    exact integral_mono (hi ρ).norm (hg.const_mul _) (fun u => mode_bound ρ y u)
  rw [show (∫ u, modes y u ∂gaussianReal T v) = ∑' ρ, ∫ u, F ρ u ∂μ from
    (integral_tsum_of_summable_integral_norm hi hs).symm]
  apply tsum_congr
  intro ρ
  rw [show (∫ u, F ρ u ∂μ) = coefficient ρ * (∫ u : ℝ, Complex.exp (rate ρ y*u) ∂μ)
    from integral_const_mul ..]
  exact congrArg (coefficient ρ * ·) (complexMGF_id_gaussianReal (μ := T) (v := v) (rate ρ y))

/-- Frequency-uniform comparison of the actual arithmetic average with the
complete Gaussian zero sum. The variance may be chosen separately at every time. -/
theorem norm_primeAverage_sub_zero_sum (T : ℝ) (v : NNReal) (y : ℝ) :
    ‖primeAverage T v y -
      ∑' ρ, coefficient ρ * Complex.exp (rate ρ y * T + (v:ℂ) * rate ρ y ^ 2 / 2)‖ ≤
      Real.exp (-T/2+(v:ℝ)/8) := by
  let μ := gaussianReal T v
  let D (u : ℝ) := twist y u * discrepancy u - modes y u
  have hd (u : ℝ) : ‖D u‖ ≤ Real.exp (-(1/2 : ℝ)*u) := by
    dsimp only [D]
    rw [← twist_modes y u, ← mul_sub, norm_mul, norm_twist, one_mul]
    exact norm_discrepancy_sub_modes u
  have hg := integrable_exp_mul_gaussianReal (μ := T) (v := v) (-(1/2 : ℝ))
  have hi : Integrable D μ := by
    apply hg.mono' _ (Filter.Eventually.of_forall hd)
    exact (((show Measurable (twist y) by unfold twist; fun_prop).mul
      measurable_discrepancy).sub (measurable_modes y)).aestronglyMeasurable
  have h := integral_add hi (integrable_modes T v y)
  have he : primeAverage T v y - (∫ u, modes y u ∂μ) = ∫ u, D u ∂μ := by
    rw [eq_comm, eq_sub_iff_add_eq, ← h]
    unfold primeAverage
    apply integral_congr_ae
    filter_upwards with u
    simp [D]
  rw [← integral_modes, he]
  apply (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hd)).trans_eq
  change mgf id (gaussianReal T v) (-(1/2 : ℝ)) = _
  rw [mgf_id_gaussianReal]
  change Real.exp (T * (-(1/2 : ℝ)) + (v:ℝ) * (-(1/2 : ℝ))^2/2) = _
  exact congrArg Real.exp (by ring)

open Filter Topology

/-- With variance twice elapsed time, each mode has a single complex
exponential rate in the time variable. -/
def heatRate (ρ : NontrivialZetaZero) (y : ℝ) : ℂ := rate ρ y + rate ρ y ^ 2

private theorem heatRate_re (ρ : NontrivialZetaZero) (y : ℝ) :
    (heatRate ρ y).re = (ρ.1.re-1/2) + (ρ.1.re-1/2)^2 - (ρ.1.im-y)^2 := by
  have hi : (rate ρ y).im = ρ.1.im-y := by simp [rate]
  simp only [heatRate, pow_two, Complex.add_re, Complex.mul_re, rate_re, hi]
  ring

/-- The quadratic time rates distinguish every pair of actual zeros at every
real test frequency. Both preimages of a rate cannot lie in the open strip. -/
theorem heatRate_injective (y : ℝ) : Function.Injective (fun ρ => heatRate ρ y) := by
  intro ρ σ he
  have hf : (rate ρ y-rate σ y)*(1+rate ρ y+rate σ y) = 0 := by
    unfold heatRate at he
    linear_combination he
  rcases mul_eq_zero.mp hf with hh | hh
  · apply Subtype.ext
    unfold rate at hh
    linear_combination hh
  · have hr := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.one_re, rate_re, Complex.zero_re] at hr
    linarith [ρ.zero_lt_re, σ.zero_lt_re]

/-- The time-scaled arithmetic Fourier coefficient. -/
def response (T y : ℝ) : ℂ := primeAverage T (2*T).toNNReal y

private def series (T y : ℝ) : ℂ := ∑' ρ, coefficient ρ * Complex.exp (heatRate ρ y * T)

private theorem norm_response_sub_series {T : ℝ} (hT : 0 ≤ T) (y : ℝ) :
    ‖response T y - series T y‖ ≤ Real.exp (-(1/4 : ℝ)*T) := by
  have hv : (((2*T).toNNReal : NNReal) : ℝ) = 2*T := Real.coe_toNNReal _ (by positivity)
  have h := norm_primeAverage_sub_zero_sum T (2*T).toNNReal y
  have he (ρ : NontrivialZetaZero) : rate ρ y * (T:ℂ) +
      (((2*T).toNNReal : NNReal) : ℂ) * rate ρ y ^ 2 / 2 = heatRate ρ y * T := by
    rw [hv]
    push_cast
    unfold heatRate
    ring
  simp_rw [he] at h
  simpa only [response, series, hv, show -T/2+2*T/8 = -(1/4 : ℝ)*T by ring] using h

private theorem heatRate_re_neg {ρ : NontrivialZetaZero} {y : ℝ}
    (hlocal : |ρ.1.im-y| < 1 → ρ.1.re = 1/2) (hne : rate ρ y ≠ 0) :
    (heatRate ρ y).re < 0 := by
  rw [heatRate_re]
  by_cases hh : |ρ.1.im-y| < 1
  · rw [hlocal hh, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, zero_sub]
    apply neg_lt_zero.mpr
    apply sq_pos_of_ne_zero
    intro him
    apply hne
    apply Complex.ext
    · rw [rate_re, hlocal hh, sub_self, Complex.zero_re]
    · simpa [rate] using him
  · have hi : 1 ≤ (ρ.1.im-y)^2 := by
      simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1)
        (le_of_not_gt hh) 2
    nlinarith [ρ.re_lt_one, ρ.zero_lt_re,
      mul_nonneg ρ.zero_lt_re.le (sub_nonneg.mpr ρ.re_lt_one.le)]

private theorem exp_decay {a : ℝ} (ha : a < 0) :
    Tendsto (fun T : ℝ => Real.exp (a*T)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg ha)

/-- If every zero within one unit of y lies on the critical line, the observed
prime average converges to the residue at 1/2 + i y, with value zero when
there is no such zero. -/
theorem tendsto_response_of_local_critical {y : ℝ}
    (hlocal : ∀ ρ : NontrivialZetaZero, |ρ.1.im-y| < 1 → ρ.1.re = 1/2) :
    Tendsto (fun T => response T y) atTop
      (𝓝 (∑' ρ, if rate ρ y = 0 then coefficient ρ else 0)) := by
  have hn (ρ : NontrivialZetaZero) (T : ℝ) :
      ‖coefficient ρ * Complex.exp (heatRate ρ y * T)‖ =
        ‖coefficient ρ‖ * Real.exp ((heatRate ρ y).re*T) := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hp (ρ : NontrivialZetaZero) :
      Tendsto (fun T : ℝ => coefficient ρ * Complex.exp (heatRate ρ y * T)) atTop
        (𝓝 (if rate ρ y = 0 then coefficient ρ else 0)) := by
    by_cases he : rate ρ y = 0
    · simp [heatRate, he]
    · simp only [he, ↓reduceIte]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [hn, mul_zero] using
        (exp_decay (heatRate_re_neg (hlocal ρ) he)).const_mul ‖coefficient ρ‖
  have hs : Tendsto (fun T => series T y) atTop _ :=
    tendsto_tsum_of_dominated_convergence summable_coeff hp (by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT ρ
      by_cases he : rate ρ y = 0
      · simp [heatRate, he]
      · rw [hn]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (heatRate_re_neg (hlocal ρ) he).le hT)))
  have herror : Tendsto (fun T => response T y - series T y) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (exp_decay (by norm_num : -(1/4 : ℝ) < 0))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT using norm_response_sub_series hT y
  simpa only [sub_add_cancel, zero_add] using herror.add hs

/-- The certified critical-line computation through height 54 verifies the
arithmetic limit simultaneously for all real test ordinates up to 53 in absolute value. -/
theorem tendsto_response_through_fiftyThree {y : ℝ} (hy : |y| ≤ 53) :
    Tendsto (fun T => response T y) atTop
      (𝓝 (∑' ρ, if rate ρ y = 0 then coefficient ρ else 0)) := by
  apply tendsto_response_of_local_critical
  intro ρ hρ
  apply ZetaElevenZeroCompleteness.critical_line_through_fiftyFour
  calc
    |ρ.1.im| = |(ρ.1.im-y)+y| := by rw [sub_add_cancel]
    _ ≤ |ρ.1.im-y|+|y| := abs_add_le ..
    _ ≤ 54 := by linarith

private theorem exists_distinct_shift {w z : ℂ} (hne : w ≠ z) :
    ∃ h : ℝ, 0 < h ∧ Complex.exp (w*h) ≠ Complex.exp (z*h) := by
  let D := 1+|w.im|+|z.im|
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro he
  have hb (a : ℂ) (ha : |a.im| ≤ D) :
      -Real.pi < (a*(D⁻¹:ℝ)).im ∧ (a*(D⁻¹:ℝ)).im ≤ Real.pi := by
    have hh : |a.im * D⁻¹| ≤ 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hD), ← div_eq_mul_inv, div_le_one hD]
      exact ha
    simp only [Complex.mul_im, Complex.ofReal_im, mul_zero, Complex.ofReal_re, zero_add]
    constructor <;> linarith [(abs_le.mp hh).1, (abs_le.mp hh).2, Real.pi_gt_three]
  have hw := hb w (by dsimp [D]; linarith [abs_nonneg z.im])
  have hz := hb z (by dsimp [D]; linarith [abs_nonneg w.im])
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi hw.1 hw.2 hz.1 hz.2 he
  exact hne (mul_right_cancel₀ (by exact_mod_cast (inv_pos.mpr hD).ne') heq)

private theorem bounded_finite_modes {ι : Type*} (S : Finset ι) (w : ι → ℂ) (z : ℂ)
    (hdist : ∀ j ∈ S, w j ≠ z) (a : ι → ℂ) (b : ℂ) (hb : b ≠ 0)
    (hbound : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      ‖b*Complex.exp (z*T) + ∑ j ∈ S, a j*Complex.exp (w j*T)‖ ≤ C) :
    z.re ≤ 0 := by
  classical
  induction S using Finset.induction_on generalizing a b with
  | empty =>
    obtain ⟨C, hC⟩ := hbound
    by_contra! hz
    have ht := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hz)).const_mul_atTop
      (norm_pos_iff.mpr hb)
    have hn := (hC.and (ht.eventually_gt_atTop C)).exists
    obtain ⟨T, hT, hl⟩ := hn
    simp [Complex.norm_exp, Complex.mul_re] at hT
    exact (not_lt_of_ge hT) hl
  | insert j S hj ih =>
    obtain ⟨h, _, hh⟩ := exists_distinct_shift (Ne.symm (hdist j (Finset.mem_insert_self ..)))
    let E (v : ℂ) := Complex.exp (v*h)
    let F (T : ℝ) := b*Complex.exp (z*T) +
      ∑ k ∈ insert j S, a k*Complex.exp (w k*T)
    obtain ⟨C, hC⟩ := hbound
    change ∀ᶠ T : ℝ in atTop, ‖F T‖ ≤ C at hC
    have hc : ∀ᶠ T : ℝ in atTop, ‖F (T+h)‖ ≤ C :=
      (tendsto_atTop_add_const_right atTop h tendsto_id).eventually hC
    apply ih (fun k hk => hdist k (Finset.mem_insert_of_mem hk))
      (fun k => a k*(E (w k)-E (w j))) (b*(E z-E (w j))) (mul_ne_zero hb (sub_ne_zero.mpr hh))
    refine ⟨C+‖E (w j)‖*C, ?_⟩
    filter_upwards [hC, hc] with T hT hTh
    change ‖F (T+h)‖ ≤ C at hTh
    have he (v : ℂ) : Complex.exp (v*((T+h:ℝ):ℂ)) = E v * Complex.exp (v*T) := by
      rw [Complex.ofReal_add, mul_add, Complex.exp_add, mul_comm]
    have hfilter : F (T+h) - E (w j)*F T =
        b*(E z-E (w j))*Complex.exp (z*T) +
        ∑ k ∈ S, a k*(E (w k)-E (w j))*Complex.exp (w k*T) := by
      unfold F
      simp_rw [he]
      rw [Finset.sum_insert hj, Finset.sum_insert hj, mul_add, mul_add, Finset.mul_sum]
      rw [show (∑ k ∈ S, a k*(E (w k)-E (w j))*Complex.exp (w k*T)) =
          (∑ k ∈ S, a k*(E (w k)*Complex.exp (w k*T))) -
          ∑ k ∈ S, E (w j)*(a k*Complex.exp (w k*T)) by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring]
      ring
    rw [← hfilter]
    exact (norm_sub_le ..).trans (add_le_add hTh (by rw [norm_mul]; gcongr))

private theorem norm_series_sub_window {T : ℝ} (hT : 0 ≤ T) (y : ℝ) {R : ℝ} (hR : |y|+1 ≤ R) :
    ‖series T y - ∑ ρ ∈ spectralZetaZeroWindow R,
      coefficient ρ * Complex.exp (heatRate ρ y*T)‖ ≤ ∑' ρ, ‖coefficient ρ‖ := by
  classical
  let S := spectralZetaZeroWindow R
  let f (ρ : NontrivialZetaZero) := coefficient ρ * Complex.exp (heatRate ρ y*T)
  have hn (ρ : NontrivialZetaZero) : ‖f ρ‖ =
      ‖coefficient ρ‖ * Real.exp ((heatRate ρ y).re*T) := by
    simp [f, Complex.norm_exp, Complex.mul_re]
  have hs : Summable (fun ρ => ‖f ρ‖) := by
    apply (summable_coeff.mul_right (Real.exp (1*T))).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro ρ
    rw [hn]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hT
    rw [heatRate_re]
    nlinarith [ρ.zero_lt_re, ρ.re_lt_one, sq_nonneg (ρ.1.im-y),
      mul_nonneg ρ.zero_lt_re.le (sub_nonneg.mpr ρ.re_lt_one.le)]
  have htail (ρ : ↥(S : Set NontrivialZetaZero)ᶜ) : ‖f ρ‖ ≤ ‖coefficient ρ‖ := by
    rw [hn]
    apply mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr _)
    apply mul_nonpos_of_nonpos_of_nonneg _ hT
    have hfar : ¬ |ρ.1.1.im-y| < 1 := by
      intro h
      apply ρ.2
      apply (mem_spectralZetaZeroWindow (by linarith [abs_nonneg y] : 0 ≤ R) _).mpr
      rw [zetaSpectralCoordinate_re]
      calc
        |ρ.1.1.im| = |(ρ.1.1.im-y)+y| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add_le ..
        _ ≤ _ := by linarith
    by_cases hr : rate ρ.1 y = 0
    · simp [heatRate, hr]
    · exact (heatRate_re_neg (fun h => (hfar h).elim) hr).le
  have hsplit := hs.of_norm.sum_add_tsum_compl (s := S)
  change ‖(∑' ρ, f ρ) - ∑ ρ ∈ S, f ρ‖ ≤ _
  rw [← hsplit, add_sub_cancel_left]
  apply ((norm_tsum_le_tsum_norm (hs.subtype _)).trans
    ((hs.subtype _).tsum_le_tsum htail (summable_coeff.subtype _))).trans
  exact Summable.tsum_subtype_le (fun ρ => ‖coefficient ρ‖) _ (fun _ => norm_nonneg _) summable_coeff

/-- A bound for one observed Fourier coefficient rules out any zero on its
ordinate strictly to the right of the critical line. -/
theorem re_le_half_of_bounded_response (ρ : NontrivialZetaZero)
    (h : ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ‖response T ρ.1.im‖ ≤ C) : ρ.1.re ≤ 1/2 := by
  classical
  let y := ρ.1.im
  let S := spectralZetaZeroWindow (|y|+1)
  have hρ : ρ ∈ S := by
    dsimp only [S]
    rw [mem_spectralZetaZeroWindow (by positivity), zetaSpectralCoordinate_re]
    dsimp only [y]
    linarith
  have hnon : coefficient ρ ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (analyticZetaZeroMultiplicity_positive ρ).ne'
    · exact pow_ne_zero _ (Complex.ne_zero_of_re_pos ρ.zero_lt_re)
  have hdist (σ) (hσ : σ ∈ S.erase ρ) : heatRate σ y ≠ heatRate ρ y :=
    fun he => (Finset.mem_erase.mp hσ).1 (heatRate_injective y he)
  have hz := bounded_finite_modes (S.erase ρ) (fun σ => heatRate σ y) (heatRate ρ y)
    hdist coefficient (coefficient ρ) hnon (by
      obtain ⟨C, hC⟩ := h
      refine ⟨C + 1 + ∑' σ, ‖coefficient σ‖, ?_⟩
      filter_upwards [hC, eventually_ge_atTop (0:ℝ)] with T hT ht
      rw [Finset.add_sum_erase S (fun σ => coefficient σ * Complex.exp (heatRate σ y*T)) hρ]
      have h1 := norm_response_sub_series ht y
      have h2 := norm_series_sub_window ht y le_rfl
      have he : Real.exp (-(1/4:ℝ)*T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have ht1 := norm_sub_norm_le (series T y) (response T y)
      rw [norm_sub_rev] at ht1
      have ht2 := norm_sub_norm_le (∑ σ ∈ S, coefficient σ * Complex.exp (heatRate σ y*T)) (series T y)
      rw [norm_sub_rev] at ht2
      change ‖response T y‖ ≤ C at hT
      change ‖series T y - ∑ σ ∈ S, coefficient σ * Complex.exp (heatRate σ y*T)‖ ≤ _ at h2
      linarith)
  rw [heatRate_re] at hz
  dsimp only [y] at hz
  nlinarith [sq_nonneg (ρ.1.re-1/2)]

/-- The absolute first moment of the literal finite-prime discrepancy under
one fixed variance schedule. -/
def absoluteAverage (T : ℝ) : ℝ := ∫ u : ℝ, ‖discrepancy u‖ ∂gaussianReal T (2*T).toNNReal

/-- A modulated observation is bounded by the absolute first moment. -/
theorem response_le_absoluteAverage (T y : ℝ) : ‖response T y‖ ≤ absoluteAverage T := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with u
  simp [norm_twist]

private theorem discrepancy_upper {B : ℝ} (hB : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) (u : ℝ) :
    ‖discrepancy u‖ ≤ 463/10000 * Real.exp ((B-1/2)*u) + Real.exp (-(1/2:ℝ)*u) := by
  by_cases hu : 0 ≤ u
  · have hmode (ρ : NontrivialZetaZero) : ‖coefficient ρ * Complex.exp (rate ρ 0 * u)‖ ≤
        ‖coefficient ρ‖ * Real.exp ((B-1/2)*u) := by
      rw [mode_norm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_sub_right (hB ρ) _) hu)
    have hz := (norm_tsum_le_tsum_norm (summable_modes 0 u)).trans
      ((summable_modes 0 u).tsum_le_tsum hmode (summable_coeff.mul_right _))
    rw [tsum_mul_right] at hz
    have hm : ‖modes 0 u‖ ≤ 463/10000 * Real.exp ((B-1/2)*u) :=
      hz.trans (mul_le_mul_of_nonneg_right mass_lt.le (Real.exp_pos _).le)
    linarith [norm_sub_norm_le (discrepancy u) (modes 0 u), norm_discrepancy_sub_modes u]
  · simp only [discrepancy, hu, ↓reduceIte, norm_zero]
    positivity

/-- The exponential moment on the Gaussian time schedule with variance twice its mean. -/
theorem scaled_exp_mean (T a : ℝ) (ht : 0 ≤ T) :
    (∫ u : ℝ, Real.exp (a*u) ∂gaussianReal T (2*T).toNNReal) = Real.exp ((a+a^2)*T) := by
  change mgf id (gaussianReal T (2*T).toNNReal) a = _
  rw [mgf_id_gaussianReal]
  change Real.exp (T*a+((2*T).toNNReal:ℝ)*a^2/2) = _
  rw [Real.coe_toNNReal _ (by positivity)]
  exact congrArg Real.exp (by ring)

/-- Any upper bound B on the real parts gives the matching exponential rate
B² - 1/4 for the positive arithmetic average. -/
theorem absoluteAverage_le_of_re_le {B : ℝ} (hB : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B)
    {T : ℝ} (ht : 0 ≤ T) :
    absoluteAverage T ≤ 463/10000 * Real.exp ((B^2-1/4)*T) + Real.exp (-T/4) := by
  let μ := gaussianReal T (2*T).toNNReal
  have h1 : Integrable (fun u : ℝ => 463/10000 * Real.exp ((B-1/2)*u)) μ :=
    (integrable_exp_mul_gaussianReal _).const_mul _
  have h2 : Integrable (fun u : ℝ => Real.exp (-(1/2:ℝ)*u)) μ := integrable_exp_mul_gaussianReal _
  apply (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (h1.add h2)
    (Eventually.of_forall (discrepancy_upper hB))).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add h1 h2, integral_const_mul]
  change _ * (∫ u : ℝ, Real.exp ((B-1/2)*u) ∂gaussianReal T (2*T).toNNReal) +
    (∫ u : ℝ, Real.exp (-(1/2:ℝ)*u) ∂gaussianReal T (2*T).toNNReal) = _
  rw [scaled_exp_mean _ _ ht, scaled_exp_mean _ _ ht]
  ring_nf

/-- The imported seven-eighths result yields an unconditional all-time
arithmetic upper bound with exponent 33/64. -/
theorem absoluteAverage_le_seven_eighths {T : ℝ} (ht : 0 ≤ T) :
    absoluteAverage T ≤ 463/10000 * Real.exp ((33/64:ℝ)*T) + Real.exp (-T/4) := by
  convert absoluteAverage_le_of_re_le suzukiLocalZero_re_le_seven_eighths ht using 1
  norm_num

/-- Under RH the absolute first moment stays within an exponentially small
error of the reciprocal norm-square mass allowance. -/
theorem absoluteAverage_le_of_rh (h : RiemannHypothesis) {T : ℝ} (ht : 0 ≤ T) :
    absoluteAverage T ≤ 463/10000 + Real.exp (-T/4) := by
  have hh := absoluteAverage_le_of_re_le (B := 1/2) (fun ρ => (h ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le) ht
  norm_num at hh
  exact hh

/-- RH is equivalent to eventual boundedness of one positive Gaussian
average of the actual arithmetic error. -/
theorem riemannHypothesis_iff_bounded_absoluteAverage :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, absoluteAverage T ≤ C := by
  constructor
  · intro h
    refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T ht
    linarith [absoluteAverage_le_of_rh h ht, Real.exp_le_one_iff.mpr (by linarith : -T/4 ≤ 0)]
  · rintro ⟨C, hC⟩
    have hle (ρ : NontrivialZetaZero) : ρ.1.re ≤ 1/2 :=
      re_le_half_of_bounded_response ρ ⟨C, hC.mono fun T hT => (response_le_absoluteAverage T _).trans hT⟩
    intro s hs ht ho
    let ρ : NontrivialZetaZero := ⟨s,hs,ht,ho⟩
    apply le_antisymm (hle ρ)
    have hp := hle ρ.functionalPartner
    rw [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hp
    change 1-s.re ≤ 1/2 at hp
    linarith

private def node (y : ℝ) (ρ : NontrivialZetaZero) : ℂ :=
  Complex.exp (-2*Complex.I*(ρ.1-(y:ℂ)*Complex.I))

private theorem node_injective (y : ℝ) : Function.Injective (node y) := by
  intro ρ σ he
  have hi (r : NontrivialZetaZero) :
      (-2*Complex.I*(r.1-(y:ℂ)*Complex.I)).im = -2*r.1.re := by
    simp [Complex.mul_im, Complex.mul_re]
  have hh (r : NontrivialZetaZero) :
      -Real.pi < (-2*Complex.I*(r.1-(y:ℂ)*Complex.I)).im ∧
      (-2*Complex.I*(r.1-(y:ℂ)*Complex.I)).im ≤ Real.pi := by
    rw [hi]
    constructor <;> linarith [Real.pi_gt_three, r.re_lt_one, r.zero_lt_re]
  have hx := Complex.exp_inj_of_neg_pi_lt_of_le_pi (hh ρ).1 (hh ρ).2 (hh σ).1 (hh σ).2 he
  exact Subtype.ext (sub_left_inj.mp (mul_left_cancel₀ (by norm_num : (-2:ℂ)*Complex.I ≠ 0) hx))

private theorem translated_mode (ρ : NontrivialZetaZero) (y : ℝ) (n : ℕ) {T : ℝ} (ht : 0 < T) :
    Complex.exp (heatRate ρ y * T) * node y ρ ^ n =
    (Real.exp ((n:ℝ)^2/T) : ℂ) * Complex.exp (heatRate ρ (y+n/T) * T) := by
  rw [node, ← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold heatRate rate
  push_cast
  field_simp [ht.ne']
  ring_nf
  simp [Complex.I_sq]

private theorem window_le_absoluteAverage {T : ℝ} (hT : 0 ≤ T) (y : ℝ) {R : ℝ} (hR : |y|+1 ≤ R) :
    ‖∑ ρ ∈ spectralZetaZeroWindow R, coefficient ρ * Complex.exp (heatRate ρ y*T)‖ ≤
      2 + absoluteAverage T := by
  have h1 := norm_response_sub_series hT y
  have h2 := norm_series_sub_window hT y hR
  have he : Real.exp (-(1/4:ℝ)*T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht1 := norm_sub_norm_le (series T y) (response T y)
  rw [norm_sub_rev] at ht1
  have ht2 := norm_sub_norm_le (∑ ρ ∈ spectralZetaZeroWindow R, coefficient ρ *
    Complex.exp (heatRate ρ y*T)) (series T y)
  rw [norm_sub_rev] at ht2
  linarith [mass_lt, response_le_absoluteAverage T y]

private theorem node_moment_bound (y : ℝ) (n : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ‖∑ ρ ∈ spectralZetaZeroWindow (|y|+2), coefficient ρ *
        Complex.exp (heatRate ρ y*T) * node y ρ ^ n‖ ≤ Real.exp 1 * (2 + absoluteAverage T) := by
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (n:ℝ),
    eventually_ge_atTop ((n:ℝ)^2)] with T ht hn hn₂
  have hy : |y+n/T|+1 ≤ |y|+2 := by
    have ha : 0 ≤ (n:ℝ)/T := by positivity
    linarith [abs_add_le y ((n:ℝ)/T), abs_of_nonneg ha, (div_le_one ht).mpr hn]
  have hsum : (∑ ρ ∈ spectralZetaZeroWindow (|y|+2), coefficient ρ *
      Complex.exp (heatRate ρ y*T) * node y ρ ^ n) =
      (Real.exp ((n:ℝ)^2/T):ℂ) * ∑ ρ ∈ spectralZetaZeroWindow (|y|+2),
      coefficient ρ * Complex.exp (heatRate ρ (y+n/T)*T) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [mul_assoc, translated_mode ρ y n ht, mul_left_comm]
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr ((div_le_one ht).mpr hn₂))
    (window_le_absoluteAverage ht.le _ hy) (norm_nonneg _) (Real.exp_pos _).le

/-- A finite interpolation at frequencies separated by 1/T recovers each
individual zero at the same time T. The positive constant can depend on the
zero, while the lower bound holds at every sufficiently large real time. -/
theorem exponential_le_absoluteAverage (ρ : NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      Real.exp ((ρ.1.re^2-1/4)*T) ≤ C*(2 + absoluteAverage T) := by
  classical
  let y := ρ.1.im
  let S := spectralZetaZeroWindow (|y|+2)
  have hρ : ρ ∈ S := by
    dsimp only [S]
    rw [mem_spectralZetaZeroWindow (by positivity), zetaSpectralCoordinate_re]
    dsimp only [y]
    linarith
  let P := Lagrange.basis S (node y) ρ
  let A (T : ℝ) (σ : NontrivialZetaZero) := coefficient σ * Complex.exp (heatRate σ y*T)
  have hrec (T : ℝ) : A T ρ = ∑ n ∈ P.support, P.coeff n *
      ∑ σ ∈ S, A T σ * node y σ ^ n := by
    calc
      A T ρ = ∑ σ ∈ S, A T σ * P.eval (node y σ) := by
        rw [Finset.sum_eq_single_of_mem ρ hρ, Lagrange.eval_basis_self (node_injective y).injOn hρ,
          mul_one]
        intro σ hσ hne
        rw [Lagrange.eval_basis_of_ne hne.symm hσ, mul_zero]
      _ = _ := by
        simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro σ _
        ring
  let B := (∑ n ∈ P.support, ‖P.coeff n‖)*Real.exp 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc : 0 < ‖coefficient ρ‖ := norm_pos_iff.mpr (div_ne_zero
    (by exact_mod_cast (analyticZetaZeroMultiplicity_positive ρ).ne')
    (pow_ne_zero _ (Complex.ne_zero_of_re_pos ρ.zero_lt_re)))
  refine ⟨(B+1)/‖coefficient ρ‖, by positivity, ?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun n _ => node_moment_bound y n)]
    with T hT
  have hnorm : ‖A T ρ‖ ≤ B*(2+absoluteAverage T) := by
    rw [hrec]
    apply (norm_sum_le ..).trans
    calc
      _ ≤ ∑ n ∈ P.support, ‖P.coeff n‖ * (Real.exp 1 * (2 + absoluteAverage T)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hT n hn) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; dsimp only [B]; ring
  have hr : (heatRate ρ y).re = ρ.1.re^2-1/4 := by rw [heatRate_re]; dsimp only [y]; ring
  simp only [A, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, hr] at hnorm
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm _ ‖coefficient ρ‖]
  have ha : 0 ≤ absoluteAverage T := integral_nonneg fun _ => norm_nonneg _
  linarith

/-- Any one zero to the right forces the absolute first moment to infinity
along all real times. -/
theorem absoluteAverage_tendsto_atTop (ρ : NontrivialZetaZero) (hρ : 1/2 < ρ.1.re) :
    Tendsto absoluteAverage atTop atTop := by
  obtain ⟨C, hC, hbound⟩ := exponential_le_absoluteAverage ρ
  have hr : 0 < ρ.1.re^2-1/4 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hρ)]
  have ht := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr)
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [hbound, ht.eventually_ge_atTop (C*(2+K))] with T hT hl
  change C*(2+K) ≤ Real.exp ((ρ.1.re^2-1/4)*T) at hl
  exact le_of_add_le_add_left (le_of_mul_le_mul_left (hl.trans hT) hC)

/-- To force RH it suffices for the positive first moment to return below one
fixed bound at arbitrarily large times, with no spacing hypothesis. -/
theorem riemannHypothesis_iff_frequently_bounded_absoluteAverage :
    RiemannHypothesis ↔ ∃ C : ℝ, ∃ᶠ T : ℝ in atTop, absoluteAverage T ≤ C := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := riemannHypothesis_iff_bounded_absoluteAverage.mp h
    exact ⟨C, hC.frequently⟩
  · rintro ⟨C, hC⟩
    have hle (ρ : NontrivialZetaZero) : ρ.1.re ≤ 1/2 := by
      by_contra! hρ
      exact hC (((absoluteAverage_tendsto_atTop ρ hρ).eventually_gt_atTop C).mono fun _ hT => not_le.mpr hT)
    intro s hs ht ho
    let ρ : NontrivialZetaZero := ⟨s,hs,ht,ho⟩
    apply le_antisymm (hle ρ)
    have hp := hle ρ.functionalPartner
    rw [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hp
    change 1-s.re ≤ 1/2 at hp
    linarith

/-- The positive part of the finite-prime discrepancy, averaged over the same
single variance schedule. -/
def positiveAverage (T : ℝ) : ℝ :=
  ∫ u : ℝ, max (discrepancy u).re 0 ∂gaussianReal T (2*T).toNNReal

/-- The actual normalized prime discrepancy is Gaussian integrable. -/
theorem integral_discrepancy (T : ℝ) :
    Integrable discrepancy (gaussianReal T (2*T).toNNReal) := by
  have h1 := (integrable_exp_mul_gaussianReal (μ := T) (v := (2*T).toNNReal) (7/8-1/2)).const_mul
    (463/10000:ℝ)
  exact (h1.add (integrable_exp_mul_gaussianReal (-(1/2:ℝ)))).mono'
    measurable_discrepancy.aestronglyMeasurable
    (Eventually.of_forall (discrepancy_upper suzukiLocalZero_re_le_seven_eighths))

/-- Exact signed correction between the positive-part average and half the
absolute average. -/
theorem twice_positiveAverage (T : ℝ) :
    2 * positiveAverage T = absoluteAverage T + (response T 0).re := by
  let μ := gaussianReal T (2*T).toNNReal
  have hi := integral_discrepancy T
  have he : response T 0 = ∫ u, discrepancy u ∂μ := by simp [response, primeAverage, twist, μ]
  have hre : (response T 0).re = ∫ u, (discrepancy u).re ∂μ :=
    he ▸ (integral_re hi).symm
  rw [hre, positiveAverage, ← integral_const_mul, absoluteAverage]
  change _ = (∫ u, ‖discrepancy u‖ ∂μ) + ∫ u, RCLike.re (discrepancy u) ∂μ
  rw [← integral_add hi.norm hi.re]
  apply integral_congr_ae
  filter_upwards with u
  have hreal : ((discrepancy u).re : ℂ) = discrepancy u := by
    by_cases hu : 0 ≤ u
    · simp only [discrepancy, hu, ↓reduceIte, RosserSchoenfeldExplicitFormula.mainTerm_eq,
        ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
    · simp [discrepancy, hu]
  have hnorm : ‖discrepancy u‖ = |(discrepancy u).re| := by
    exact (congrArg norm hreal).symm.trans (by simp)
  change 2 * max (discrepancy u).re 0 = ‖discrepancy u‖ + (discrepancy u).re
  rw [hnorm]
  rcases le_total 0 (discrepancy u).re with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- The unmodulated signed arithmetic average tends to zero unconditionally. -/
theorem tendsto_signed_response_zero : Tendsto (fun T => response T 0) atTop (𝓝 0) := by
  have hz (ρ : NontrivialZetaZero) : rate ρ 0 ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp [rate] at hh
    have hg := ZetaFirstZeroCompleteness.no_zero_through_fourteen ρ
    simp [hh] at hg
    linarith
  simpa only [hz, ↓reduceIte, tsum_zero] using tendsto_response_through_fiftyThree (y := 0) (by norm_num)

/-- A bounded positive part on any cofinal sequence suffices for RH, since the
unconditional signed average supplies the other side. -/
theorem riemannHypothesis_iff_frequently_bounded_positiveAverage :
    RiemannHypothesis ↔ ∃ C : ℝ, ∃ᶠ T : ℝ in atTop, positiveAverage T ≤ C := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp tendsto_signed_response_zero
  have hsmall : ∀ᶠ T : ℝ in atTop, |(response T 0).re| < 1 := by
    exact (tendsto_order.mp (show Tendsto (fun T => |(response T 0).re|) atTop (𝓝 0) by
      simpa using hr.abs)).2 1 (by norm_num)
  rw [riemannHypothesis_iff_frequently_bounded_absoluteAverage]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(C+1)/2, ((hC.and_eventually hsmall).mono fun T ⟨hT, hs⟩ => ?_)⟩
    linarith [twice_positiveAverage T, (abs_lt.mp hs).2]
  · rintro ⟨C, hC⟩
    refine ⟨2*C+1, ((hC.and_eventually hsmall).mono fun T ⟨hT, hs⟩ => ?_)⟩
    linarith [twice_positiveAverage T, (abs_lt.mp hs).1]

/-- The positive prime discrepancy on the finite logarithmic interval
[T/4,4T], whose largest prime-power cutoff is exp(4T). -/
def windowPositiveAverage (T : ℝ) : ℝ :=
  ∫ u in Set.Icc (T/4) (4*T), max (discrepancy u).re 0 ∂gaussianReal T (2*T).toNNReal

/-- The positive prime discrepancy has a finite first moment under the scaled Gaussian. -/
theorem positive_integrable (T : ℝ) :
    Integrable (fun u => max (discrepancy u).re 0) (gaussianReal T (2*T).toNNReal) := by
  have hi := integral_discrepancy T
  apply hi.norm.mono'
  · exact (Complex.measurable_re.comp measurable_discrepancy |>.max measurable_const).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (Complex.re_le_norm _) (norm_nonneg _)

/-- A two-sided growth estimate on the normalized finite prime discrepancy. -/
theorem discrepancy_norm_growth (u : ℝ) : ‖discrepancy u‖ ≤ 2*Real.exp ((3/8:ℝ)*u) := by
  by_cases hu : 0 ≤ u
  · have hh := discrepancy_upper suzukiLocalZero_re_le_seven_eighths u
    rw [show (7/8:ℝ)-1/2 = 3/8 by norm_num] at hh
    have he : Real.exp (-(1/2:ℝ)*u) ≤ Real.exp ((3/8:ℝ)*u) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos ((3/8:ℝ)*u)]
  · simp only [discrepancy, hu, ↓reduceIte, norm_zero]
    positivity

/-- Gaussian tail control for each observable dominated by the unconditional
pointwise bound, including the absolute prime discrepancy. -/
theorem integral_outside_window_le {T : ℝ} (ht : 0 ≤ T) {g : ℝ → ℝ}
    (hf : Integrable g (gaussianReal T (2*T).toNNReal))
    (hg : ∀ u, g u ≤ 2*Real.exp ((3/8:ℝ)*u)) :
    (∫ u in (Set.Icc (T/4) (4*T))ᶜ, g u ∂gaussianReal T (2*T).toNNReal) ≤
      2*Real.exp (-(3/64:ℝ)*T) + 2*Real.exp (-(3/4:ℝ)*T) := by
  let μ := gaussianReal T (2*T).toNNReal
  let s := Set.Icc (T/4) (4*T)
  have hm : MeasurableSet s := measurableSet_Icc
  change (∫ u in sᶜ, g u ∂μ) ≤ _
  rw [← integral_indicator hm.compl]
  let a (u : ℝ) := (2*Real.exp ((3/16:ℝ)*T)) * Real.exp (-(3/8:ℝ)*u)
  let b (u : ℝ) := (2*Real.exp (-(9/2:ℝ)*T)) * Real.exp ((3/2:ℝ)*u)
  have ha : Integrable a μ := (integrable_exp_mul_gaussianReal _).const_mul _
  have hb : Integrable b μ := (integrable_exp_mul_gaussianReal _).const_mul _
  have hbound (u : ℝ) : sᶜ.indicator g u ≤ a u + b u := by
    by_cases hu : u ∈ s
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hu)]
      dsimp [a, b]
      positivity
    · rw [Set.indicator_of_mem hu]
      apply (hg u).trans
      change ¬ (T/4 ≤ u ∧ u ≤ 4*T) at hu
      by_cases hlow : T/4 ≤ u
      · have hhigh : 4*T < u := lt_of_not_ge fun h => hu ⟨hlow,h⟩
        apply le_add_of_nonneg_of_le (by dsimp [a]; positivity)
        dsimp [b]
        rw [mul_assoc, ← Real.exp_add]
        gcongr
        linarith
      · apply (le_add_of_le_of_nonneg _ (by dsimp [b]; positivity))
        dsimp [a]
        rw [mul_assoc, ← Real.exp_add]
        gcongr
        linarith
  apply (integral_mono (hf.indicator hm.compl) (ha.add hb) hbound).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add ha hb]
  dsimp only [a, b, μ]
  rw [integral_const_mul, integral_const_mul, scaled_exp_mean _ _ ht, scaled_exp_mean _ _ ht,
    mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- An unconditional upper bound on the entire omitted positive part,
uniform for all nonnegative observation times. -/
theorem window_positive_error {T : ℝ} (ht : 0 ≤ T) :
    0 ≤ positiveAverage T - windowPositiveAverage T ∧
    positiveAverage T - windowPositiveAverage T ≤
      2*Real.exp (-(3/64:ℝ)*T) + 2*Real.exp (-(3/4:ℝ)*T) := by
  let μ := gaussianReal T (2*T).toNNReal
  let s := Set.Icc (T/4) (4*T)
  let f (u : ℝ) := max (discrepancy u).re 0
  have hf : Integrable f μ := positive_integrable T
  have hm : MeasurableSet s := measurableSet_Icc
  have eq_tail : positiveAverage T - windowPositiveAverage T = ∫ u, sᶜ.indicator f u ∂μ := by
    rw [integral_indicator hm.compl]
    change (∫ u, f u ∂μ) - (∫ u in s, f u ∂μ) = _
    rw [← integral_add_compl hm hf, add_sub_cancel_left]
  rw [eq_tail]
  refine ⟨integral_nonneg (fun _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _), ?_⟩
  rw [integral_indicator hm.compl]
  apply integral_outside_window_le ht hf
  intro u
  exact max_le ((Complex.re_le_norm _).trans (discrepancy_norm_growth u)) (by positivity)

/-- A bounded positive part on finite logarithmic intervals at arbitrarily
large times is equivalent to RH. -/
theorem riemannHypothesis_iff_frequently_bounded_window :
    RiemannHypothesis ↔ ∃ C : ℝ, ∃ᶠ T : ℝ in atTop, windowPositiveAverage T ≤ C := by
  rw [riemannHypothesis_iff_frequently_bounded_positiveAverage]
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C, (hC.and_eventually (eventually_ge_atTop (0:ℝ))).mono fun T ⟨hT,ht⟩ =>
      by linarith [(window_positive_error ht).1]⟩
  · rintro ⟨C,hC⟩
    refine ⟨C+4, (hC.and_eventually (eventually_ge_atTop (0:ℝ))).mono fun T ⟨hT,ht⟩ => ?_⟩
    linarith [(window_positive_error ht).2,
      Real.exp_le_one_iff.mpr (by linarith : -(3/64:ℝ)*T ≤ 0),
      Real.exp_le_one_iff.mpr (by linarith : -(3/4:ℝ)*T ≤ 0)]

/-- Under RH the finite-interval positive average eventually falls below
each fixed threshold above 0.02315. -/
theorem eventually_window_le_of_rh (h : RiemannHypothesis) {c : ℝ} (hc : 463/20000 < c) :
    ∀ᶠ T : ℝ in atTop, windowPositiveAverage T ≤ c := by
  let δ := c - 463/20000
  have hd : 0 < δ := sub_pos.mpr hc
  have hdec : Tendsto (fun T : ℝ => Real.exp (-T/4)) atTop (𝓝 0) := by
    simpa only [show ∀ T : ℝ, -(1/4:ℝ)*T = -T/4 by intro T; ring] using
      exp_decay (by norm_num : -(1/4:ℝ) < 0)
  have hr : Tendsto (fun T => (response T 0).re) atTop (𝓝 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp tendsto_signed_response_zero
  filter_upwards [eventually_ge_atTop (0:ℝ), (tendsto_order.mp hdec).2 δ hd,
    (tendsto_order.mp hr).2 δ hd] with T ht h1 h2
  dsimp only [δ] at h1 h2
  linarith [absoluteAverage_le_of_rh h ht, twice_positiveAverage T, (window_positive_error ht).1]

/-- One fixed numerical assertion on arbitrarily distant finite prime
windows is equivalent to Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_window_le_one_fortieth :
    RiemannHypothesis ↔ ∃ᶠ T : ℝ in atTop, windowPositiveAverage T ≤ 1/40 :=
  ⟨fun h => (eventually_window_le_of_rh h (by norm_num)).frequently,
    fun h => riemannHypothesis_iff_frequently_bounded_window.mpr ⟨_, h⟩⟩

/-- The finite-window test as an ordinary real integral containing only an
elementary weight, the positive part, and finite von Mangoldt sums. -/
theorem windowPositiveAverage_eq_prime_integral {T : ℝ} (hT : 0 < T) :
    windowPositiveAverage T = Real.exp (-T/4) / Real.sqrt (4*Real.pi*T) *
      ∫ u in Set.Icc (T/4) (4*T), Real.exp (-u^2/(4*T)) *
        max (Real.exp u-1-Real.log (2*Real.pi)*u -
          ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, ArithmeticFunction.vonMangoldt n * (u-Real.log n)) 0 := by
  let s := Set.Icc (T/4) (4*T)
  let D (u : ℝ) := Real.exp u-1-Real.log (2*Real.pi)*u-RosserSchoenfeldPrimePrimitive.value u
  let f (u : ℝ) := max (discrepancy u).re 0
  let g (u : ℝ) := Real.exp (-u^2/(4*T)) * max (D u) 0
  let C := Real.exp (-T/4)/Real.sqrt (4*Real.pi*T)
  have hv : (2*T).toNNReal ≠ 0 := (Real.toNNReal_pos.mpr (by positivity)).ne'
  have hval (u : ℝ) (hu : u ∈ s) : f u = Real.exp (-(1/2:ℝ)*u) * max (D u) 0 := by
    have hpos : 0 ≤ u := le_trans (by positivity : 0 ≤ T/4) hu.1
    simp only [f, D, discrepancy, hpos, ↓reduceIte, RosserSchoenfeldExplicitFormula.mainTerm_eq,
      ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re, mul_max_of_nonneg _ _ (Real.exp_pos _).le,
      mul_zero]
  have hide : ∀ u, gaussianPDFReal T (2*T).toNNReal u * s.indicator f u =
      C * s.indicator g u := by
    intro u
    by_cases hu : u ∈ s
    · simp only [Set.indicator_of_mem hu, hval u hu, gaussianPDFReal, Real.coe_toNNReal _ (by positivity : 0 ≤ 2*T)]
      dsimp only [g, C]
      have he : -(u-T)^2/(2*(2*T)) + -(1/2:ℝ)*u = -T/4 + -u^2/(4*T) := by
        field_simp [hT.ne']
        ring
      rw [show 2*Real.pi*(2*T) = 4*Real.pi*T by ring]
      rw [show ∀ a b c d : ℝ, (a*b)*(c*d) = a*(b*c)*d by intros; ring,
        ← Real.exp_add, he, Real.exp_add]
      ring
    · simp [Set.indicator_of_notMem hu]
  simp_rw [← RosserSchoenfeldPrimePrimitive.value_eq_sum]
  change (∫ u in s, f u ∂gaussianReal T (2*T).toNNReal) = C * ∫ u in s, g u
  rw [← integral_indicator (μ := gaussianReal T (2*T).toNNReal) measurableSet_Icc,
    integral_gaussianReal_eq_integral_smul hv, ← integral_indicator (μ := volume) measurableSet_Icc,
    ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall hide)

end
end RiemannGaussian.QuasiRHPrimePrimitiveHeat
