/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPairDecay

/-!
# Curvature controls the full Fermi--Gaussian derivative cost

On the closed reflection strip, the actual damped amplitude is at most the
Gaussian window. Its signed second derivative is the difference of a
nonnegative squared-score density and a nonnegative curvature density.
Their full integrals agree. Estimating after that identity removes the
inverse-width loss from the Fourier bound on the closed strip.
-/

namespace RiemannGaussian.GaussianFermiFisherBound
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open EtaGammaSmoothing FermiLaplaceReflection GaussianFermiZeroPair
open GaussianFermiDerivativeBounds GaussianFermiPairDecay

/-- The positive derivative of the increasing logistic profile. -/
def logisticSlope (a t : ℝ) : ℝ := a * fermi (-a * t) * (1 - fermi (-a * t))

/-- The exact logarithmic slope of the original damped amplitude. -/
def score (a b x t : ℝ) : ℝ := -2 * b * t - x + a * (1 - fermi (-a * t))

/-- The nonnegative negative second logarithmic derivative. -/
def curvature (a b t : ℝ) : ℝ := 2 * b + a * logisticSlope a t

/-- Both logistic orientations partition one exactly. -/
theorem fermi_add_reflection (t : ℝ) : fermi (-t) + fermi t = 1 := by
  have hp := weight_partition 1 (fun _ => (1 : ℝ)) t
  have hr := weight_reflection 1 (g := fun _ => (1 : ℝ)) (fun _ => rfl) t
  norm_num [weight] at hp hr
  linarith

/-- The logistic slope has nonnegative sign. -/
theorem logisticSlope_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : 0 ≤ logisticSlope a t := by
  unfold logisticSlope
  exact mul_nonneg (mul_nonneg ha (fermi_bounds _).1.le) (by linarith [(fermi_bounds (-a*t)).2])

/-- Reflection preserves the logistic derivative density. -/
theorem logisticSlope_even (a : ℝ) : Function.Even (logisticSlope a) := by
  intro t
  have h := fermi_add_reflection (a * t)
  simp only [logisticSlope, neg_mul]
  rw [mul_neg, neg_neg]
  rw [show fermi (-(a * t)) = 1 - fermi (a * t) by linarith]
  ring

/-- The logistic slope is the genuine derivative, with its sign retained. -/
theorem hasDerivAt_logistic (a t : ℝ) :
    HasDerivAt (fun u : ℝ => fermi (-a * u)) (logisticSlope a t) t := by
  apply ((hasDerivAt_fermi (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))).congr_deriv
  dsimp only [logisticSlope, fermiOne]
  ring

/-- The increasing logistic profile converges to one at positive infinity. -/
theorem tendsto_logistic_one {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => fermi (-a * t)) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => -a * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have he := Real.tendsto_exp_atBot.comp ht
  simpa only [fermi, Function.comp_apply, add_zero, inv_one] using
    (tendsto_const_nhds.add he).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)

/-- Nonnegative differentiation and the actual logistic limits give full
integrability without an assumed density normalization. -/
theorem integrable_logisticSlope {a : ℝ} (ha : 0 < a) : Integrable (logisticSlope a) := by
  have hi : IntegrableOn (logisticSlope a) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hasDerivAt_logistic a t)
      (fun t _ => logisticSlope_nonneg ha.le t) (tendsto_logistic_one ha)
  have hc : IntegrableOn (logisticSlope a) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
  have hl : IntegrableOn (logisticSlope a) (Iic 0) := by
    have h := IntegrableOn.comp_neg_Iic (c := (0 : ℝ))
      (show IntegrableOn (logisticSlope a) (Ici (-0)) by simpa using hc)
    have he : (fun x : ℝ => logisticSlope a (-x)) = logisticSlope a :=
      funext (logisticSlope_even a)
    rwa [he] at h
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hi

/-- The logistic derivative has exact unit mass on the full real line. -/
theorem integral_logisticSlope {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, logisticSlope a t) = 1 := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
    (fun t _ => hasDerivAt_logistic a t) (fun t _ => logisticSlope_nonneg ha.le t)
    (tendsto_logistic_one ha)
  norm_num [fermi] at hi
  have habs (t : ℝ) : logisticSlope a |t| = logisticSlope a t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, logisticSlope_even a]
  have h := integral_comp_abs (f := logisticSlope a)
  simp_rw [habs] at h
  linarith

/-- The first derivative factors through the actual logarithmic slope. -/
theorem dampedOne_eq_score (a b x t : ℝ) :
    dampedOne a b x t = score a b x t * damped a b x t := by
  unfold dampedOne score damped fermiOne
  ring

/-- The exact signed second derivative retains the squared score and the
curvature before either positive piece is estimated. -/
theorem dampedTwo_eq_score_curvature (a b x t : ℝ) :
    dampedTwo a b x t = score a b x t ^ 2 * damped a b x t -
      curvature a b t * damped a b x t := by
  unfold dampedTwo score curvature logisticSlope damped fermiOne fermiTwo
  ring

/-- The full curvature has nonnegative sign at nonnegative Gaussian scale. -/
theorem curvature_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ) :
    0 ≤ curvature a b t := by
  exact add_nonneg (mul_nonneg (by norm_num) hb) (mul_nonneg ha (logisticSlope_nonneg ha t))

/-- Closed-strip geometry bounds the amplitude by the Gaussian itself. -/
theorem damped_le_window {a b x : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) (t : ℝ) :
    damped a b x t ≤ window b t := by
  simpa [window] using damped_le_exp_abs (δ := 0) (by simpa using hx) (by simpa using hxa) t

/-- The curvature density has an integrable majorant with a small Gaussian
mass term and the exact logistic derivative density. -/
theorem curvature_density_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hxa : x ≤ a) (t : ℝ) :
    curvature a b t * damped a b x t ≤ 2 * b * window b t + a * logisticSlope a t := by
  have hW := damped_le_window (b := b) hx hxa t
  have h1 : damped a b x t ≤ 1 := hW.trans (by
    unfold window
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t]))
  unfold curvature
  rw [add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hW (by positivity))
    (by simpa using mul_le_mul_of_nonneg_left h1 (mul_nonneg ha (logisticSlope_nonneg ha t)))

/-- The curvature density is genuinely integrable at every positive width,
uniformly over the full closed reflection strip including its endpoints. -/
theorem integrable_curvature_density {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    Integrable (fun t : ℝ => curvature a b t * damped a b x t) := by
  have hi : Integrable (fun t : ℝ => 2 * b * window b t + a * logisticSlope a t) :=
    ((integrable_exp_neg_mul_sq hb).const_mul (2 * b)).add ((integrable_logisticSlope ha).const_mul a)
  have hf := continuous_fermi
  apply hi.mono' (by unfold curvature logisticSlope damped; fun_prop)
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (curvature_nonneg ha.le hb.le t) (damped_pos _ _ _ _).le)]
  exact curvature_density_le ha.le hb.le hx hxa t

/-- The total curvature density has no inverse-width loss. -/
theorem integral_curvature_density_le {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫ t : ℝ, curvature a b t * damped a b x t) ≤ 2 * b * Real.sqrt (Real.pi / b) + a := by
  have hiW : Integrable (window b) := integrable_exp_neg_mul_sq hb
  have hiL := integrable_logisticSlope ha
  have h := integral_mono (integrable_curvature_density ha hb hx hxa)
    ((hiW.const_mul (2*b)).add (hiL.const_mul a)) (curvature_density_le ha.le hb.le hx hxa)
  change (∫ t : ℝ, curvature a b t * damped a b x t) ≤
    ∫ t : ℝ, 2 * b * window b t + a * logisticSlope a t at h
  rw [integral_add (hiW.const_mul (2*b)) (hiL.const_mul a), integral_const_mul,
    integral_const_mul, integral_logisticSlope ha, mul_one] at h
  simpa only [window, integral_gaussian] using h

/-- The actual squared logarithmic slope is integrable against its own
amplitude; this follows from the signed derivative identity. -/
theorem integrable_score_density {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    Integrable (fun t : ℝ => score a b x t ^ 2 * damped a b x t) := by
  have hd := (integrable_damped_orders ha.le hb (δ := 0) le_rfl (by simpa using hb.le)
    (by simpa using hx) (by simpa using hxa)).2.2
  apply (hd.add (integrable_curvature_density ha hb hx hxa)).congr
  filter_upwards with t
  simp only [Pi.add_apply, dampedTwo_eq_score_curvature]
  ring

/-- The squared-score integral equals the curvature integral exactly.
This is the unnormalized Fisher-information identity for the actual signal. -/
theorem integral_score_eq_curvature {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫ t : ℝ, score a b x t ^ 2 * damped a b x t) =
      ∫ t : ℝ, curvature a b t * damped a b x t := by
  obtain ⟨_, h1, h2⟩ := integrable_damped_orders ha.le hb (δ := 0) le_rfl (by simpa using hb.le)
    (by simpa using hx) (by simpa using hxa)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable (hasDerivAt_dampedOne a b x) h2 h1
  simp_rw [dampedTwo_eq_score_curvature] at hz
  rw [integral_sub (integrable_score_density ha hb hx hxa)
    (integrable_curvature_density ha hb hx hxa)] at hz
  exact sub_eq_zero.mp hz

/-- Estimating only after the signed balance gives a closed-strip second
derivative bound that remains finite as the Gaussian width tends to zero. -/
theorem integral_abs_dampedTwo_le_curvature {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫ t : ℝ, |dampedTwo a b x t|) ≤ 4 * b * Real.sqrt (Real.pi / b) + 2 * a := by
  have h2 := (integrable_damped_orders ha.le hb (δ := 0) le_rfl (by simpa using hb.le)
    (by simpa using hx) (by simpa using hxa)).2.2
  have hs := integrable_score_density ha hb hx hxa
  have hc := integrable_curvature_density ha hb hx hxa
  have hp (t : ℝ) : |dampedTwo a b x t| ≤ score a b x t ^ 2 * damped a b x t +
      curvature a b t * damped a b x t := by
    rw [dampedTwo_eq_score_curvature]
    apply (abs_sub _ _).trans_eq
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (damped_pos _ _ _ _).le),
      abs_of_nonneg (mul_nonneg (curvature_nonneg ha.le hb.le t) (damped_pos _ _ _ _).le)]
  have h := integral_mono h2.abs (hs.add hc) hp
  simp only [Pi.add_apply] at h
  rw [integral_add hs hc, integral_score_eq_curvature ha hb hx hxa] at h
  linarith [integral_curvature_density_le ha hb hx hxa]

/-- The full complex analytic reflection inherits the improved frequency
bound on the closed strip, without identifying distinct complex carriers. -/
theorem im_sq_mul_norm_pair_le_curvature {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) :
    z.im ^ 2 * ‖transform a (window b) z + transform a (window b) ((a : ℂ) - z)‖ ≤
      4 * b * Real.sqrt (Real.pi / b) + 2 * a := by
  obtain ⟨h0, h1, h2⟩ := integrable_damped_orders ha.le hb (δ := 0) le_rfl (by simpa using hb.le)
    (by simpa using hz0) (by simpa using hza)
  have he := oscillatory_second_derivative (hasDerivAt_damped a b z.re)
    (hasDerivAt_dampedOne a b z.re) h0 h1 h2 z.im
  have hn := congrArg norm he
  have hn' : ‖oscillatory (dampedTwo a b z.re) z.im‖ =
      z.im ^ 2 * ‖oscillatory (damped a b z.re) z.im‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, sq_abs] using hn
  rw [pair_eq_oscillatory hb, ← hn']
  exact (norm_oscillatory_le h2 z.im).trans (integral_abs_dampedTwo_le_curvature ha hb hz0 hza)

/-- The Gaussian part of the curvature cost is uniformly bounded on
positive scales at most one. -/
theorem gaussian_curvature_cost_le {b : ℝ} (hb : 0 < b) (hbu : b ≤ 1) :
    b * Real.sqrt (Real.pi / b) ≤ Real.sqrt Real.pi := by
  calc
    _ = Real.sqrt (b ^ 2) * Real.sqrt (Real.pi / b) := by rw [Real.sqrt_sq hb.le]
    _ = Real.sqrt (b * Real.pi) := by
      rw [← Real.sqrt_mul (sq_nonneg b)]
      congr 1
      field_simp
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])

/-- The complex reflected pair has a constant inverse-square frequency
bound, uniformly down to arbitrarily small positive Gaussian widths. -/
theorem im_sq_mul_norm_pair_le_uniform {a b : ℝ} (ha : 0 < a) (hau : a ≤ 1)
    (hb : 0 < b) (hbu : b ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a) :
    z.im ^ 2 * ‖transform a (window b) z + transform a (window b) ((a : ℂ) - z)‖ ≤
      4 * Real.sqrt Real.pi + 2 := by
  have h := im_sq_mul_norm_pair_le_curvature ha hb hz0 hza
  linarith [gaussian_curvature_cost_le hb hbu]

/-- The physical same-phase pair inherits only the real-part estimate;
the distinct complex analytic reflection remains explicit in the proof. -/
theorem abs_physical_pair_re_le_uniform {a b : ℝ} (ha : 0 < a) (hau : a ≤ 1)
    (hb : 0 < b) (hbu : b ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.re) (hza : z.re ≤ a)
    (hy : z.im ≠ 0) :
    |(transform a (window b) z +
      transform a (window b) ((a : ℂ) - starRingEnd ℂ z)).re| ≤
      (4 * Real.sqrt Real.pi + 2) / z.im ^ 2 := by
  rw [physical_pair_re_eq]
  apply (Complex.abs_re_le_norm _).trans
  apply (le_div_iff₀ (sq_pos_of_ne_zero hy)).mpr
  simpa only [mul_comm] using im_sq_mul_norm_pair_le_uniform ha hau hb hbu hz0 hza

end
end RiemannGaussian.GaussianFermiFisherBound
