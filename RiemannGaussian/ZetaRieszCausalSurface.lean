/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszArtificialModeAudit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# A causal pole-surface subtraction and a joint radial bound for the regression model

A cutoff-only multiplier matches the complete selected pole surface.
Its inverse stays on the triangular cone. The remaining toy kernel has
an exponential gain on the strict core, before radial integration.
These are exact results for the regression model, not a zeta packet bound.
-/

namespace RiemannGaussian.ZetaRieszCausalSurface
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszZeroParityCascade ZetaRieszAnalyticFactorAudit

/-- Convolution on the positive cutoff ray; the mode is arbitrary. -/
def cutoffRay (b : ℂ) (f : ZetaRieszNegativeModeSupport.Test) :
    ZetaRieszNegativeModeSupport.Test :=
  fun s d => ∫ t : ℝ in Ioi 0, Complex.exp (b*t)*f s (d+t)

/-- A cutoff convolution preserves the full support cone. -/
theorem cutoffRay_vanishes (b : ℂ) {f : ZetaRieszNegativeModeSupport.Test}
    (hf : ZetaRieszNegativeModeSupport.VanishesOnCone f) :
    ZetaRieszNegativeModeSupport.VanishesOnCone (cutoffRay b f) := by
  intro s d hs hd
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [hf s (d+t) hs (by linarith [show 0 < t from ht]), mul_zero]

/-- The causal normal multiplier is 1/(z-b), on its convergence half-plane. -/
theorem cutoffRay_laplace (b w z : ℂ) (hz : b.re < z.re) :
    cutoffRay b (ZetaRieszNegativeModeSupport.laplaceTest w z) =
      fun s d => (1/(z-b))*ZetaRieszNegativeModeSupport.laplaceTest w z s d := by
  funext s d
  unfold cutoffRay
  have he (t : ℝ) :
      Complex.exp (b*t)*ZetaRieszNegativeModeSupport.laplaceTest w z s (d+t) =
      ZetaRieszNegativeModeSupport.laplaceTest w z s d*Complex.exp ((b-z)*t) := by
    simp only [ZetaRieszNegativeModeSupport.laplaceTest, Complex.ofReal_add]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show b-z = -(z-b) by ring]
  simp only [div_neg, neg_neg, one_div, mul_comm, neg_div]

/-- The entire selected pole surface is matched by a z-only multiplier. -/
theorem causal_response_split (w z : ℂ) (hz : z ≠ 0) (hws : w+z ≠ 0)
    (hw : w+1 ≠ 0) (hz1 : z-1 ≠ 0) :
    toyResponse w z = 1/((1-z)*z*(w+z))+1/(z*(w+1)*(z-1)) := by
  rw [toyResponse_eq w z hz hws hw]
  have h1z : 1-z ≠ 0 := by intro h; apply hz1; linear_combination -h
  field_simp
  ring

/-- Matching the full normal-pole trace, rather than one of its values,
removes the pole for every fixed z. Causality of that trace is a separate
condition, proved above for the rational cutoff multipliers. -/
theorem surface_subtraction_removable {H : ℂ → ℂ → ℂ} (z : ℂ)
    (hH : AnalyticAt ℂ (fun w => H w z) (-z)) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (-z) ∧
      (fun w => w*(H w z-H (-z) z)/(w+z)) =ᶠ[𝓝[≠] (-z)] F := by
  let G := fun w => w*(H w z-H (-z) z)
  have hG : AnalyticAt ℂ G (-z) := analyticAt_id.mul (hH.sub analyticAt_const)
  obtain ⟨F, hF, he⟩ := exists_analytic_poleTaylor_remainder hG 1
  refine ⟨F, hF, ?_⟩
  filter_upwards [he] with w hw
  simp only [poleTaylorPrincipalPart, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, iteratedDeriv_zero, one_mul, pow_one] at hw
  have hzero : G (-z) = 0 := by simp [G]
  simpa only [hzero, zero_div, sub_zero, sub_neg_eq_add, G] using hw

/-- The supported ordinary inverse of the first summand. -/
def supportedKernel (s d : ℝ) : ℂ :=
  (supportKernel s d : ℂ)*(1-Complex.exp ((d-s : ℝ) : ℂ))

/-- The remainder has no selected diagonal pole. -/
def remainderKernel (s d : ℝ) : ℂ :=
  Complex.exp (-(s : ℂ))*(Complex.exp (d : ℂ)-1)

private theorem exp_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(a : ℂ)*x)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha) 0

private theorem exp_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-(a : ℂ)*x)) = 1/(a : ℂ) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos ha)]
  simp

/-- Exact ordinary one-sided double inverse of the remaining rational
term after the complete selected-pole subtraction. -/
theorem remainderKernel_transform {w z : ℝ} (hw : 0 < w) (hz : 1 < z) :
    (∫ s : ℝ in Ioi 0, Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*remainderKernel s d)) =
      1/((z : ℂ)*(w+1)*(z-1)) := by
  have hi (s : ℝ) :
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*remainderKernel s d) =
      Complex.exp (-(s : ℂ))*(1/((z-1 : ℝ) : ℂ)-1/(z : ℂ)) := by
    have he (d : ℝ) : Complex.exp (-(z : ℂ)*d)*remainderKernel s d =
        Complex.exp (-(s : ℂ))*(Complex.exp (-((z-1 : ℝ) : ℂ)*d)-
          Complex.exp (-(z : ℂ)*d)) := by
      have he' : Complex.exp (-(z : ℂ)*d)*Complex.exp (d : ℂ) =
          Complex.exp (-((z-1 : ℝ) : ℂ)*d) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      dsimp [remainderKernel]
      linear_combination Complex.exp (-(s : ℂ))*he'
    simp_rw [he]
    rw [integral_const_mul, integral_sub (exp_integrable (by linarith : 0 < z-1))
      (exp_integrable (by linarith : 0 < z)), exp_integral (by linarith : 0 < z-1),
      exp_integral (by linarith : 0 < z)]
  simp_rw [hi, ← mul_assoc]
  have he (s : ℝ) : Complex.exp (-(w : ℂ)*s)*Complex.exp (-(s : ℂ)) =
      Complex.exp (-((w+1 : ℝ) : ℂ)*s) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_mul_const, exp_integral (by linarith : 0 < w+1)]
  have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast (by linarith : z ≠ 0)
  have hz1 : (z-1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : z-1 ≠ 0)
  have hw1 : (w+1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : w+1 ≠ 0)
  push_cast
  field_simp
  ring

theorem supportedKernel_below {s d : ℝ} (h : d < s) : supportedKernel s d = 0 := by
  simp [supportedKernel, supportKernel_eq_zero h]

/-- Exact equality of the original inverse, including the one-sided
boundary term; the carrier is not changed by the subtraction. -/
theorem kernel_split (s d : ℝ) :
    leakageKernel s d = supportedKernel s d+remainderKernel s d := by
  have he : Complex.exp (-(s : ℂ))*Complex.exp (d : ℂ) =
      Complex.exp ((d-s : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp [leakageKernel, supportedKernel, remainderKernel]
  linear_combination -(supportKernel s d : ℂ)*he

/-- On the positive strict core, the complete remaining kernel has a
pointwise exponential gain in the physical gap. -/
theorem remainderKernel_norm_le {s d : ℝ} (hd : 0 ≤ d) :
    ‖remainderKernel s d‖ ≤ Real.exp (d-s) := by
  have hp : 0 ≤ Real.exp d-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hd)
  have he : remainderKernel s d = ((Real.exp (-s)*(Real.exp d-1) : ℝ) : ℂ) := by
    simp [remainderKernel, Complex.ofReal_exp]
  rw [he, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hp)]
  calc
    _ ≤ Real.exp (-s)*Real.exp d := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = Real.exp (d-s) := by rw [← Real.exp_add]; congr 1; ring

theorem remainderKernel_core_bound {s d T g : ℝ}
    (hd : 0 ≤ d) (hgap : g*T ≤ s-d) :
    ‖remainderKernel s d‖ ≤ Real.exp (-g*T) := by
  exact (remainderKernel_norm_le hd).trans (Real.exp_le_exp.mpr (by linarith))

/-- The same estimate bounds the full toy inverse below the diagonal,
not merely an algebraically chosen remainder. -/
theorem leakageKernel_core_bound {s d T g : ℝ}
    (hd : 0 ≤ d) (hds : d < s) (hgap : g*T ≤ s-d) :
    ‖leakageKernel s d‖ ≤ Real.exp (-g*T) := by
  rw [kernel_split, supportedKernel_below hds, zero_add]
  exact remainderKernel_core_bound hd hgap

private theorem radial_integrable (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun T : ℝ => T^N*Real.exp (-a*T)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : (-1 : ℝ) < N) (by norm_num : (0 : ℝ) < 1) ha
  simpa using h

theorem radial_integral (N : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ T : ℝ in Ioi 0, T^N*Real.exp (-a*T)) = (N.factorial : ℝ)/a^(N+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : (0 : ℝ) < (N : ℝ)+1) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  simp_rw [neg_mul]
  rw [h]
  rw [show (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, div_pow, one_pow]
  ring

/-- Joint radial estimate after the pointwise core gain. Any masks and
fixed-height phase may be kept inside f, subject to the displayed bound. -/
theorem radial_bound (N : ℕ) {u g : ℝ} (hu : 0 ≤ u) (hg : 0 < 1/2+g)
    {f : ℝ → ℂ} (hf : ∀ T > 0, ‖f T‖ ≤ Real.exp (-g*T)) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*f T)‖ ≤
      (u/(1/2+g))^(N+1) := by
  have hnorm : ‖∫ T : ℝ in Ioi 0,
      ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*f T‖ ≤
      ∫ T : ℝ in Ioi 0, T^N*Real.exp (-(1/2+g)*T)/(N.factorial : ℝ) := by
    apply norm_integral_le_of_norm_le ((radial_integrable N hg).div_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTp : 0 < T := hT
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.exp (-T/2)*T^N/(N.factorial : ℝ))*Real.exp (-g*T) :=
        mul_le_mul_of_nonneg_left (hf T hT) (by positivity)
      _ = _ := by
        have he : Real.exp (-T/2)*Real.exp (-g*T) = Real.exp (-(1/2+g)*T) := by
          rw [← Real.exp_add]; congr 1; ring
        linear_combination (T^N/(N.factorial : ℝ))*he
  rw [integral_div, radial_integral N hg] at hnorm
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ u^(N+1)*((N.factorial : ℝ)/(1/2+g)^(N+1)/(N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [div_pow]; field_simp

/-- The regression model's full radial source is geometrically small on
the strict core, uniformly throughout the requested radius interval. -/
theorem core_radial_bound (N : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 10001/20000)
    {f : ℝ → ℂ} (hf : ∀ T > 0, ‖f T‖ ≤ Real.exp (-(7/25 : ℝ)*T)) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*f T)‖ ≤
      (2/3 : ℝ)^(N+1) := by
  refine (radial_bound N hu (by norm_num : (0 : ℝ) < 1/2+7/25) hf).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num
  linarith

/-- The regression response on the actual moving core, with its phase and
largest-share mask. The one-sided cutoff boundary is explicit. -/
def maskedToy (u y p : ℝ) (N : ℕ) (T : ℝ) : ℂ :=
  if 39/20*(N : ℝ) < T ∧ T ≤ 203/100*(N : ℝ) ∧
      43/80 ≤ p ∧ p ≤ 9/16 ∧ 0 ≤ SquarefreeVaughanLogSource.length u N-p*T then
    Complex.exp (-Complex.I*y*T)*leakageKernel ((1-p)*T)
      (SquarefreeVaughanLogSource.length u N-p*T)
  else 0

theorem measurable_maskedToy (u y p : ℝ) (N : ℕ) : Measurable (maskedToy u y p N) := by
  have hconst (P : Prop) : MeasurableSet {T : ℝ | P} := by
    by_cases h : P <;> simp [h]
  have hs : MeasurableSet {T : ℝ | (1-p)*T ≤ SquarefreeVaughanLogSource.length u N-p*T} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hhR : Measurable (fun T : ℝ =>
      supportKernel ((1-p)*T) (SquarefreeVaughanLogSource.length u N-p*T)) :=
    measurable_const.ite hs measurable_const
  have hh := Complex.continuous_ofReal.measurable.comp hhR
  have hg : Measurable (fun T : ℝ => leakageKernel ((1-p)*T)
      (SquarefreeVaughanLogSource.length u N-p*T)) := by
    unfold leakageKernel
    fun_prop
  have hm0 : MeasurableSet {T : ℝ | 39/20*(N : ℝ) < T} :=
    (isOpen_lt continuous_const continuous_id).measurableSet
  have hm1 : MeasurableSet {T : ℝ | T ≤ 203/100*(N : ℝ)} :=
    (isClosed_le continuous_id continuous_const).measurableSet
  have hm2 : MeasurableSet {T : ℝ | 0 ≤ SquarefreeVaughanLogSource.length u N-p*T} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hm : MeasurableSet {T : ℝ | 39/20*(N : ℝ) < T ∧ T ≤ 203/100*(N : ℝ) ∧
      43/80 ≤ p ∧ p ≤ 9/16 ∧ 0 ≤ SquarefreeVaughanLogSource.length u N-p*T} := by
    simpa only [ofPred_and] using hm0.inter
      (hm1.inter ((hconst (43/80 ≤ p)).inter ((hconst (p ≤ 9/16)).inter hm2)))
  exact ((show Measurable (fun T : ℝ => Complex.exp (-Complex.I*y*T)) by fun_prop).mul hg).ite
    hm measurable_const

theorem maskedToy_core_bound {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (y p : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖maskedToy u y p N T‖ ≤ Real.exp (-(7/25 : ℝ)*T) := by
  unfold maskedToy
  split_ifs with h
  · have hL := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hlog : 2*Real.log 2 ≤ (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hlen : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N :=
      hL.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
    have hgap : (7/25 : ℝ)*T < ((1-p)*T)-(SquarefreeVaughanLogSource.length u N-p*T) := by
      nlinarith [h.1, Nat.cast_nonneg (α := ℝ) N]
    rw [norm_mul, Complex.norm_exp]
    have hphase : (-Complex.I*(y : ℂ)*(T : ℂ)).re = 0 := by simp
    rw [hphase, Real.exp_zero, one_mul]
    exact leakageKernel_core_bound h.2.2.2.2 (by nlinarith) hgap.le
  · simp only [norm_zero]
    exact (Real.exp_pos _).le

/-- The toy radial integral is genuinely integrable; its bound does not
rely on the totalized value of a nonintegrable Bochner integral. -/
theorem integrable_maskedToy {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (y p : ℝ) :
    IntegrableOn (fun T : ℝ =>
      ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*maskedToy u y p N T) (Ioi 0) := by
  apply ((radial_integrable N (by norm_num : (0 : ℝ) < 1/2+7/25)).div_const
    (N.factorial : ℝ)).mono'
  · apply AEStronglyMeasurable.mul
    · exact (show Continuous (fun T : ℝ =>
        ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)) by fun_prop).aestronglyMeasurable
    · exact (measurable_maskedToy u y p N).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTp : 0 < T := hT
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.exp (-T/2)*T^N/(N.factorial : ℝ))*Real.exp (-(7/25 : ℝ)*T) :=
        mul_le_mul_of_nonneg_left (maskedToy_core_bound hu hN y p hTp) (by positivity)
      _ = _ := by
        have he : Real.exp (-T/2)*Real.exp (-(7/25 : ℝ)*T) =
            Real.exp (-(1/2+7/25 : ℝ)*T) := by
          rw [← Real.exp_add]; congr 1; ring
        linear_combination (T^N/(N.factorial : ℝ))*he

/-- An explicit joint estimate for the original counterexample on the
literal moving radial window: no fixed total-log slice is substituted. -/
theorem maskedToy_radial_decay {u : ℝ} (hu : 1/2 ≤ u) (hu1 : u ≤ 10001/20000)
    {N : ℕ} (hN : 2 ≤ N) (y p : ℝ) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*
        maskedToy u y p N T)‖ ≤ (2/3 : ℝ)^(N+1) :=
  core_radial_bound N (by linarith) hu1 (fun _ hT => maskedToy_core_bound hu hN y p hT)

theorem maskedToy_radial_small {u : ℝ} (hu : 1/2 ≤ u) (hu1 : u ≤ 10001/20000)
    {N : ℕ} (hN : 20 ≤ N) (y p : ℝ) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*
        maskedToy u y p N T)‖ < 1/1000 := by
  refine lt_of_le_of_lt ((maskedToy_radial_decay hu hu1 (by omega) y p).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num : (2/3 : ℝ) ≤ 1)
      (show 21 ≤ N+1 by omega))) ?_
  norm_num

/-- The physical selected-mode displacement from the radial center 1/2. -/
def sourceShift (u : ℝ) : ℝ := 1/2-u

/-- The source-matched count factor. Its normalized slice is exactly the
original analytic-factor counterexample, not a change of physical units. -/
def sourceFactor (u : ℝ) (w z : ℂ) : ℂ :=
  ((w-sourceShift u)/(w+z-sourceShift u))*
    ((w+z-sourceShift u+u)/(w-sourceShift u+u))

theorem sourceFactor_path {u : ℝ} (hu : u ≠ 0) {t : ℂ} (ht : t ≠ 1) :
    sourceFactor u (1/2) (-(u : ℂ)*t) = (1/(1-t))*(1-t/2) := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have htC : 1-t ≠ 0 := sub_ne_zero.mpr ht.symm
  unfold sourceFactor sourceShift
  push_cast
  have he0 : (1/2 : ℂ)+ -↑u*t-(1/2-↑u) = ↑u*(1-t) := by ring
  have he1 : (1/2 : ℂ)-(1/2-↑u)+↑u = 2*↑u := by ring
  rw [he0, he1]
  field_simp
  ring

/-- Exact two-variable response with the selected source at its physical
location. All boundary and empty-cofactor terms remain. -/
theorem sourceFactor_response {u : ℝ} (w z : ℂ) (hz : z ≠ 0)
    (h0 : w+z-sourceShift u ≠ 0) (h1 : w-sourceShift u+u ≠ 0) :
    (1-sourceFactor u w z)/z^2 =
      (u : ℂ)/(z*(w+z-sourceShift u)*(w-sourceShift u+u)) := by
  unfold sourceFactor
  field_simp
  ring

/-- The same whole-surface subtraction in the original normalization. -/
theorem sourceFactor_split {u : ℝ} (w z : ℂ) (hz : z ≠ 0)
    (h0 : w+z-sourceShift u ≠ 0) (h1 : w-sourceShift u+u ≠ 0)
    (hu : (u : ℂ)-z ≠ 0) :
    (1-sourceFactor u w z)/z^2 =
      (u : ℂ)/((u-z)*z*(w+z-sourceShift u))+
      (u : ℂ)/(z*(w-sourceShift u+u)*(z-u)) := by
  rw [sourceFactor_response w z hz h0 h1]
  have hzu : z-(u : ℂ) ≠ 0 := by intro h; apply hu; linear_combination -h
  field_simp
  ring

/-- Scaled and shifted ordinary inverse for the exact source-matched toy. -/
def sourceKernel (u s d : ℝ) : ℂ :=
  Complex.exp ((sourceShift u*s : ℝ) : ℂ)*leakageKernel (u*s) (u*d)

/-- Scaling both Laplace variables and translating the selected mode gives
an exact inverse transform, rather than just a coefficient analogy. -/
theorem sourceKernel_transform {u w z : ℝ} (hu : 0 < u)
    (hw : sourceShift u < w) (hz : u < z) :
    (∫ s : ℝ in Ioi 0, Complex.exp (-(w : ℂ)*s)*
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*sourceKernel u s d)) =
      (1-sourceFactor u w z)/(z : ℂ)^2 := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  let F := fun s : ℝ => ∫ d : ℝ in Ioi 0,
    Complex.exp (-((z/u : ℝ) : ℂ)*d)*leakageKernel s d
  have inner (s : ℝ) :
      (∫ d : ℝ in Ioi 0, Complex.exp (-(z : ℂ)*d)*sourceKernel u s d) =
      Complex.exp ((sourceShift u*s : ℝ) : ℂ)*(u⁻¹ : ℝ)*F (u*s) := by
    have he (d : ℝ) : Complex.exp (-(z : ℂ)*d)*sourceKernel u s d =
        Complex.exp ((sourceShift u*s : ℝ) : ℂ)*
          (Complex.exp (-((z/u : ℝ) : ℂ)*(u*d))*leakageKernel (u*s) (u*d)) := by
      unfold sourceKernel
      have hx : -((z/u : ℝ) : ℂ)*(u*d) = -(z : ℂ)*d := by
        push_cast; field_simp
      rw [hx]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    have h := integral_comp_mul_left_Ioi
      (fun x : ℝ => Complex.exp (-((z/u : ℝ) : ℂ)*x)*leakageKernel (u*s) x) 0 hu
    simp only [mul_zero, Complex.ofReal_mul, Complex.real_smul] at h
    rw [h]
    simp only [F, mul_assoc]
  simp_rw [inner, ← mul_assoc]
  have he (s : ℝ) : Complex.exp (-(w : ℂ)*s)*
      Complex.exp ((sourceShift u*s : ℝ) : ℂ) =
      Complex.exp (-(((w-sourceShift u)/u : ℝ) : ℂ)*(u*s)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [he]
  simp_rw [show ∀ s : ℝ, Complex.exp (-(((w-sourceShift u)/u : ℝ) : ℂ)*(u*s))*
      ((u⁻¹ : ℝ) : ℂ)*F (u*s) = ((u⁻¹ : ℝ) : ℂ)*
      (Complex.exp (-(((w-sourceShift u)/u : ℝ) : ℂ)*(u*s))*F (u*s)) by intro s; ring]
  rw [integral_const_mul]
  have ho := integral_comp_mul_left_Ioi
    (fun x : ℝ => Complex.exp (-(((w-sourceShift u)/u : ℝ) : ℂ)*x)*F x) 0 hu
  simp only [mul_zero, Complex.ofReal_mul, Complex.real_smul] at ho
  rw [ho]
  dsimp only [F]
  rw [leakageKernel_transform (div_pos (sub_pos.mpr hw) hu)
    ((lt_div_iff₀ hu).mpr (by linarith))]
  have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast (by linarith : z ≠ 0)
  have hwz : (w : ℂ)+z-sourceShift u ≠ 0 := by
    exact_mod_cast (by linarith : w+z-sourceShift u ≠ 0)
  have hw1 : (w : ℂ)-sourceShift u+u ≠ 0 := by
    exact_mod_cast (by linarith : w-sourceShift u+u ≠ 0)
  rw [sourceFactor_response _ _ hzc hwz hw1]
  have hwz' : (w : ℂ)-sourceShift u+z ≠ 0 := by
    convert hwz using 1
    ring
  unfold toyResponse toyFactor
  push_cast
  field_simp
  ring

theorem sourceKernel_core_bound {u s d T : ℝ} (hu : 1/2 ≤ u)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hds : d < s) (_hT : 0 ≤ T)
    (hgap : (7/25 : ℝ)*T ≤ s-d) :
    ‖sourceKernel u s d‖ ≤ Real.exp (-(7/50 : ℝ)*T) := by
  have hu0 : 0 < u := by linarith
  have hgap' : (7/50 : ℝ)*T ≤ u*s-u*d := by nlinarith
  rw [sourceKernel, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  have he : Real.exp (sourceShift u*s) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by dsimp [sourceShift]; linarith) hs
  calc
    _ ≤ 1*‖leakageKernel (u*s) (u*d)‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact leakageKernel_core_bound (mul_nonneg hu0.le hd)
        (mul_lt_mul_of_pos_left hds hu0) hgap'

/-- The normalized regression on the same moving length and literal radial
window. Its selected-source location and analytic pole are source-matched. -/
def sourceMaskedToy (u y p : ℝ) (N : ℕ) (T : ℝ) : ℂ :=
  if 39/20*(N : ℝ) < T ∧ T ≤ 203/100*(N : ℝ) ∧
      43/80 ≤ p ∧ p ≤ 9/16 ∧ 0 ≤ SquarefreeVaughanLogSource.length u N-p*T then
    Complex.exp (-Complex.I*y*T)*sourceKernel u ((1-p)*T)
      (SquarefreeVaughanLogSource.length u N-p*T)
  else 0

theorem measurable_sourceMaskedToy (u y p : ℝ) (N : ℕ) :
    Measurable (sourceMaskedToy u y p N) := by
  have hconst (P : Prop) : MeasurableSet {T : ℝ | P} := by
    by_cases h : P <;> simp [h]
  have hs : MeasurableSet {T : ℝ | u*((1-p)*T) ≤
      u*(SquarefreeVaughanLogSource.length u N-p*T)} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hhR : Measurable (fun T : ℝ => supportKernel (u*((1-p)*T))
      (u*(SquarefreeVaughanLogSource.length u N-p*T))) :=
    measurable_const.ite hs measurable_const
  have hh := Complex.continuous_ofReal.measurable.comp hhR
  have hg : Measurable (fun T : ℝ => sourceKernel u ((1-p)*T)
      (SquarefreeVaughanLogSource.length u N-p*T)) := by
    unfold sourceKernel leakageKernel
    fun_prop
  have hm0 : MeasurableSet {T : ℝ | 39/20*(N : ℝ) < T} :=
    (isOpen_lt continuous_const continuous_id).measurableSet
  have hm1 : MeasurableSet {T : ℝ | T ≤ 203/100*(N : ℝ)} :=
    (isClosed_le continuous_id continuous_const).measurableSet
  have hm2 : MeasurableSet {T : ℝ | 0 ≤ SquarefreeVaughanLogSource.length u N-p*T} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hm : MeasurableSet {T : ℝ | 39/20*(N : ℝ) < T ∧ T ≤ 203/100*(N : ℝ) ∧
      43/80 ≤ p ∧ p ≤ 9/16 ∧ 0 ≤ SquarefreeVaughanLogSource.length u N-p*T} := by
    simpa only [ofPred_and] using hm0.inter
      (hm1.inter ((hconst (43/80 ≤ p)).inter ((hconst (p ≤ 9/16)).inter hm2)))
  exact ((show Measurable (fun T : ℝ => Complex.exp (-Complex.I*y*T)) by fun_prop).mul hg).ite
    hm measurable_const

theorem sourceMaskedToy_core_bound {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (y p : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖sourceMaskedToy u y p N T‖ ≤ Real.exp (-(7/50 : ℝ)*T) := by
  unfold sourceMaskedToy
  split_ifs with h
  · have hL := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hlog : 2*Real.log 2 ≤ (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hlen : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N :=
      hL.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
    have hgap : (7/25 : ℝ)*T < ((1-p)*T)-(SquarefreeVaughanLogSource.length u N-p*T) := by
      nlinarith [h.1, Nat.cast_nonneg (α := ℝ) N]
    rw [norm_mul, Complex.norm_exp]
    have hphase : (-Complex.I*(y : ℂ)*(T : ℂ)).re = 0 := by simp
    rw [hphase, Real.exp_zero, one_mul]
    exact sourceKernel_core_bound hu (mul_nonneg (by linarith [h.2.2.2.1]) hT.le)
      h.2.2.2.2 (by nlinarith) hT.le hgap.le
  · simp only [norm_zero]
    exact (Real.exp_pos _).le

theorem integrable_sourceMaskedToy {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (y p : ℝ) :
    IntegrableOn (fun T : ℝ =>
      ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*sourceMaskedToy u y p N T) (Ioi 0) := by
  apply ((radial_integrable N (by norm_num : (0 : ℝ) < 1/2+7/50)).div_const
    (N.factorial : ℝ)).mono'
  · apply AEStronglyMeasurable.mul
    · exact (show Continuous (fun T : ℝ =>
        ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)) by fun_prop).aestronglyMeasurable
    · exact (measurable_sourceMaskedToy u y p N).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hTp : 0 < T := hT
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (Real.exp (-T/2)*T^N/(N.factorial : ℝ))*Real.exp (-(7/50 : ℝ)*T) :=
        mul_le_mul_of_nonneg_left (sourceMaskedToy_core_bound hu hN y p hTp) (by positivity)
      _ = _ := by
        have he : Real.exp (-T/2)*Real.exp (-(7/50 : ℝ)*T) =
            Real.exp (-(1/2+7/50 : ℝ)*T) := by
          rw [← Real.exp_add]; congr 1; ring
        linear_combination (T^N/(N.factorial : ℝ))*he

/-- Quantitative decay for the exact source-matched regression, with every
stated radial/share mask and the fixed-height phase retained. -/
theorem sourceMaskedToy_radial_decay {u : ℝ} (hu : 1/2 ≤ u)
    (hu1 : u ≤ 10001/20000) {N : ℕ} (hN : 2 ≤ N) (y p : ℝ) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*
        sourceMaskedToy u y p N T)‖ ≤ (4/5 : ℝ)^(N+1) := by
  refine (radial_bound N (by linarith) (by norm_num : (0 : ℝ) < 1/2+7/50)
    (fun _ hT => sourceMaskedToy_core_bound hu hN y p hT)).trans ?_
  apply pow_le_pow_left₀ (by positivity)
  norm_num
  linarith

theorem sourceMaskedToy_radial_small {u : ℝ} (hu : 1/2 ≤ u)
    (hu1 : u ≤ 10001/20000) {N : ℕ} (hN : 32 ≤ N) (y p : ℝ) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*
        sourceMaskedToy u y p N T)‖ < 1/1000 := by
  refine lt_of_le_of_lt ((sourceMaskedToy_radial_decay hu hu1 (by omega) y p).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num : (4/5 : ℝ) ≤ 1)
      (show 33 ≤ N+1 by omega))) ?_
  norm_num

/-- The below-diagonal kernel for one analytic mode at displacement b from
the selected source. Complex directions are retained. -/
def displacedKernel (u : ℝ) (b : ℂ) (s d : ℝ) : ℂ :=
  Complex.exp ((sourceShift u*s : ℝ) : ℂ)*
    (Complex.exp (-b*((s-d : ℝ) : ℂ))-Complex.exp (-b*s))

theorem sourceKernel_eq_displaced {u s d : ℝ} (hu : 0 < u) (hd : d < s) :
    sourceKernel u s d = displacedKernel u (u : ℂ) s d := by
  rw [sourceKernel, leakageKernel_below (mul_lt_mul_of_pos_left hd hu)]
  have he : Complex.exp (-((u*s : ℝ) : ℂ))*Complex.exp ((u*d : ℝ) : ℂ) =
      Complex.exp (-(u : ℂ)*((s-d : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  unfold displacedKernel
  push_cast at he ⊢
  simp only [neg_mul] at he ⊢
  linear_combination Complex.exp ((sourceShift u : ℂ)*s)*he

/-- This is the directional estimate that a mere analytic disk does not
give. It applies before radial integration and keeps the joint kernel. -/
theorem displacedKernel_bound {u s d : ℝ} (b : ℂ) (hu : 1/2 ≤ u)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hb : 0 ≤ b.re) :
    ‖displacedKernel u b s d‖ ≤ 2*Real.exp (-b.re*(s-d)) := by
  rw [displacedKernel, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  have he : Real.exp (sourceShift u*s) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by dsimp [sourceShift]; linarith) hs
  calc
    _ ≤ ‖Complex.exp (-b*((s-d : ℝ) : ℂ))-Complex.exp (-b*s)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)
    _ ≤ ‖Complex.exp (-b*((s-d : ℝ) : ℂ))‖+‖Complex.exp (-b*s)‖ := norm_sub_le _ _
    _ = Real.exp (-b.re*(s-d))+Real.exp (-b.re*s) := by
      simp [Complex.norm_exp]
    _ ≤ _ := by
      have h := Real.exp_le_exp.mpr (show -b.re*s ≤ -b.re*(s-d) by nlinarith)
      linarith

/-- A tiny positive horizontal displacement already beats the restricted
source growth; the imaginary part need not be bounded. -/
theorem displacedKernel_core_bound {u s d T : ℝ} (b : ℂ) (hu : 1/2 ≤ u)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hT : 0 ≤ T) (hb : 1/1000 ≤ b.re)
    (hgap : (7/25 : ℝ)*T ≤ s-d) :
    ‖displacedKernel u b s d‖ ≤ 2*Real.exp (-(7/25000 : ℝ)*T) := by
  refine (displacedKernel_bound b hu hs hd (by linarith)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A reusable numerical threshold for any exact joint inverse kernel.
No claim that the actual zeta remainder satisfies the premise is made. -/
theorem directional_radial_bound (N : ℕ) {u M : ℝ} (hu : 0 ≤ u)
    (hu1 : u ≤ 10001/20000) (hM : 0 < M) {f : ℝ → ℂ}
    (hf : ∀ T > 0, ‖f T‖ ≤ M*Real.exp (-(7/25000 : ℝ)*T)) :
    ‖((u^(N+1) : ℝ) : ℂ)*
      (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*f T)‖ ≤
      M*(9999/10000 : ℝ)^(N+1) := by
  have h := radial_bound N hu (by norm_num : (0 : ℝ) < 1/2+7/25000)
    (f := fun T => f T/(M : ℂ)) (by
      intro T hT
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le]
      exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm] using hf T hT))
  have hi :
      ((u^(N+1) : ℝ) : ℂ)*
        (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*
          (f T/(M : ℂ))) =
      (((u^(N+1) : ℝ) : ℂ)*
        (∫ T : ℝ in Ioi 0, ((Real.exp (-T/2)*T^N/(N.factorial : ℝ) : ℝ) : ℂ)*f T))/(M : ℂ) := by
    simp only [← mul_div_assoc, integral_div]
  rw [hi, norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le] at h
  have h' := (div_le_iff₀ hM).mp h
  have hr : (u/(1/2+7/25000))^(N+1) ≤ (9999/10000 : ℝ)^(N+1) := by
    apply pow_le_pow_left₀ (by positivity)
    norm_num
    linarith
  simpa only [mul_comm] using h'.trans (mul_le_mul_of_nonneg_right hr hM.le)

/-- Physical mode of an actual zero in the shifted-center correction.
The radial Laplace coordinate has center 1/2. -/
def shiftedMode (y : ℝ) (tau : ℂ) : ℂ :=
  1/2-(ZetaRieszShiftedCenter.center y+1-tau)/ZetaRieszShiftedCenter.ratio y

theorem shiftedMode_eq (y : ℝ) (tau : ℂ) :
    shiftedMode y tau = (tau-1)*ZetaRieszShiftedCenter.pole y/
      ZetaRieszShiftedCenter.center y-Complex.I*y := by
  have hc := ZetaRieszShiftedCenter.center_ne_zero y
  have hp := ZetaRieszShiftedCenter.pole_ne_zero y
  unfold shiftedMode ZetaRieszShiftedCenter.ratio
  field_simp
  unfold ZetaRieszShiftedCenter.pole ZetaRieszShiftedCenter.center
  ring

/-- The reflected ordinate here is the genuine conjugate zero, not a
canonical reflected auxiliary mode. -/
theorem shiftedMode_conjugate_re (rho : NontrivialZetaZero) :
    (shiftedMode rho.1.im (NontrivialZetaZero.conjugate rho).1).re =
      ((rho.1.re-1)*(rho.1.im^2+3/4)+rho.1.im^2)/(rho.1.im^2+9/4) := by
  rw [shiftedMode_eq]
  simp only [NontrivialZetaZero.conjugate_coe, Complex.sub_re,
    Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.one_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num [ZetaRieszShiftedCenter.pole, ZetaRieszShiftedCenter.center,
    Complex.normSq_apply]
  ring

/-- An actual shifted conjugate mode lies in the adverse horizontal
half-plane, although its Taylor pole is far outside the local disk. -/
theorem shiftedMode_conjugate_re_gt (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    99/100 < (shiftedMode rho.1.im (NontrivialZetaZero.conjugate rho).1).re := by
  rw [shiftedMode_conjugate_re]
  have hy := ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho
  have hy2 : 54^2 < rho.1.im^2 := by nlinarith [sq_abs rho.1.im]
  apply (lt_div_iff₀ (by positivity : 0 < rho.1.im^2+9/4)).mpr
  have hprod := mul_nonneg
    (show 0 ≤ rho.1.re-19999/20000 by linarith)
    (show 0 ≤ rho.1.im^2+3/4 by positivity)
  nlinarith

/-- The normalized Taylor location of a zero in the shifted-center term. -/
def shiftedPole (u y : ℝ) (tau : ℂ) : ℂ :=
  (ZetaRieszShiftedCenter.center y+1-tau)/((u : ℂ)*ZetaRieszShiftedCenter.ratio y)

theorem shiftedPole_substitution {u : ℝ} (hu : u ≠ 0) (y : ℝ) (tau : ℂ) :
    ZetaRieszShiftedCenter.center y+1-(u : ℂ)*ZetaRieszShiftedCenter.ratio y*
      shiftedPole u y tau = tau := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [shiftedPole, mul_div_cancel₀ _
    (mul_ne_zero huC (ZetaRieszShiftedCenter.ratio_ne_zero y))]
  ring

/-- This genuine adverse mode does not contradict the existing analytic
radius-two theorem for the complete shifted leg. -/
theorem shiftedPole_conjugate_outside (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    2 < ‖shiftedPole (3/2-rho.1.re) rho.1.im (NontrivialZetaZero.conjugate rho).1‖ := by
  by_contra! ht
  have hp := ZetaRieszLocalXiDivisor.source_pos rho
  have hh := ZetaRieszShiftedCenter.shifted_re_gt_one hp.le hu
    (ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho) ht
  rw [shiftedPole_substitution hp.ne'] at hh
  linarith [NontrivialZetaZero.re_lt_one (NontrivialZetaZero.conjugate rho)]

theorem shiftedPole_original {u : ℝ} (hu : u ≠ 0) (y : ℝ) (tau : ℂ) :
    ZetaRieszShiftedCenter.center y-(u : ℂ)*shiftedPole u y tau =
      1+Complex.I*y+shiftedMode y tau := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hr := ZetaRieszShiftedCenter.ratio_ne_zero y
  unfold shiftedPole shiftedMode
  field_simp
  unfold ZetaRieszShiftedCenter.center
  ring

/-- The original center is in Re>1 at this shifted pole, so it is not
another nontrivial zero or the zeta pole that could cancel this channel. -/
theorem shiftedPole_original_re_gt (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    199/100 < (ZetaRieszShiftedCenter.center rho.1.im-
      ((3/2-rho.1.re : ℝ) : ℂ)*shiftedPole (3/2-rho.1.re) rho.1.im
        (NontrivialZetaZero.conjugate rho).1).re := by
  have hp := ZetaRieszLocalXiDivisor.source_pos rho
  rw [shiftedPole_original hp.ne']
  have h := shiftedMode_conjugate_re_gt rho hrho hu
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  linarith

/-- The displacement needed by the directional model theorem has the
opposite sign for the actual conjugate shifted channel. -/
theorem shifted_conjugate_displacement_neg (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hu : 3/2-rho.1.re ≤ 10001/20000) :
    sourceShift (3/2-rho.1.re)-
      (shiftedMode rho.1.im (NontrivialZetaZero.conjugate rho).1).re < -99/100 := by
  have h := shiftedMode_conjugate_re_gt rho hrho hu
  have hr := NontrivialZetaZero.re_lt_one rho
  change 1/2-(3/2-rho.1.re)-
    (shiftedMode rho.1.im (NontrivialZetaZero.conjugate rho).1).re < -99/100
  linarith

/-- Exact radial frequency cancellation in the real-contraction stress
model. Both auxiliary positive heights exceed the selected height. -/
theorem contraction_model_phase_exact (y : ℝ) :
    (2*((119/40)*y)-y)-(11/20)*(10*y-y) = 0 := by ring

/-- The real saddle rate includes the selected largest-prime leg. -/
theorem contraction_model_rate :
    (1/2 : ℝ)-(19999/20000-1)*(11/20)-2*(99999/100000-1)+
      (11/20)*(99999/100000-1) = 250021/500000 := by norm_num

/-- The resonant model exponent is genuinely positive. This does not
assert growth of the complete literal prime packet. -/
theorem contraction_model_exponent_pos :
    (1/40000 : ℝ) < Real.log (10001/20000)-Real.log (250021/500000)-
      (1/50000)*Real.log (10001/20000) := by
  have hrat := Real.log_le_sub_one_of_pos
    (by norm_num : (0 : ℝ) < (250021/500000)/(10001/20000))
  rw [Real.log_div (by norm_num : (250021/500000 : ℝ) ≠ 0)
    (by norm_num : (10001/20000 : ℝ) ≠ 0)] at hrat
  have hsmall := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10001/10000)
  have he : Real.log (10001/20000 : ℝ) = Real.log (10001/10000)-Real.log 2 := by
    rw [← Real.log_div (by norm_num : (10001/10000 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hlog : Real.log (10001/20000 : ℝ) < -(13/20 : ℝ) := by
    rw [he]
    linarith [Real.log_two_gt_d9]
  norm_num at hrat
  linarith

end
end RiemannGaussian.ZetaRieszCausalSurface
