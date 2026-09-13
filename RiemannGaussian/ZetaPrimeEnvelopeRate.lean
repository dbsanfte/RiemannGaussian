/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeWindowLocalization
import RiemannGaussian.ZetaMoebiusFractionalBudgetAudit
import RiemannGaussian.ZetaPrimeBandAbel

/-!
# Subexponential error envelopes at the actual prime-source scale

Every continuous positive envelope which decays more slowly than each
exponential leaves a divergent absolute moment allowance for every fixed
filter normalized at the source coordinate. A single logarithmic interval
of length one already proves this. This is a theorem about an allowance,
not a lower bound for the actual signed Chebyshev error or prime tail.
-/

namespace RiemannGaussian.PrimeEnvelopeRate
noncomputable section
open Complex Filter Topology MeasureTheory

/-- The local absolute allowance after a Chebyshev error envelope
`x*g(log x)` is inserted in logarithmic coordinates. -/
def windowAllowance (p : Polynomial ℂ) (g : ℝ → ℝ) (u : ℝ) (N : ℕ) : ℝ :=
  u ^ (N + 1) * ∫ t in u⁻¹ * N..u⁻¹ * N + 1,
    g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖

/-- The full factorial polynomial is continuous in its real coordinate. -/
theorem continuous_factorialPolynomial (p : Polynomial ℂ) (N : ℕ) :
    Continuous (fun t : ℝ ↦ zetaFactorialPolynomial p N (t : ℂ)) := by
  unfold zetaFactorialPolynomial Polynomial.sum
  fun_prop

/-- These local allowances are genuine finite integrals for every
continuous envelope and fixed complex filter. -/
theorem integrable_window (p : Polynomial ℂ) (N : ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦
      g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖) volume a b :=
  ((hg.mul (by fun_prop)).mul (continuous_factorialPolynomial p N).norm).intervalIntegrable _ _

/-- Uniform localization prevents a normalized filter from removing
the absolute mass on the selected logarithmic interval. -/
theorem eventually_factorial_lower (p : Polynomial ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hp : p.eval (c : ℂ) = 1) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, c * N ≤ t → t ≤ c * N + 1 →
      (1 / 2 : ℝ) * ((c * N) ^ N / (N.factorial : ℝ)) ≤
        ‖zetaFactorialPolynomial p N (t : ℂ)‖ := by
  filter_upwards [eventually_zetaFactorialLocalAmplitude_near_one p hc hp 1
    (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
  intro t ht htu
  have ha := (hN t ht htu).le
  have hn : (1 / 2 : ℝ) ≤ ‖zetaFactorialLocalAmplitude p N t‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (zetaFactorialLocalAmplitude p N t)
    rw [norm_one, norm_sub_rev] at h
    linarith
  have ht0 : 0 ≤ t := (mul_nonneg hc (Nat.cast_nonneg N)).trans ht
  rw [zetaFactorialPolynomial_eq_localAmplitude, norm_mul, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, Complex.norm_natCast]
  have hm := mul_le_mul
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht N)
      (by positivity : 0 ≤ (N.factorial : ℝ)))
    hn (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)
  linarith

/-- A uniform exponential lower envelope gives a concrete lower bound
for the complete local absolute allowance, with the original filter. -/
theorem eventually_windowAllowance_lower (p : Polynomial ℂ) {u ε : ℝ}
    (hu : 0 < u) (hε : 0 < ε) {g : ℝ → ℝ} (hg : Continuous g)
    (hlower : ∀ᶠ t : ℝ in atTop, Real.exp (-ε * t) ≤ g t)
    (hp : p.eval (u : ℂ)⁻¹ = 1) :
    ∀ᶠ N : ℕ in atTop,
      (u * Real.exp (-ε - 1 / 2) / 12) *
        ((u * PrimeWindow.localGrowth u⁻¹ * Real.exp (-ε * u⁻¹)) ^ N / (N : ℝ)) ≤
          windowAllowance p g u N := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hlower
  have hcoord : Tendsto (fun N : ℕ ↦ u⁻¹ * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr hu)
  filter_upwards [hcoord.eventually_ge_atTop T, eventually_ge_atTop (1 : ℕ),
    eventually_factorial_lower p (inv_nonneg.mpr hu.le)
      (by simpa only [Complex.ofReal_inv] using hp)] with N hNT hN hpN
  have hbase : 0 ≤ (1 / 2 : ℝ) * ((u⁻¹ * N) ^ N / (N.factorial : ℝ)) := by positivity
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (u⁻¹ * N) (u⁻¹ * N + 1)) :
      Real.exp (-ε * (u⁻¹ * N + 1)) * Real.exp (-(u⁻¹ * N + 1) / 2) *
        ((1 / 2 : ℝ) * ((u⁻¹ * N) ^ N / (N.factorial : ℝ))) ≤
      g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖ := by
    have he := (Real.exp_le_exp.mpr (by nlinarith [ht.2] :
      -ε * (u⁻¹ * N + 1) ≤ -ε * t)).trans (hT t (hNT.trans ht.1))
    have he' : Real.exp (-(u⁻¹ * N + 1) / 2) ≤ Real.exp (-t / 2) :=
      Real.exp_le_exp.mpr (by linarith [ht.2])
    have hge : 0 ≤ g t := (Real.exp_pos _).le.trans he
    exact mul_le_mul (mul_le_mul he he' (Real.exp_pos _).le hge)
      (hpN t ht.1 ht.2) hbase (by positivity)
  have hi := intervalIntegral.integral_mono_on (show u⁻¹ * (N : ℝ) ≤ u⁻¹ * N + 1 by linarith)
    intervalIntegrable_const (integrable_window p N hg _ _) hpoint
  simp only [intervalIntegral.integral_const, add_sub_cancel_left, one_smul] at hi
  have hs := PrimeWindow.local_monomial_lower hN (inv_nonneg.mpr hu.le)
  have hmult := mul_le_mul_of_nonneg_left hi (pow_nonneg hu.le (N + 1))
  have hs' := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ u ^ (N + 1) * Real.exp (-ε * (u⁻¹ * N + 1) - 1 / 2) / 2 by positivity)
  apply le_trans (le_of_eq ?_) (hs'.trans ?_)
  · have hex : Real.exp (-ε * (u⁻¹ * N + 1) - 1 / 2) =
        Real.exp (-ε - 1 / 2) * Real.exp ((N : ℝ) * (-ε * u⁻¹)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [pow_succ, mul_pow, mul_pow, ← Real.exp_nat_mul, hex]
    ring
  · apply le_trans (le_of_eq ?_) hmult
    have hex : Real.exp (-ε * (u⁻¹ * N + 1) - 1 / 2) * Real.exp (-(u⁻¹ * N) / 2) =
        Real.exp (-ε * (u⁻¹ * N + 1)) * Real.exp (-(u⁻¹ * N + 1) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (u ^ (N + 1) * ((u⁻¹ * N) ^ N / (N.factorial : ℝ)) / 2) *
          (Real.exp (-ε * (u⁻¹ * N + 1) - 1 / 2) * Real.exp (-(u⁻¹ * N) / 2)) := by ring
      _ = _ := by rw [hex]; ring

/-- Every allowance with a subexponential positive lower envelope
diverges at source scale, for every fixed normalized complex filter. -/
theorem windowAllowance_tendsto_atTop (p : Polynomial ℂ) {u : ℝ} (hu : 1 / 2 < u)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hslow : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop, Real.exp (-ε * t) ≤ g t)
    (hp : p.eval (u : ℂ)⁻¹ = 1) :
    Tendsto (windowAllowance p g u) atTop atTop := by
  have hu0 : 0 < u := by linarith
  let ε : ℝ := (u - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let r : ℝ := u * PrimeWindow.localGrowth u⁻¹ * Real.exp (-ε * u⁻¹)
  have hr : 1 < r := by
    dsimp [r]
    rw [PrimeWindow.source_localGrowth hu0, ← Real.exp_add, Real.one_lt_exp_iff]
    have hi : u⁻¹ < 2 := by
      rw [inv_eq_one_div, div_lt_iff₀ hu0]
      linarith
    have hm := mul_inv_cancel₀ hu0.ne'
    dsimp [ε]
    nlinarith
  have ht : Tendsto (fun N : ℕ ↦ r ^ N / (N : ℝ)) atTop atTop := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 (Real.log r) (Real.log_pos hr)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply h.congr'
    filter_upwards [] with N
    simp only [Function.comp_apply, Real.rpow_one, mul_comm (Real.log r),
      Real.exp_nat_mul, Real.exp_log (by linarith : 0 < r)]
  exact tendsto_atTop_mono' atTop
    (eventually_windowAllowance_lower p hu0 hε hg (hslow ε hε) hp)
    (ht.const_mul_atTop (by positivity : 0 < u * Real.exp (-ε - 1 / 2) / 12))

/-- Any sublinear logarithmic saving stays above every exponential
lower envelope eventually, without choosing a particular rate family. -/
theorem exp_lower_of_sublinear {r : ℝ → ℝ}
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-ε * t) ≤ Real.exp (-r t) := by
  filter_upwards [hr.eventually_lt_const hε, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  apply Real.exp_le_exp.mpr
  have h := (div_lt_iff₀ ht0).mp ht
  linarith

/-- In particular, every continuous sublinear exponent `r(t)=o(t)`
leaves a divergent absolute allowance. This includes error-envelope
strategies, not an assertion that the signed arithmetic error is large. -/
theorem sublinear_exponent_allowance_tendsto (p : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 < u) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0))
    (hp : p.eval (u : ℂ)⁻¹ = 1) :
    Tendsto (windowAllowance p (fun t ↦ Real.exp (-r t)) u) atTop atTop :=
  windowAllowance_tendsto_atTop p hu (Real.continuous_exp.comp hc.neg)
    (fun _ hε ↦ exp_lower_of_sublinear hr hε) hp

/-- The witness interval lies inside the original retained prime band
at every positive order. No new arithmetic cutoff is substituted. -/
theorem window_inside_original_band {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    Real.log (zetaPrimeBandLower N) ≤ u⁻¹ * N ∧
      u⁻¹ * N + 1 ≤ Real.log (zetaPrimeBandUpper N) := by
  have hu0 : 0 < u := by linarith
  have hi : 1 ≤ u⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ hu0]; linarith
  have hi' : u⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ hu0]; linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow := mul_le_mul_of_nonneg_right hi hn0
  have hupp := mul_le_mul_of_nonneg_right hi' hn0
  have hloglo := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) hn0
  have hloghi := mul_le_mul_of_nonneg_left
    (show Real.log 2 ≤ (1 : ℝ) by linarith [Real.log_two_lt_d9]) hn0
  simp only [zetaPrimeBandLower, Real.log_exp, zetaPrimeBandUpper, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]
  constructor <;> nlinarith

/-- The absolute allowance over the full original prime band, for the
same fixed complex filter and source normalization. -/
def bandAllowance (p : Polynomial ℂ) (g : ℝ → ℝ) (u : ℝ) (N : ℕ) : ℝ :=
  u ^ (N + 1) * ∫ t in Real.log (zetaPrimeBandLower N)..Real.log (zetaPrimeBandUpper N),
    g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖

/-- The complete absolute allowance contains the witness interval's
mass. This is a comparison of genuine integrals, not of totalized expressions. -/
theorem windowAllowance_le_bandAllowance (p : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 < u) (hu1 : u < 1) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t : ℝ, 0 ≤ g t) {N : ℕ} (hN : 1 ≤ N) :
    windowAllowance p g u N ≤ bandAllowance p g u N := by
  obtain ⟨ha, hb⟩ := window_inside_original_band hu hu1 hN
  have hu0 : 0 < u := by linarith
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu0.le _)
  apply intervalIntegral.integral_mono_interval ha (by linarith) hb
    (Filter.Eventually.of_forall fun t ↦ by have hgt := hg0 t; positivity)
    (integrable_window p N hg _ _)

/-- Every fixed normalized filter has a divergent full-band absolute
allowance under every continuous sublinear exponent. -/
theorem bandAllowance_sublinear_tendsto (p : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 < u) (hu1 : u < 1) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0))
    (hp : p.eval (u : ℂ)⁻¹ = 1) :
    Tendsto (bandAllowance p (fun t ↦ Real.exp (-r t)) u) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (sublinear_exponent_allowance_tendsto p hu hc hr hp)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact windowAllowance_le_bandAllowance p hu hu1 (Real.continuous_exp.comp hc.neg)
    (fun t ↦ (Real.exp_pos _).le) hN

/-- The original pole-jet filter satisfies the normalization premise,
so sublinear exponent envelopes fail at every hypothetical right-half zero.
This does not assert a lower bound for the actual signed prime tail. -/
theorem actual_bandAllowance_sublinear_tendsto (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0)) :
    Tendsto (bandAllowance (zetaRightHalfPoleJetFilter ρ hρ)
      (fun t ↦ Real.exp (-r t)) (3 / 2 - ρ.1.re)) atTop atTop :=
  bandAllowance_sublinear_tendsto _ (by linarith [ρ.re_lt_one]) (by linarith) hc hr
    (zetaRightHalfPoleJetFilter_eval_selected ρ hρ)

/-- Scalar multiplication of the original filter scales the complete
absolute allowance by exactly the scalar's norm. -/
theorem bandAllowance_C_mul (p : Polynomial ℂ) (c : ℂ) (g : ℝ → ℝ) (u : ℝ) (N : ℕ) :
    bandAllowance (Polynomial.C c * p) g u N = ‖c‖ * bandAllowance p g u N := by
  unfold bandAllowance
  simp_rw [zetaFactorialPolynomial_C_mul, norm_mul]
  have he (t : ℝ) : g t * Real.exp (-t / 2) * (‖c‖ * ‖zetaFactorialPolynomial p N (t : ℂ)‖) =
      ‖c‖ * (g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Nonzero source evaluation suffices: normalization is not a
restriction on the class of fixed filters with this obstruction. -/
theorem bandAllowance_sublinear_tendsto_of_eval_ne_zero (p : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 < u) (hu1 : u < 1) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0))
    (hp : p.eval (u : ℂ)⁻¹ ≠ 0) :
    Tendsto (bandAllowance p (fun t ↦ Real.exp (-r t)) u) atTop atTop := by
  let q := Polynomial.C (p.eval (u : ℂ)⁻¹)⁻¹ * p
  have hq : q.eval (u : ℂ)⁻¹ = 1 := by simp [q, hp]
  have h := (bandAllowance_sublinear_tendsto q hu hu1 hc hr hq).const_mul_atTop
    (norm_pos_iff.mpr hp)
  apply h.congr'
  filter_upwards [] with N
  dsimp only [q]
  rw [bandAllowance_C_mul, norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_mul]

/-- The same exact scalar transport holds on the witness interval. -/
theorem windowAllowance_C_mul (p : Polynomial ℂ) (c : ℂ) (g : ℝ → ℝ) (u : ℝ) (N : ℕ) :
    windowAllowance (Polynomial.C c * p) g u N = ‖c‖ * windowAllowance p g u N := by
  unfold windowAllowance
  simp_rw [zetaFactorialPolynomial_C_mul, norm_mul]
  have he (t : ℝ) : g t * Real.exp (-t / 2) * (‖c‖ * ‖zetaFactorialPolynomial p N (t : ℂ)‖) =
      ‖c‖ * (g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial p N (t : ℂ)‖) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Nonzero source evaluation already forces a divergent local
allowance under every continuous sublinear exponent. -/
theorem windowAllowance_sublinear_tendsto_of_eval_ne_zero (p : Polynomial ℂ) {u : ℝ}
    (hu : 1 / 2 < u) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0))
    (hp : p.eval (u : ℂ)⁻¹ ≠ 0) :
    Tendsto (windowAllowance p (fun t ↦ Real.exp (-r t)) u) atTop atTop := by
  let q := Polynomial.C (p.eval (u : ℂ)⁻¹)⁻¹ * p
  have hq : q.eval (u : ℂ)⁻¹ = 1 := by simp [q, hp]
  have h := (sublinear_exponent_allowance_tendsto q hu hc hr hq).const_mul_atTop
    (norm_pos_iff.mpr hp)
  apply h.congr'
  filter_upwards [] with N
  dsimp only [q]
  rw [windowAllowance_C_mul, norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_mul]

/-- The full derivative combination is a single fixed polynomial
filter. Its two complex terms are retained together before any norm. -/
def derivativeFilter (p : Polynomial ℂ) (s : ℂ) : Polynomial ℂ :=
  p - Polynomial.C s * (Polynomial.X * p)

/-- Exact consecutive-moment identity for the full complex derivative
polynomial; no triangle inequality separates its two terms. -/
theorem derivativeFilter_polynomial (p : Polynomial ℂ) (s : ℂ) (N : ℕ) (t : ℂ) :
    zetaFactorialPolynomial (derivativeFilter p s) N t =
      zetaFactorialPolynomial p N t - s * zetaFactorialPolynomial p (N + 1) t := by
  simp only [derivativeFilter, zetaFactorialPolynomial_sub, zetaFactorialPolynomial_C_mul,
    zetaFactorialPolynomial_X_mul]

/-- The derivative of the literal original prime kernel carries this
same complete filter, with its exact real-variable Jacobian. -/
theorem derivativeFilter_kernel (p : Polynomial ℂ) (s : ℂ) (N : ℕ) {x : ℝ}
    (hx : 0 < x) :
    deriv (zetaPrimeFilterKernel p (N + 1) s) x =
      zetaPrimeFilterKernel (derivativeFilter p s) N s x / (x : ℂ) := by
  rw [deriv_zetaPrimeFilterKernel p N s hx]
  simp only [zetaPrimeFilterKernel, derivativeFilter_polynomial]
  ring

/-- The Chebyshev envelope factor `x` and the logarithmic substitution
Jacobian `dx=exp(t)dt` produce exactly this half-damped derivative norm.
The complex difference is not split into separate estimates. -/
theorem derivative_norm_log_coordinate (p : Polynomial ℂ) (N : ℕ) (y t : ℝ) :
    Real.exp (2 * t) * ‖deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y)) (Real.exp t)‖ =
      Real.exp (-t / 2) *
        ‖zetaFactorialPolynomial p N (t : ℂ) -
          (3 / 2 + I * y) * zetaFactorialPolynomial p (N + 1) (t : ℂ)‖ := by
  rw [derivativeFilter_kernel p _ N (Real.exp_pos t)]
  simp only [norm_div, zetaPrimeFilterKernel, norm_mul, Real.log_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), derivativeFilter_polynomial]
  have hn : ‖Complex.exp (-(3 / 2 + I * (y : ℂ)) * (t : ℂ))‖ =
      Real.exp (-(3 / 2 : ℝ) * t) := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [hn]
  have he : Real.exp (2 * t) * Real.exp (-(3 / 2 : ℝ) * t) / Real.exp t =
      Real.exp (-t / 2) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  calc
    _ = (Real.exp (2 * t) * Real.exp (-(3 / 2 : ℝ) * t) / Real.exp t) *
        ‖zetaFactorialPolynomial p N (t : ℂ) -
          (3 / 2 + I * y) * zetaFactorialPolynomial p (N + 1) (t : ℂ)‖ := by ring
    _ = _ := by rw [he]

/-- At a selected zero the full derivative has nonzero source
evaluation. Preserving its internal cancellation therefore does not remove
the obstruction for an absolute error envelope. -/
theorem derivativeFilter_eval_selected (ρ : NontrivialZetaZero) (hρ : 1 / 2 < ρ.1.re) :
    (derivativeFilter (zetaRightHalfPoleJetFilter ρ hρ) (3 / 2 + I * ρ.1.im)).eval
      (((3 / 2 - ρ.1.re : ℝ) : ℂ)⁻¹) ≠ 0 := by
  rw [derivativeFilter, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    zetaRightHalfPoleJetFilter_eval_selected ρ hρ]
  simp only [mul_one]
  have hu : (((3 / 2 - ρ.1.re : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show 3 / 2 - ρ.1.re ≠ 0 by linarith [ρ.re_lt_one])
  intro he
  have hmul := congrArg (fun z : ℂ ↦ z * (((3 / 2 - ρ.1.re : ℝ) : ℂ))) he
  simp only [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one, zero_mul] at hmul
  have hre := congrArg Complex.re hmul
  norm_num at hre
  linarith

/-- The obstruction survives the complete complex derivative, for the
actual pole-jet filter and every continuous sublinear exponent. -/
theorem actual_derivative_allowance_sublinear_tendsto (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0)) :
    Tendsto (bandAllowance
      (derivativeFilter (zetaRightHalfPoleJetFilter ρ hρ) (3 / 2 + I * ρ.1.im))
      (fun t ↦ Real.exp (-r t)) (3 / 2 - ρ.1.re)) atTop atTop :=
  bandAllowance_sublinear_tendsto_of_eval_ne_zero _
    (by linarith [ρ.re_lt_one]) (by linarith) hc hr (derivativeFilter_eval_selected ρ hρ)

/-- The same witness remains inside the original band at the successor
moment order used by the derivative identity. -/
theorem window_inside_successor_band {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    {N : ℕ} (hN : 1 ≤ N) :
    Real.log (zetaPrimeBandLower (N + 1)) ≤ u⁻¹ * N ∧
      u⁻¹ * N + 1 ≤ Real.log (zetaPrimeBandUpper (N + 1)) := by
  have hu0 : 0 < u := by linarith
  have hi : 1 ≤ u⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ hu0]; linarith
  have hi' : u⁻¹ ≤ 2 := by rw [inv_eq_one_div, div_le_iff₀ hu0]; linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow := mul_le_mul_of_nonneg_right hi hn0
  have hupp := mul_le_mul_of_nonneg_right hi' hn0
  have hloglo := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (show 0 ≤ (N : ℝ) + 1 by positivity)
  have hloghi := mul_le_mul_of_nonneg_left
    (show Real.log 2 ≤ (1 : ℝ) by linarith [Real.log_two_lt_d9])
    (show 0 ≤ (N : ℝ) + 1 by positivity)
  simp only [zetaPrimeBandLower, Real.log_exp, zetaPrimeBandUpper, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

/-- The full derivative's absolute error allowance, at its original
successor moment and original successor band. Both complex terms remain
inside the same norm. -/
def derivativeBandAllowance (p : Polynomial ℂ) (g : ℝ → ℝ) (s : ℂ) (u : ℝ) (N : ℕ) : ℝ :=
  u ^ (N + 2) * ∫ t in Real.log (zetaPrimeBandLower (N + 1))..Real.log (zetaPrimeBandUpper (N + 1)),
    g t * Real.exp (-t / 2) *
      ‖zetaFactorialPolynomial p N (t : ℂ) - s * zetaFactorialPolynomial p (N + 1) (t : ℂ)‖

/-- The witness interval survives in the actual derivative allowance
with exactly the extra source-normalization factor `u`. -/
theorem window_le_derivativeBandAllowance (p : Polynomial ℂ) (s : ℂ) {u : ℝ}
    (hu : 1 / 2 < u) (hu1 : u < 1) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t : ℝ, 0 ≤ g t) {N : ℕ} (hN : 1 ≤ N) :
    u * windowAllowance (derivativeFilter p s) g u N ≤ derivativeBandAllowance p g s u N := by
  obtain ⟨ha, hb⟩ := window_inside_successor_band hu hu1 hN
  have hu0 : 0 < u := by linarith
  have hi := intervalIntegral.integral_mono_interval ha (show u⁻¹ * (N : ℝ) ≤ u⁻¹ * N + 1 by linarith) hb
    (f := fun t : ℝ ↦ g t * Real.exp (-t / 2) * ‖zetaFactorialPolynomial (derivativeFilter p s) N (t : ℂ)‖)
    (Filter.Eventually.of_forall fun t ↦ by have hgt := hg0 t; positivity)
    (integrable_window (derivativeFilter p s) N hg _ _)
  have hm := mul_le_mul_of_nonneg_left hi (pow_nonneg hu0.le (N + 2))
  unfold windowAllowance derivativeBandAllowance
  simp_rw [derivativeFilter_polynomial] at hm ⊢
  have he : u ^ (N + 2) = u * u ^ (N + 1) := by
    rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
    ring
  simpa only [he, mul_assoc] using hm

/-- The literal zero's full derivative error allowance diverges even
when its two complex terms are kept together. Both the source normalization
and the finite arithmetic band match the original successor moment. -/
theorem actual_full_derivative_allowance_tendsto (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0)) :
    Tendsto (derivativeBandAllowance (zetaRightHalfPoleJetFilter ρ hρ)
      (fun t ↦ Real.exp (-r t)) (3 / 2 + I * ρ.1.im) (3 / 2 - ρ.1.re)) atTop atTop := by
  have hu : 1 / 2 < 3 / 2 - ρ.1.re := by linarith [ρ.re_lt_one]
  have h := (windowAllowance_sublinear_tendsto_of_eval_ne_zero _ hu hc hr
    (derivativeFilter_eval_selected ρ hρ)).const_mul_atTop (by linarith : 0 < 3 / 2 - ρ.1.re)
  apply tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact window_le_derivativeBandAllowance _ _ hu (by linarith)
    (Real.continuous_exp.comp hc.neg) (fun _ ↦ (Real.exp_pos _).le) hN

private theorem continuousOn_original_envelope (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun x : ℝ ↦ x * g (Real.log x) *
      ‖deriv (zetaPrimeFilterKernel p N s) x‖) (Set.Ioi 0) := by
  have hd : ContDiffOn ℝ 2 (zetaPrimeFilterKernel p N s) (Set.Ioi 0) :=
    fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p N s hx).contDiffWithinAt
  have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
    fun _ hx ↦ (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  exact (continuousOn_id.mul (hg.comp_continuousOn hlog)).mul
    (hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).norm

/-- The original arithmetic-coordinate allowance is a genuine finite
integral on every positive compact interval. -/
theorem original_derivative_envelope_integrable (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ ↦ x * g (Real.log x) *
      ‖deriv (zetaPrimeFilterKernel p N s) x‖) volume a b :=
  ((continuousOn_original_envelope p N s hg).mono
    (fun _ hx ↦ (lt_min ha hb).trans_le hx.1)).intervalIntegrable

/-- Exact logarithmic substitution for the complete derivative envelope.
It retains both complex terms and proves the integral, including its
Jacobian and positive endpoints, in the original arithmetic coordinate. -/
theorem original_derivative_envelope_eq_log (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, x * g (Real.log x) *
      ‖deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y)) x‖) =
    ∫ t in Real.log a..Real.log b, g t * Real.exp (-t / 2) *
      ‖zetaFactorialPolynomial p N (t : ℂ) -
        (3 / 2 + I * y) * zetaFactorialPolynomial p (N + 1) (t : ℂ)‖ := by
  have hcont := (continuousOn_original_envelope p (N + 1) (3 / 2 + I * y) hg).mono
    (show Real.exp '' Set.uIcc (Real.log a) (Real.log b) ⊆ Set.Ioi 0 from by
      rintro _ ⟨t, _, rfl⟩
      exact Real.exp_pos t)
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log a) (b := Real.log b) (f := Real.exp) (f' := Real.exp)
    (fun t _ ↦ Real.hasDerivAt_exp t) Real.continuous_exp.continuousOn hcont
  rw [Real.exp_log ha, Real.exp_log hb] at hsubst
  rw [← hsubst]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Function.comp_apply, Real.log_exp]
  calc
    _ = g t * (Real.exp (2 * t) *
        ‖deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y)) (Real.exp t)‖) := by
      rw [show 2 * t = t + t by ring, Real.exp_add]
      ring
    _ = _ := by rw [derivative_norm_log_coordinate]; ring

/-- The allowance audited above is exactly the original derivative
integral at the original successor band and source normalization. -/
theorem derivativeBandAllowance_eq_original (p : Polynomial ℂ) {g : ℝ → ℝ}
    (hg : Continuous g) (u y : ℝ) (N : ℕ) :
    derivativeBandAllowance p g (3 / 2 + I * y) u N =
      u ^ (N + 2) * ∫ x in zetaPrimeBandLower (N + 1)..zetaPrimeBandUpper (N + 1),
        x * g (Real.log x) * ‖deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y)) x‖ := by
  rw [original_derivative_envelope_eq_log p N y hg (zetaPrimeBandLower_pos _)
    ((zetaPrimeBandLower_pos _).trans_le (zetaPrimeBandLower_le_upper _))]
  rfl

/-- The actual arithmetic-coordinate derivative allowance diverges for
every continuous sublinear exponent, with no omitted substitution or
integrability premise. This is still an allowance, not the signed error. -/
theorem actual_original_derivative_allowance_tendsto (ρ : NontrivialZetaZero)
    (hρ : 1 / 2 < ρ.1.re) {r : ℝ → ℝ} (hc : Continuous r)
    (hr : Tendsto (fun t : ℝ ↦ r t / t) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - ρ.1.re) ^ (N + 2) *
      ∫ x in zetaPrimeBandLower (N + 1)..zetaPrimeBandUpper (N + 1),
        x * Real.exp (-r (Real.log x)) *
          ‖deriv (zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter ρ hρ)
            (N + 1) (3 / 2 + I * ρ.1.im)) x‖) atTop atTop := by
  apply (actual_full_derivative_allowance_tendsto ρ hρ hc hr).congr'
  filter_upwards [] with N
  exact derivativeBandAllowance_eq_original _ (Real.continuous_exp.comp hc.neg) _ _ N

end
end RiemannGaussian.PrimeEnvelopeRate
