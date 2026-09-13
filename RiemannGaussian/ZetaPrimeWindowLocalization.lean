/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaFactorialFilterLocalization
import RiemannGaussian.ZetaPrimeWindow

/-!
# Large ordinary-prime windows for every normalized fixed filter

The original complex kernel is tested on logarithmic windows around `c*N`.
If the fixed polynomial has value one at `c`, uniform localization keeps a
positive rotated projection of the actual prime sum. The prime number
theorem and Stirling's bound give its exponential growth rate. This tests
raw window norms; it does not bound the centered error or the signed tail.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.PrimeWindow
noncomputable section

/-- The original filtered ordinary-prime moment on one logarithmic window. -/
def filteredMoment (p : Polynomial ℂ) (N : ℕ) (y h t : ℝ) : ℂ :=
  ∑ a ∈ primesInWindow (Real.exp t) (Real.exp h),
    (Real.log a : ℂ) * zetaPrimeFilterKernel p N (3 / 2 + I * y) a

/-- Rotation leaves the unfiltered kernel's exact nonnegative amplitude
unchanged. Its phase remains available in `rotated_kernel_one_re`. -/
theorem norm_rotated_kernel_one (N : ℕ) (y t : ℝ) {x : ℝ} (hx : 0 ≤ Real.log x) :
    ‖Complex.exp (I * y * t) * zetaPrimeFilterKernel 1 N (3 / 2 + I * y) x‖ =
      Real.log x ^ N / (N.factorial : ℝ) * Real.exp (-(3 / 2 : ℝ) * Real.log x) := by
  have hp : zetaFactorialPolynomial 1 N (Real.log x : ℂ) =
      (Real.log x : ℂ) ^ N / (N.factorial : ℂ) := by
    simpa only [Polynomial.monomial_zero_one, Nat.add_zero, one_mul] using
      zetaFactorialPolynomial_monomial 0 1 N (Real.log x : ℂ)
  simp [zetaPrimeFilterKernel, hp, norm_pow, Complex.norm_exp,
    Complex.mul_re, Real.norm_eq_abs, abs_of_nonneg hx]

private theorem quarter_projection {z w : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (hn : ‖z‖ = a) (hz : a / 2 ≤ z.re) (hw : ‖w - 1‖ ≤ 1 / 4) :
    a / 4 ≤ (z * w).re := by
  have hd : z - z * w = z * (1 - w) := by ring
  have he := Complex.re_le_norm (z - z * w)
  rw [Complex.sub_re, hd, norm_mul, hn, norm_sub_rev 1 w] at he
  nlinarith [mul_le_mul_of_nonneg_left hw ha]

/-- Uniform closeness of the full filter amplitude to one yields a
positive phase projection of each unchanged prime kernel in the window. -/
theorem filtered_kernel_projection_lower (p : Polynomial ℂ) (N : ℕ)
    {t h y x : ℝ} (ht : 0 ≤ t) (hx : t ≤ Real.log x) (hxu : Real.log x ≤ t + h)
    (hy : |y| * h ≤ 1)
    (hp : ‖zetaFactorialLocalAmplitude p N (Real.log x) - 1‖ ≤ 1 / 4) :
    (1 / 4 : ℝ) * (t ^ N / (N.factorial : ℝ)) * Real.exp (-(3 / 2 : ℝ) * (t + h)) ≤
      (Complex.exp (I * y * t) * zetaPrimeFilterKernel p N (3 / 2 + I * y) x).re := by
  have hlog : 0 ≤ Real.log x := ht.trans hx
  have hn := norm_rotated_kernel_one N y t hlog
  have hz : (Real.log x ^ N / (N.factorial : ℝ) *
      Real.exp (-(3 / 2 : ℝ) * Real.log x)) / 2 ≤
      (Complex.exp (I * y * t) * zetaPrimeFilterKernel 1 N (3 / 2 + I * y) x).re := by
    rw [rotated_kernel_one_re]
    have hc := mul_le_mul_of_nonneg_left (cos_phase_window_lower hx hxu hy)
      (show 0 ≤ Real.log x ^ N / (N.factorial : ℝ) *
        Real.exp (-(3 / 2 : ℝ) * Real.log x) by positivity)
    linarith
  have hq := quarter_projection (by positivity) hn hz hp
  rw [zetaPrimeFilterKernel_eq_one_mul_localAmplitude, ← mul_assoc]
  apply le_trans ?_ hq
  have hpow := div_le_div_of_nonneg_right (pow_le_pow_left₀ ht hx N)
    (show 0 ≤ (N.factorial : ℝ) by positivity)
  have he : Real.exp (-(3 / 2 : ℝ) * (t + h)) ≤
      Real.exp (-(3 / 2 : ℝ) * Real.log x) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul hpow he (Real.exp_pos _).le (by positivity)
  linarith

/-- The complete prime-window sum has a lower projection controlled by
its actual logarithmic prime mass. Every fixed normalized filter qualifies
eventually, with a common starting order for all primes in the window. -/
theorem eventually_filteredMoment_projection_lower (p : Polynomial ℂ)
    {c h y : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (hy : |y| * h ≤ 1)
    (hp : p.eval (c : ℂ) = 1) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) * ((c * N) ^ N / (N.factorial : ℝ)) *
        Real.exp (-(3 / 2 : ℝ) * (c * N + h)) *
          (Chebyshev.theta (Real.exp h * Real.exp (c * N)) - Chebyshev.theta (Real.exp (c * N))) ≤
        (Complex.exp (I * y * (c * N : ℝ)) * filteredMoment p N y h (c * N)).re := by
  filter_upwards [eventually_zetaFactorialLocalAmplitude_near_one p hc hp h
    (by norm_num : (0 : ℝ) < 1 / 4)] with N hN
  rw [← sum_log_primesInWindow (Real.exp_pos _).le (Real.one_le_exp_iff.mpr hh), filteredMoment]
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hm := mem_primesInWindow_bounds (Real.exp_pos _).le (Real.exp_pos h).le ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast hm.2.2.pos
  have hlog : c * N ≤ Real.log a := by
    simpa using Real.log_le_log (Real.exp_pos _) hm.1.le
  have hlogu : Real.log a ≤ c * N + h := by
    simpa [← Real.exp_add, add_comm] using Real.log_le_log ha0 hm.2.1
  have ht : 0 ≤ c * (N : ℝ) := mul_nonneg hc (Nat.cast_nonneg N)
  have hproj := filtered_kernel_projection_lower p N ht hlog hlogu hy (hN _ hlog hlogu).le
  rw [mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith [mul_le_mul_of_nonneg_left hproj (ht.trans hlog)]

/-- The exponential rate of a raw logarithmic window before the source
normalization. This retains its dependence on the chosen coordinate. -/
def localGrowth (c : ℝ) : ℝ := c * Real.exp (1 - c / 2)

/-- Stirling's inequality gives a lower bound for every nonnegative
linear logarithmic coordinate, with only one polynomial factor lost. -/
theorem local_monomial_lower {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    localGrowth c ^ N / (6 * N) ≤
      Real.exp (-(c * N) / 2) * (c * N) ^ N / (N.factorial : ℝ) := by
  have hex : Real.exp (-(c * N) / 2) = Real.exp (-c / 2) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he1 : Real.exp (1 - c / 2) = Real.exp 1 * Real.exp (-c / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : ((N : ℝ) / Real.exp 1) ^ N * localGrowth c ^ N =
      Real.exp (-(c * N) / 2) * (c * N) ^ N := by
    rw [hex, ← mul_pow, ← mul_pow]
    congr 1
    unfold localGrowth
    rw [he1]
    field_simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hN)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_right (factorial_le_six_mul_stirling hN)
    (show 0 ≤ localGrowth c ^ N by unfold localGrowth; positivity)
  calc
    _ = (N.factorial : ℝ) * localGrowth c ^ N := by ring
    _ ≤ (6 * N * ((N : ℝ) / Real.exp 1) ^ N) * localGrowth c ^ N := h
    _ = _ := by rw [mul_assoc (6 * (N : ℝ)), hid]; ring

/-- A positive window constant independent of the moment order and filter. -/
def localConstant (h : ℝ) : ℝ :=
  (Real.exp h - 1) / 8 * Real.exp (-(3 / 2 : ℝ) * h)

/-- Each positive fixed logarithmic width has a strictly positive allowance. -/
theorem localConstant_pos {h : ℝ} (hh : 0 < h) : 0 < localConstant h := by
  have := Real.one_lt_exp_iff.mpr hh
  unfold localConstant
  positivity

/-- Actual ordinary-prime windows attain the full local exponential rate
for every fixed polynomial normalized at their logarithmic coordinate. -/
theorem eventually_filteredMoment_growth_lower (p : Polynomial ℂ)
    {c h y : ℝ} (hc : 0 < c) (hh : 0 < h) (hy : |y| * h ≤ 1)
    (hp : p.eval (c : ℂ) = 1) :
    ∀ᶠ N : ℕ in atTop,
      localConstant h * (localGrowth c ^ N / (6 * N)) ≤
        (Complex.exp (I * y * (c * N : ℝ)) * filteredMoment p N y h (c * N)).re := by
  have hx : Tendsto (fun N : ℕ ↦ Real.exp (c * N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have hm := (theta_interval_div_tendsto (Real.exp_pos h)).comp hx
  have hdelta : 0 < Real.exp h - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hh)
  have hmass := hm.eventually_const_lt (show (Real.exp h - 1) / 2 < Real.exp h - 1 by linarith)
  filter_upwards [hmass, eventually_ge_atTop (1 : ℕ),
    eventually_filteredMoment_projection_lower p hc.le hh.le hy hp] with N hmN hN hproj
  have htheta : (Real.exp h - 1) / 2 * Real.exp (c * N) ≤
      Chebyshev.theta (Real.exp h * Real.exp (c * N)) - Chebyshev.theta (Real.exp (c * N)) :=
    (le_div_iff₀ (Real.exp_pos _)).mp hmN.le
  have hexp : Real.exp (-(3 / 2 : ℝ) * (c * N + h)) * Real.exp (c * N) =
      Real.exp (-(c * N) / 2) * Real.exp (-(3 / 2 : ℝ) * h) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ localConstant h *
      (Real.exp (-(c * N) / 2) * (c * N) ^ N / (N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (local_monomial_lower hN hc.le) (localConstant_pos hh).le
    _ = ((1 / 4 : ℝ) * ((c * N) ^ N / (N.factorial : ℝ)) *
      Real.exp (-(3 / 2 : ℝ) * (c * N + h))) *
        ((Real.exp h - 1) / 2 * Real.exp (c * N)) := by
      dsimp [localConstant]
      calc
        _ = ((Real.exp h - 1) / 8 * ((c * N) ^ N / (N.factorial : ℝ))) *
          (Real.exp (-(c * N) / 2) * Real.exp (-(3 / 2 : ℝ) * h)) := by ring
        _ = _ := by rw [← hexp]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left htheta (by positivity)).trans hproj

/-- Whenever the normalized local rate exceeds one, the rotated real
projection of the actual prime window tends to positive infinity. -/
theorem normalized_filteredMoment_projection_tendsto (p : Polynomial ℂ)
    {u c h y : ℝ} (hu : 0 < u) (hc : 0 < c) (hh : 0 < h) (hy : |y| * h ≤ 1)
    (hp : p.eval (c : ℂ) = 1) (hr : 1 < u * localGrowth c) :
    Tendsto (fun N : ℕ ↦ u ^ (N + 1) *
      (Complex.exp (I * y * (c * N : ℝ)) * filteredMoment p N y h (c * N)).re)
      atTop atTop := by
  have hg : Tendsto (fun N : ℕ ↦ (u * localGrowth c) ^ N / (N : ℝ)) atTop atTop := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 (Real.log (u * localGrowth c))
      (Real.log_pos hr)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    apply h.congr'
    filter_upwards [] with N
    simp only [Function.comp_apply, Real.rpow_one, mul_comm (Real.log (u * localGrowth c)),
      Real.exp_nat_mul, Real.exp_log (by linarith : 0 < u * localGrowth c)]
  have hg' := hg.const_mul_atTop (show 0 < localConstant h * u / 6 by
    have := localConstant_pos hh
    positivity)
  apply tendsto_atTop_mono' atTop ?_ hg'
  filter_upwards [eventually_filteredMoment_growth_lower p hc hh hy hp] with N hN
  have hm := mul_le_mul_of_nonneg_left hN (pow_nonneg hu.le (N + 1))
  apply le_trans (le_of_eq ?_) hm
  rw [pow_succ, mul_pow]
  ring

/-- The same actual-prime window diverges in norm. This conclusion does
not take norms inside the window: its complete internal phase is retained. -/
theorem normalized_filteredMoment_norm_tendsto (p : Polynomial ℂ)
    {u c h y : ℝ} (hu : 0 < u) (hc : 0 < c) (hh : 0 < h) (hy : |y| * h ≤ 1)
    (hp : p.eval (c : ℂ) = 1) (hr : 1 < u * localGrowth c) :
    Tendsto (fun N : ℕ ↦ u ^ (N + 1) * ‖filteredMoment p N y h (c * N)‖)
      atTop atTop := by
  apply tendsto_atTop_mono (fun N ↦ ?_)
    (normalized_filteredMoment_projection_tendsto p hu hc hh hy hp hr)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu.le _)
  have hrot : ‖Complex.exp (I * y * (c * N : ℝ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  simpa only [norm_mul, hrot, one_mul] using
    Complex.re_le_norm (Complex.exp (I * y * (c * N : ℝ)) * filteredMoment p N y h (c * N))

/-- At the required source normalization the local exponential rate is
explicit, positive and independent of all other polynomial coefficients. -/
theorem source_localGrowth {u : ℝ} (hu : 0 < u) :
    u * localGrowth u⁻¹ = Real.exp (1 - u⁻¹ / 2) := by
  rw [localGrowth, ← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

/-- Every fixed normalized polynomial has an exponentially large window
near `exp(N/u)`. The theorem applies to all complex coefficient choices and
all extra zero or pole roots; no search for a special polynomial is used. -/
theorem every_normalized_filter_has_large_windows (p : Polynomial ℂ)
    {u h y : ℝ} (hu : 1 / 2 < u) (hh : 0 < h) (hy : |y| * h ≤ 1)
    (hp : p.eval (u : ℂ)⁻¹ = 1) :
    Tendsto (fun N : ℕ ↦ u ^ (N + 1) * ‖filteredMoment p N y h (u⁻¹ * N)‖)
      atTop atTop := by
  have hu0 : 0 < u := by linarith
  apply normalized_filteredMoment_norm_tendsto p hu0 (inv_pos.mpr hu0) hh hy
    (by simpa only [Complex.ofReal_inv] using hp)
  rw [source_localGrowth hu0, Real.one_lt_exp_iff]
  have hi : u⁻¹ < 2 := by
    rw [inv_eq_one_div, div_lt_iff₀ hu0]
    linarith
  linarith

end
end RiemannGaussian.PrimeWindow
