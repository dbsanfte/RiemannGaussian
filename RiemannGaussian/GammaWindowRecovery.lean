/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GammaMomentRecovery

/-!
# Arbitrarily narrow relative windows for signed gamma moments

The damping of a gamma kernel is retained as a free parameter. For any
fixed window around its mean, a sufficiently small exponential growth
allowance gives geometric control of both omitted tails. The whole signed
moment therefore forces a positive value inside that window. The bounds
use an actual weighted L1 integral; no pointwise sign or growth hypothesis
is substituted for the signal.
-/

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

/-- Gamma kernel with variable damping and the normalization of a double
pole moment. Its nonnegative sign on positive time is unchanged. -/
def dampedFactorialGammaKernel (d : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  d ^ 2 * factorialGammaKernel n (d * t)

/-- Exact normalization relating the damped kernel to its Laplace moment. -/
theorem dampedFactorialGammaKernel_eq (d : ℝ) (n : ℕ) (t : ℝ) :
    dampedFactorialGammaKernel d n t =
      d ^ (n + 2) * (t ^ n * Real.exp (-d * t) / (n.factorial : ℝ)) := by
  simp only [dampedFactorialGammaKernel, factorialGammaKernel, mul_pow, pow_add, neg_mul]
  ring

private def tailRatio (b v : ℝ) : ℝ := v * Real.exp (1 - (1 - b) * v)

private theorem tailRatio_zero_lt_one {v : ℝ} (hv : 0 < v) (hv1 : v ≠ 1) :
    tailRatio 0 v < 1 := by
  have h := Real.log_lt_sub_one_of_pos hv hv1
  have he : tailRatio 0 v = Real.exp (Real.log v + 1 - v) := by
    rw [tailRatio, show Real.log v + 1 - v = Real.log v + (1 - v) by ring,
      Real.exp_add, Real.exp_log hv]
    simp
  rw [he, Real.exp_lt_one_iff]
  linarith

/-- Every fixed relative window about one admits a positive exponential
allowance for which both complete tail ratios are strictly below one. -/
theorem exists_gammaWindow_tail_allowance {l u : ℝ}
    (hl : 0 < l) (hl1 : l < 1) (hu : 1 < u) :
    ∃ b : ℝ, 0 < b ∧ 1 / u < 1 - b ∧
      l * Real.exp (1 - (1 - b) * l) < 1 ∧
      u * Real.exp (1 - (1 - b) * u) < 1 := by
  have hlu : 1 / u < (1 : ℝ) := (div_lt_one (by linarith)).mpr hu
  have hlow := tailRatio_zero_lt_one hl (ne_of_lt hl1)
  have hhigh := tailRatio_zero_lt_one (by linarith : 0 < u) (ne_of_gt hu)
  have hc : Continuous (fun b : ℝ => tailRatio b l) := by unfold tailRatio; fun_prop
  have hd : Continuous (fun b : ℝ => tailRatio b u) := by unfold tailRatio; fun_prop
  have hnear : ∀ᶠ b : ℝ in 𝓝 0,
      1 / u < 1 - b ∧ tailRatio b l < 1 ∧ tailRatio b u < 1 := by
    filter_upwards [((continuous_const.sub continuous_id).continuousAt
      (x := (0 : ℝ))).eventually (lt_mem_nhds (by simpa using hlu)),
      hc.continuousAt.eventually (gt_mem_nhds hlow),
      hd.continuousAt.eventually (gt_mem_nhds hhigh)] with b hb hlb hub
    exact ⟨by simpa only [one_div, Pi.sub_apply, id_eq] using hb, hlb, hub⟩
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hb := hball (show dist (e / 2) (0 : ℝ) < e by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  exact ⟨e / 2, by positivity, hb⟩

private theorem factorial_tilt_bound (n : ℕ) {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) :
    x ^ n / (n.factorial : ℝ) ≤ v ^ n * Real.exp (x / v) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.pow_div_factorial_le_exp (x / v) (div_nonneg hx hv.le) n)
    (pow_nonneg hv.le n)
  apply le_trans _ h
  rw [div_pow]
  field_simp
  exact le_rfl

private theorem lower_kernel_bound (n : ℕ) {b l x : ℝ}
    (hl : 0 < l) (hc : 0 ≤ 1 / l - (1 - b)) (hx : 0 ≤ x) (hxl : x ≤ l * n) :
    x ^ n * Real.exp (-(1 - b) * x) / (n.factorial : ℝ) ≤ tailRatio b l ^ n := by
  calc
    _ = (x ^ n / (n.factorial : ℝ)) * Real.exp (-(1 - b) * x) := by ring
    _ ≤ (l ^ n * Real.exp (x / l)) * Real.exp (-(1 - b) * x) :=
      mul_le_mul_of_nonneg_right (factorial_tilt_bound n hx hl) (Real.exp_pos _).le
    _ = l ^ n * Real.exp (x * (1 / l - (1 - b))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ l ^ n * Real.exp ((l * n) * (1 / l - (1 - b))) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxl hc)) (by positivity)
    _ = tailRatio b l ^ n := by
      have he : (l * n) * (1 / l - (1 - b)) = (n : ℝ) * (1 - (1 - b) * l) := by
        field_simp
      rw [he, Real.exp_nat_mul, tailRatio, mul_pow]

private theorem upper_kernel_bound (n : ℕ) {b u x : ℝ}
    (hu : 0 < u) (hc : 1 / u - (1 - b) ≤ 0) (hx : 0 ≤ x) (hux : u * n ≤ x) :
    x ^ n * Real.exp (-(1 - b) * x) / (n.factorial : ℝ) ≤ tailRatio b u ^ n := by
  calc
    _ = (x ^ n / (n.factorial : ℝ)) * Real.exp (-(1 - b) * x) := by ring
    _ ≤ (u ^ n * Real.exp (x / u)) * Real.exp (-(1 - b) * x) :=
      mul_le_mul_of_nonneg_right (factorial_tilt_bound n hx hu) (Real.exp_pos _).le
    _ = u ^ n * Real.exp (x * (1 / u - (1 - b))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ u ^ n * Real.exp ((u * n) * (1 / u - (1 - b))) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hux hc)) (by positivity)
    _ = tailRatio b u ^ n := by
      have he : (u * n) * (1 / u - (1 - b)) = (n : ℝ) * (1 - (1 - b) * u) := by
        field_simp
      rw [he, Real.exp_nat_mul, tailRatio, mul_pow]

private theorem kernel_split (f : ℝ → ℝ) (d b : ℝ) (n : ℕ) (t : ℝ) :
    f t * dampedFactorialGammaKernel d n t =
      d ^ 2 * (f t * Real.exp (-(b * d) * t)) *
        ((d * t) ^ n * Real.exp (-(1 - b) * (d * t)) / (n.factorial : ℝ)) := by
  have he : Real.exp (-(d * t)) =
      Real.exp (-(b * d) * t) * Real.exp (-(1 - b) * (d * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [dampedFactorialGammaKernel, factorialGammaKernel, he]
  ring

/-- The full signed moment is bounded by both weighted L1 tails if the
actual signal is nonpositive throughout the selected relative window. -/
theorem dampedGammaMoment_le_tails_of_nonpositive_window {f : ℝ → ℝ} {d b l u : ℝ}
    (hd : 0 < d) (hb : 0 ≤ b) (hl : 0 < l) (hl1 : l < 1)
    (hu : 1 < u) (hbu : 1 / u < 1 - b)
    (hf0 : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hi : Integrable (fun t : ℝ => f t * Real.exp (-(b * d) * t)))
    (n : ℕ) (hn : Integrable (fun t : ℝ => f t * dampedFactorialGammaKernel d n t))
    (hmid : ∀ t ∈ Icc (l * n / d) (u * n / d), f t ≤ 0) :
    (∫ t : ℝ, f t * dampedFactorialGammaKernel d n t) ≤
      d ^ 2 * ((l * Real.exp (1 - (1 - b) * l)) ^ n +
        (u * Real.exp (1 - (1 - b) * u)) ^ n) *
        ∫ t : ℝ, ‖f t * Real.exp (-(b * d) * t)‖ := by
  have hlc : 0 ≤ 1 / l - (1 - b) := by
    have ht : (1 : ℝ) < 1 / l := (lt_div_iff₀ hl).mpr (by simpa using hl1)
    linarith
  have hu0 : 0 < u := by linarith
  have hql : 0 ≤ tailRatio b l := by unfold tailRatio; positivity
  have hqu : 0 ≤ tailRatio b u := by unfold tailRatio; positivity
  have hq : 0 ≤ tailRatio b l ^ n + tailRatio b u ^ n := by positivity
  have hbound (t : ℝ) : f t * dampedFactorialGammaKernel d n t ≤
      (d ^ 2 * (tailRatio b l ^ n + tailRatio b u ^ n)) *
        ‖f t * Real.exp (-(b * d) * t)‖ := by
    by_cases ht : t ≤ 0
    · rw [hf0 t ht, zero_mul]
      positivity
    have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    by_cases hm : t ∈ Icc (l * n / d) (u * n / d)
    · apply (mul_nonpos_of_nonpos_of_nonneg (hmid t hm) (by
        unfold dampedFactorialGammaKernel factorialGammaKernel; positivity)).trans
      positivity
    have htail : (d * t) ^ n * Real.exp (-(1 - b) * (d * t)) / (n.factorial : ℝ) ≤
        tailRatio b l ^ n + tailRatio b u ^ n := by
      rcases lt_or_ge t (l * n / d) with h | h
      · have hx : d * t ≤ l * n := by
          simpa only [mul_comm d t] using (le_div_iff₀ hd).mp h.le
        exact (lower_kernel_bound n hl hlc (by positivity) hx).trans
          (le_add_of_nonneg_right (pow_nonneg hqu n))
      · have hh : u * n / d ≤ t := (lt_of_not_ge (fun hh => hm ⟨h, hh⟩)).le
        have hx : u * n ≤ d * t := by simpa only [mul_comm d t] using (div_le_iff₀ hd).mp hh
        exact (upper_kernel_bound n hu0 (by linarith) (by positivity) hx).trans
          (le_add_of_nonneg_left (pow_nonneg hql n))
    rw [kernel_split]
    calc
      _ ≤ (d ^ 2 * ‖f t * Real.exp (-(b * d) * t)‖) *
          ((d * t) ^ n * Real.exp (-(1 - b) * (d * t)) / (n.factorial : ℝ)) := by
        gcongr
        exact Real.le_norm_self _
      _ ≤ (d ^ 2 * ‖f t * Real.exp (-(b * d) * t)‖) *
          (tailRatio b l ^ n + tailRatio b u ^ n) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have h := integral_mono hn (hi.norm.const_mul
    (d ^ 2 * (tailRatio b l ^ n + tailRatio b u ^ n))) hbound
  rw [integral_const_mul] at h
  exact h

/-- Divergent signed moments yield a positive value in each sufficiently
late relative window, whenever its two geometric tail ratios are below one. -/
theorem eventually_exists_pos_in_dampedGammaWindow {f : ℝ → ℝ} {d b l u : ℝ}
    (hd : 0 < d) (hb : 0 ≤ b) (hl : 0 < l) (hl1 : l < 1)
    (hu : 1 < u) (hbu : 1 / u < 1 - b)
    (hql : l * Real.exp (1 - (1 - b) * l) < 1)
    (hqu : u * Real.exp (1 - (1 - b) * u) < 1)
    (hf0 : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hi : Integrable (fun t : ℝ => f t * Real.exp (-(b * d) * t)))
    (hn : ∀ n : ℕ, Integrable (fun t : ℝ => f t * dampedFactorialGammaKernel d n t))
    (hm : Tendsto (fun n : ℕ => ∫ t : ℝ, f t * dampedFactorialGammaKernel d n t)
      atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ∃ t ∈ Icc (l * n / d) (u * n / d), 0 < f t := by
  have hl0 : 0 ≤ l * Real.exp (1 - (1 - b) * l) := by positivity
  have hu0 : 0 ≤ u * Real.exp (1 - (1 - b) * u) := by
    have : 0 < u := by linarith
    positivity
  have htail := (((tendsto_pow_atTop_nhds_zero_of_lt_one hl0 hql).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hu0 hqu)).const_mul (d ^ 2)).mul_const
      (∫ t : ℝ, ‖f t * Real.exp (-(b * d) * t)‖)
  simp only [zero_add, mul_zero, zero_mul] at htail
  filter_upwards [hm.eventually (eventually_gt_atTop (1 : ℝ)),
    htail.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hmn htn
  by_contra hnot
  push Not at hnot
  have hbound := dampedGammaMoment_le_tails_of_nonpositive_window hd hb hl hl1 hu hbu
    hf0 hi n (hn n) hnot
  linarith

end
end RiemannGaussian
