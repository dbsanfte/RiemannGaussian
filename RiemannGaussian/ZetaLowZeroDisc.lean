/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerBernoulli
import RiemannGaussian.AnalyticNewtonIsolation

/-!
# Explicit analytic bounds for a low-zero isolation disc

The already proved Bernoulli identity bounds actual zeta on a full disc
crossing the critical line. Cauchy's estimate then controls its second
derivative on the smaller disc. Neither bound assumes a zero location.
-/

namespace RiemannGaussian.ZetaLowZeroDisc
noncomputable section
open Complex Metric Set

/-- A uniform low-height bound obtained from the actual second Bernoulli tail. -/
theorem norm_le_thirty_two {s : ℂ} (hs : (1 / 4 : ℝ) ≤ s.re)
    (hn : ‖s‖ ≤ 16) (hi : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 32 := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 1 := by intro he; norm_num [he] at hi
  have hd : 1 ≤ ‖s - 1‖ := by
    have hh := Complex.abs_im_le_norm (s - 1)
    simpa only [sub_im, one_im, sub_zero] using hi.trans (by simpa using hh)
  have htail : ‖ZetaEulerBernoulli.tail 0 s‖ ≤ (2 / 15 : ℝ) := by
    have hh := ZetaEulerBernoulli.norm_tail_le hs0 0
    norm_num only [Nat.cast_zero, zero_add, Real.one_rpow] at hh
    refine hh.trans ((div_le_iff₀ (by positivity : 0 < 6 * (s.re + 1))).mpr ?_)
    nlinarith
  have hs1 : ‖s + 1‖ ≤ 17 := by
    have hh := norm_add_le s 1
    norm_num at hh
    linarith
  have hterm : ‖s * (s + 1) / 2 * ZetaEulerBernoulli.tail 0 s‖ ≤ 20 := by
    rw [norm_mul, norm_div, norm_mul]
    norm_num only [norm_ofNat]
    calc
      ‖s‖ * ‖s + 1‖ / 2 * ‖ZetaEulerBernoulli.tail 0 s‖ ≤ 16 * 17 / 2 * (2 / 15) := by gcongr
      _ ≤ 20 := by norm_num
  have hpole : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hd)).mpr hd
  have hlinear : ‖s / 12‖ ≤ 2 := by
    rw [norm_div]
    norm_num only [norm_ofNat]
    exact (div_le_iff₀ (by norm_num)).mpr (by linarith)
  have he := ZetaEulerBernoulli.zeta_eq hs0 hsne 0
  simp only [ZetaEulerCell.partialSum, Finset.sum_range_zero, Nat.cast_zero,
    zero_add, one_cpow, mul_one] at he
  rw [he]
  calc
    _ ≤ ‖(1 : ℂ) / (s - 1) + 1 / 2 + s / 12‖ +
        ‖s * (s + 1) / 2 * ZetaEulerBernoulli.tail 0 s‖ := norm_sub_le _ _
    _ ≤ (‖(1 : ℂ) / (s - 1)‖ + ‖(1 / 2 : ℂ)‖ + ‖s / 12‖) + 20 :=
      add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) hterm
    _ ≤ 32 := by norm_num at hpole hlinear ⊢; linarith

/-- Center on the critical line with an arbitrary real ordinate. -/
def center (t : ℝ) : ℂ := (1 / 2 : ℂ) + t * I

private theorem geometry {t : ℝ} (ht : t ∈ Icc (14 : ℝ) 15)
    {s : ℂ} (hs : s ∈ closedBall (center t) (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ s.re ∧ ‖s‖ ≤ 16 ∧ 1 ≤ |s.im| := by
  have hn := mem_closedBall_iff_norm.mp hs
  have hre : (center t).re = 1 / 2 := by norm_num [center]
  have him : (center t).im = t := by norm_num [center]
  have hcn : ‖center t‖ ≤ 31 / 2 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (center t)
    rw [hre, him, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] at hh
    norm_num at hh
    linarith [ht.2]
  have hsr : |s.re - 1 / 2| ≤ 1 / 4 := by
    have hh := (Complex.abs_re_le_norm (s - center t)).trans hn
    simpa only [sub_re, hre] using hh
  have hsi : |s.im - t| ≤ 1 / 4 := by
    have hh := (Complex.abs_im_le_norm (s - center t)).trans hn
    simpa only [sub_im, him] using hh
  refine ⟨by linarith [(abs_le.mp hsr).1], ?_, ?_⟩
  · have hh := norm_add_le (s - center t) (center t)
    rw [sub_add_cancel] at hh
    linarith
  · have hh := le_abs_self s.im
    linarith [(abs_le.mp hsi).1, ht.1]

/-- The full quarter-radius disc has a proved absolute bound and avoids the pole. -/
theorem bound_on_disc {t : ℝ} (ht : t ∈ Icc (14 : ℝ) 15)
    {s : ℂ} (hs : s ∈ closedBall (center t) (1 / 4 : ℝ)) :
    s ≠ 1 ∧ ‖riemannZeta s‖ ≤ 32 := by
  obtain ⟨hr, hn, hi⟩ := geometry ht hs
  exact ⟨by intro he; norm_num [he] at hi, norm_le_thirty_two hr hn hi⟩

/-- Actual zeta is analytic on the full disc used in Cauchy's estimate. -/
theorem analytic_on_disc {t : ℝ} (ht : t ∈ Icc (14 : ℝ) 15) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (center t) (1 / 4 : ℝ)) := by
  intro s hs
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_compl_singleton s (by simpa using (bound_on_disc ht hs).1)

/-- The second derivative is bounded uniformly on the entire smaller disc. -/
theorem second_derivative_bound {t : ℝ} (ht : t ∈ Icc (14 : ℝ) 15)
    {s : ℂ} (hs : s ∈ closedBall (center t) (1 / 8 : ℝ)) :
    ‖deriv (deriv riemannZeta) s‖ ≤ 4096 := by
  have hsub : closedBall s (1 / 8 : ℝ) ⊆ closedBall (center t) (1 / 4 : ℝ) := by
    intro z hz
    apply mem_closedBall.mpr
    have hh := dist_triangle z s (center t)
    have hz' := mem_closedBall.mp hz
    have hs' := mem_closedBall.mp hs
    linarith
  have hf := ((analytic_on_disc ht).mono hsub).differentiableOn
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
    (by norm_num : (0 : ℝ) < 1 / 8)
    ((hf.mono closure_ball_subset_closedBall).diffContOnCl)
    (fun z hz => (bound_on_disc ht (hsub (sphere_subset_closedBall hz))).2)
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial] at hh
  exact hh

end
end RiemannGaussian.ZetaLowZeroDisc
