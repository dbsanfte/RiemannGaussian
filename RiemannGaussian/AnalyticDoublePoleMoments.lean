/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMomentPoleJet
import RiemannGaussian.ZetaMoebiusTailMoments
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Data.Nat.Choose.Cast

/-!
# A uniform error bound for a selected double pole

An analytic numerator is divided exactly into its double pole, simple
pole, and second divided difference. Cauchy's estimate bounds the full
remaining complex moment uniformly after geometric normalization. The
leading double-pole term retains its linear moment-order factor.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Divided differences preserve local analyticity, including the
filled value at the base point. -/
theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {a s : ℂ}
    (ha : AnalyticAt ℂ f a) (hs : AnalyticAt ℂ f s) : AnalyticAt ℂ (dslope f a) s := by
  by_cases h : s = a
  · subst s
    obtain ⟨p, hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · rw [analyticAt_congr (dslope_eventuallyEq_slope_of_ne f h)]
    exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h)).smul
      (hs.sub analyticAt_const)

/-- The same divided difference is analytic throughout any domain
containing its base point. -/
theorem analyticOnNhd_dslope_of_mem {f : ℂ → ℂ} {K : Set ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f K) (ha : a ∈ K) : AnalyticOnNhd ℂ (dslope f a) K :=
  fun s hs ↦ analyticAt_dslope_of_analyticAt (hf a ha) (hf s hs)

/-- Exact division keeps both polar coefficients and the complete
analytic second divided difference. -/
theorem div_sub_sq_eq_dslope (f : ℂ → ℂ) (a : ℂ) {s : ℂ} (hs : s ≠ a) :
    f s / (s - a) ^ 2 = f a * ((s - a)⁻¹) ^ 2 + deriv f a * (s - a)⁻¹ +
      dslope (dslope f a) a s := by
  rw [dslope_of_ne _ hs, slope, dslope_of_ne _ hs, slope, dslope_same]
  simp only [smul_eq_mul, vsub_eq_sub]
  field_simp
  ring

/-- A simple pole at any complex point gives the complete geometric
signed moment at any evaluation center. -/
theorem signedTaylorMoment_inv_sub (n : ℕ) (a s : ℂ) :
    signedTaylorMoment n (fun z ↦ (z - a)⁻¹) s = ((s - a)⁻¹) ^ (n + 1) := by
  have ht := congrFun (iteratedDeriv_comp_const_add n (fun z : ℂ ↦ (z - a)⁻¹) s) 0
  simp only [add_zero] at ht
  rw [signedTaylorMoment, ← ht]
  have he : (fun z : ℂ ↦ (s + z - a)⁻¹) = (fun z ↦ (1 * z + (s - a))⁻¹) := by
    funext z
    congr 1
    ring
  rw [he]
  simpa only [signedTaylorMoment, one_pow, one_mul] using signedTaylorMoment_inv_linear n 1 (s - a)

/-- The double-pole moment retains its extra linear factor at every
order, with no restriction on the relative complex phase. -/
theorem signedTaylorMoment_inv_sub_sq (n : ℕ) (a : ℂ) {s : ℂ} (hs : s ≠ a) :
    signedTaylorMoment n (fun z ↦ ((z - a)⁻¹) ^ 2) s =
      ((n + 1 : ℕ) : ℂ) * ((s - a)⁻¹) ^ (n + 2) := by
  have he : (fun z : ℂ ↦ ((z - a)⁻¹) ^ 2) =ᶠ[𝓝 s]
      (fun z ↦ -deriv (fun w : ℂ ↦ (w - a)⁻¹) z) := by
    filter_upwards [compl_singleton_mem_nhds hs] with z hz
    have hd : deriv (fun w : ℂ ↦ (w - a)⁻¹) z = -(z - a)⁻¹ ^ 2 := by
      simpa only [id_eq, Pi.inv_apply, neg_div, one_div, inv_pow] using
        (((hasDerivAt_id z).sub_const a).fun_inv (sub_ne_zero.mpr hz)).deriv
    rw [hd, neg_neg]
  rw [signedTaylorMoment_congr n he]
  have hm := signedTaylorMoment_const_mul n (-1) (deriv (fun z : ℂ ↦ (z - a)⁻¹)) s
  simp only [neg_one_mul] at hm
  rw [hm, signedTaylorMoment_deriv, signedTaylorMoment_inv_sub]
  simp only [neg_mul, neg_neg]

/-- Every exact moment splits into its two selected pole coefficients
and one genuinely analytic remainder. -/
theorem signedTaylorMoment_div_sub_sq {f : ℂ → ℂ} {a s : ℂ}
    (ha : AnalyticAt ℂ f a) (hs : AnalyticAt ℂ f s) (hne : s ≠ a) (n : ℕ) :
    signedTaylorMoment n (fun z ↦ f z / (z - a) ^ 2) s =
      f a * (((n + 1 : ℕ) : ℂ) * ((s - a)⁻¹) ^ (n + 2)) +
      deriv f a * ((s - a)⁻¹) ^ (n + 1) + signedTaylorMoment n (dslope (dslope f a) a) s := by
  have he : (fun z ↦ f z / (z - a) ^ 2) =ᶠ[𝓝 s] (fun z ↦
      f a * ((z - a)⁻¹) ^ 2 + deriv f a * (z - a)⁻¹ + dslope (dslope f a) a z) := by
    filter_upwards [compl_singleton_mem_nhds hne] with z hz
    exact div_sub_sq_eq_dslope f a hz
  have hp : AnalyticAt ℂ (fun z ↦ (z - a)⁻¹) s :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne)
  have hd := analyticAt_dslope_of_analyticAt (analyticAt_dslope_of_analyticAt ha ha)
    (analyticAt_dslope_of_analyticAt ha hs)
  have h₂ : AnalyticAt ℂ (fun z ↦ f a * ((z - a)⁻¹) ^ 2) s := analyticAt_const.mul (hp.pow 2)
  have h₁ : AnalyticAt ℂ (fun z ↦ deriv f a * (z - a)⁻¹) s := analyticAt_const.mul hp
  have hsum : AnalyticAt ℂ (fun z ↦ f a * ((z - a)⁻¹) ^ 2 + deriv f a * (z - a)⁻¹) s := h₂.add h₁
  rw [signedTaylorMoment_congr n he,
    signedTaylorMoment_add n hsum hd,
    signedTaylorMoment_add n h₂ h₁,
    signedTaylorMoment_const_mul, signedTaylorMoment_const_mul,
    signedTaylorMoment_inv_sub_sq n a hne, signedTaylorMoment_inv_sub]

/-- The geometric normalization leaves a uniformly bounded error after
the leading linear double-pole source is subtracted. -/
theorem exists_doublePoleMoment_uniform_error {f : ℂ → ℂ} {s a : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall s R)) (ha : ‖s - a‖ < R) (hne : s ≠ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖(s - a) ^ (n + 2) * signedTaylorMoment n (fun z ↦ f z / (z - a) ^ 2) s -
        ((n + 1 : ℕ) : ℂ) * f a‖ ≤ C := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) ha
  have has : a ∈ closedBall s R := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using ha.le
  have hss : s ∈ closedBall s R := mem_closedBall_self hR.le
  have hd := analyticOnNhd_dslope_of_mem (analyticOnNhd_dslope_of_mem hf has) has
  obtain ⟨B, hB⟩ := ((isCompact_closedBall s R).image_of_continuousOn hd.continuousOn).isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨s, hss, rfl⟩)
  have hdc : DiffContOnCl ℂ (dslope (dslope f a) a) (ball s R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    exact hd.differentiableOn
  have hb (n : ℕ) : ‖signedTaylorMoment n (dslope (dslope f a) a) s‖ ≤ B / R ^ n :=
    norm_signedTaylorMoment_le hR hdc (fun z hz ↦ hB _ ⟨z, sphere_subset_closedBall hz, rfl⟩) n
  refine ⟨‖s - a‖ * ‖deriv f a‖ + B * ‖s - a‖ ^ 2 + 1, by positivity, ?_⟩
  intro n
  have hne' : s - a ≠ 0 := sub_ne_zero.mpr hne
  have hpow : (s - a) ^ (n + 2) * ((s - a)⁻¹) ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hne', one_pow]
  have hpow' : (s - a) ^ (n + 2) * ((s - a)⁻¹) ^ (n + 1) = s - a := by
    rw [pow_succ (s - a) (n + 1), mul_right_comm, ← mul_pow, mul_inv_cancel₀ hne', one_pow, one_mul]
  have he : (s - a) ^ (n + 2) * signedTaylorMoment n (fun z ↦ f z / (z - a) ^ 2) s -
      ((n + 1 : ℕ) : ℂ) * f a =
      (s - a) * deriv f a + (s - a) ^ (n + 2) * signedTaylorMoment n (dslope (dslope f a) a) s := by
    rw [signedTaylorMoment_div_sub_sq (hf a has) (hf s hss) hne]
    calc
      _ = f a * ((n + 1 : ℕ) : ℂ) * ((s - a) ^ (n + 2) * ((s - a)⁻¹) ^ (n + 2)) +
          deriv f a * ((s - a) ^ (n + 2) * ((s - a)⁻¹) ^ (n + 1)) +
          (s - a) ^ (n + 2) * signedTaylorMoment n (dslope (dslope f a) a) s -
          ((n + 1 : ℕ) : ℂ) * f a := by ring
      _ = _ := by rw [hpow, hpow']; ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_pow]
  have ht : ‖s - a‖ ^ (n + 2) * (B / R ^ n) ≤ B * ‖s - a‖ ^ 2 := by
    have hpowle : ‖s - a‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) ha.le n
    rw [pow_add]
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpowle (by positivity : 0 ≤ ‖s - a‖ ^ 2))
      (by positivity : 0 ≤ B / R ^ n)).trans_eq
    field_simp
  have hbn := mul_le_mul_of_nonneg_left (hb n) (by positivity : 0 ≤ ‖s - a‖ ^ (n + 2))
  linarith

/-- The exact convolution law for signed factorial moments of a
product. Every cofactor phase stays coupled to its Dirichlet moment. -/
theorem signedTaylorMoment_mul {f g : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hg : AnalyticAt ℂ g s) (n : ℕ) :
    signedTaylorMoment n (fun z ↦ f z * g z) s =
      ∑ k ∈ Finset.range (n + 1), signedTaylorMoment k f s * signedTaylorMoment (n - k) g s := by
  simp only [signedTaylorMoment, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hsign : (-1 : ℂ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [Nat.cast_choose ℂ hkn, hsign]
  have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk0 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  field_simp

/-- A holomorphic cofactor times a genuinely convergent Dirichlet
series has one exact arithmetic kernel at every moment order. The
kernel includes all Leibniz terms and their complex signs. -/
theorem hasSum_signedTaylorMoment_mul_LSeries (c : ℕ → ℂ) (hc0 : c 0 = 0)
    {A : ℂ → ℂ} {s : ℂ} (hA : AnalyticAt ℂ A s)
    (hc : LSeries.abscissaOfAbsConv c < s.re) (n : ℕ) :
    HasSum (fun m : ℕ ↦ c m * zetaPrimeFeature s m *
      ∑ k ∈ Finset.range (n + 1), signedTaylorMoment k A s *
        ((Real.log m : ℂ) ^ (n - k) / ((n - k).factorial : ℂ)))
      (signedTaylorMoment n (fun z ↦ A z * LSeries c z) s) := by
  rw [signedTaylorMoment_mul hA (LSeries_analyticOnNhd c s hc)]
  have h := hasSum_sum (s := Finset.range (n + 1)) (fun k _ ↦
    (hasSum_signedTaylorMoment_LSeries c hc0 hc (n - k)).mul_left (signedTaylorMoment k A s))
  apply h.congr_fun
  intro m
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end

end RiemannGaussian
