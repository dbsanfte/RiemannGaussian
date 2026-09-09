/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLogarithmicConvolution
import RiemannGaussian.GaussianXiDivisorContour

/-!
# The source retained by the logarithmic convolution

The centered Möbius convolution has the genuine Euler-half-plane
response `zeta'' / zeta + r * zeta' / zeta`. Its double-pole coefficient
is `m * (m - 1)`, whereas the complete prime-pair subtraction has
coefficient `m^2`. At a simple zero the convolution's leading source
vanishes; their signed difference still has coefficient `-m`.

The local analytic remainder is kept before taking limits. The source
comparison is a test of the proposed separation, not an arithmetic bound
on the Suzuki potential or a zero exclusion.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- The logarithmic derivative identity is valid at every analytic
nonzero point; no value at a zero is inferred from totalized division. -/
theorem deriv_logDeriv_add_sq {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (h0 : f s ≠ 0) :
    deriv (logDeriv f) s + (logDeriv f s) ^ 2 = deriv (deriv f) s / f s := by
  have hd := (hf.deriv.differentiableAt.hasDerivAt.div
    hf.differentiableAt.hasDerivAt h0).deriv
  change deriv (fun z ↦ deriv f z / f z) s = _ at hd
  change deriv (fun z ↦ deriv f z / f z) s + (deriv f s / f s) ^ 2 = _
  rw [hd]
  field_simp
  ring

/-- The actual centered prime coefficient has an absolutely convergent
Dirichlet response, including its unchanged center and derivative sign. -/
theorem LSeriesHasSum_vonMangoldt_center (r : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦
      ((ArithmeticFunction.vonMangoldt n * (Real.log n - r) : ℝ) : ℂ)) s
      (deriv (logDeriv riemannZeta) s + (r : ℂ) * logDeriv riemannZeta s) := by
  have hb : LSeries.abscissaOfAbsConv
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le_one (by exact_mod_cast hs)
  have hval : LSeries (LSeries.logMul
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))) s =
      deriv (logDeriv riemannZeta) s := by
    have h := iteratedDeriv_neg_logDeriv_riemannZeta hs 1
    have hd : deriv (fun z ↦ -logDeriv riemannZeta z) s =
        -deriv (logDeriv riemannZeta) s := by
      change deriv (-(logDeriv riemannZeta)) s = _
      exact deriv.neg (f := logDeriv riemannZeta) (x := s)
    simpa only [iteratedDeriv_one, hd, pow_one, neg_one_mul,
      Function.iterate_one, neg_inj] using h.symm
  have hlog := (LSeriesSummable_logMul_of_lt_re hb).LSeriesHasSum
  rw [hval] at hlog
  have hprime := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hprime
  have h := hlog.sub (hprime.smul (r : ℂ))
  convert h using 1
  · funext n
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LSeries.logMul,
      ← Complex.natCast_log, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  · simp only [logDeriv_apply]
    ring

/-- The complete centered Möbius coefficient has response `zeta''/zeta`
plus the first logarithmic derivative. This is a genuine convergent
series on `Re s > 1`, not a Dirichlet series asserted across its poles. -/
theorem LSeriesHasSum_moebius_log_mul_sub_center (r : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ ((∑ p ∈ n.divisorsAntidiagonal,
      (μ p.1 : ℝ) * Real.log p.2 * (Real.log p.2 - r) : ℝ) : ℂ)) s
      (deriv (deriv riemannZeta) s / riemannZeta s +
        (r : ℂ) * logDeriv riemannZeta s) := by
  have h := (LSeriesHasSum_vonMangoldt_center r hs).add
    (LSeriesHasSum_zetaPrimePairArithmetic hs)
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have ha := analyticOn_riemannZeta s (by simpa using hs1)
  have hd := deriv_logDeriv_add_sq ha (riemannZeta_ne_zero_of_one_lt_re hs)
  convert h using 1
  · funext n
    rw [sum_moebius_log_mul_sub_center]
    simp
  · linear_combination -hd

/-- Differentiating the local logarithmic residue retains one common
analytic remainder. The derivative channel has coefficient `-m`, before
it is combined with the square channel of coefficient `m^2`. -/
theorem AnalyticAt.exists_logDeriv_deriv_common_remainder {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ ∀ᶠ s in 𝓝[≠] a,
      logDeriv f s = (analyticOrderNatAt f a : ℂ) / (s - a) + h s ∧
      deriv (logDeriv f) s = -(analyticOrderNatAt f a : ℂ) / (s - a) ^ 2 + deriv h s := by
  obtain ⟨h, hh, he⟩ := AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic hf hfinite
  refine ⟨h, hh, ?_⟩
  filter_upwards [he, he.nhdsNE_deriv,
    hh.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs hds hhs (hsa : s ≠ a)
  refine ⟨hs, hds.trans ?_⟩
  have hd := ((hasDerivAt_const s (analyticOrderNatAt f a : ℂ)).fun_div
    ((hasDerivAt_id s).sub_const a) (sub_ne_zero.mpr hsa)).fun_add hhs.differentiableAt.hasDerivAt
  simpa only [zero_mul, mul_one, zero_sub, Pi.add_apply, Pi.div_apply, id_eq] using hd.deriv

/-- One pair of analytic remainders controls all complex centers at
once. The quadratic source and the whole first-order error retain their
signs; in particular, a moving center is not silently frozen. -/
theorem AnalyticAt.exists_logarithmicConvolution_uniform_remainder {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ A D : ℂ → ℂ, AnalyticAt ℂ A a ∧ AnalyticAt ℂ D a ∧
      D a = (analyticOrderNatAt f a : ℂ) ∧ ∀ᶠ s in 𝓝[≠] a, ∀ r : ℂ,
        (s - a) ^ 2 * (deriv (logDeriv f) s + (logDeriv f s) ^ 2 + r * logDeriv f s) -
          (analyticOrderNatAt f a : ℂ) * ((analyticOrderNatAt f a : ℂ) - 1) =
            (s - a) * (A s + r * D s) := by
  obtain ⟨h, hh, he⟩ := AnalyticAt.exists_logDeriv_deriv_common_remainder hf hfinite
  let m : ℂ := analyticOrderNatAt f a
  refine ⟨fun s ↦ 2 * m * h s + (s - a) * (deriv h s + h s ^ 2),
    fun s ↦ m + (s - a) * h s, ?_, ?_, by simp [m], ?_⟩
  · exact (analyticAt_const.mul hh).add
      ((analyticAt_id.sub analyticAt_const).mul (hh.deriv.add (hh.pow 2)))
  · exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hh)
  filter_upwards [he, self_mem_nhdsWithin] with s hs (hsa : s ≠ a) r
  rw [hs.1, hs.2]
  dsimp [m]
  field_simp [sub_ne_zero.mpr hsa]
  ring

/-- The full centered convolution has a local error linear in distance
and in `1 + norm r`, uniformly for every center. This estimate alone can
be small even when a simple zero is present. -/
theorem AnalyticAt.exists_logarithmicConvolution_uniform_bound {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ s in 𝓝[≠] a, ∀ r : ℂ,
      ‖(s - a) ^ 2 * (deriv (logDeriv f) s + (logDeriv f s) ^ 2 + r * logDeriv f s) -
        (analyticOrderNatAt f a : ℂ) * ((analyticOrderNatAt f a : ℂ) - 1)‖ ≤
          B * (1 + ‖r‖) * ‖s - a‖ := by
  obtain ⟨A, D, hA, hD, _, he⟩ :=
    AnalyticAt.exists_logarithmicConvolution_uniform_remainder hf hfinite
  let B : ℝ := ‖A a‖ + ‖D a‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hBA : ‖A a‖ < B := by dsimp [B]; linarith [norm_nonneg (D a)]
  have hBD : ‖D a‖ < B := by dsimp [B]; linarith [norm_nonneg (A a)]
  have hAb : ∀ᶠ s in 𝓝[≠] a, ‖A s‖ < B :=
    (hA.continuousAt.norm.tendsto.eventually (gt_mem_nhds hBA)).filter_mono
    nhdsWithin_le_nhds
  have hDb : ∀ᶠ s in 𝓝[≠] a, ‖D s‖ < B :=
    (hD.continuousAt.norm.tendsto.eventually (gt_mem_nhds hBD)).filter_mono
    nhdsWithin_le_nhds
  refine ⟨B, hB, ?_⟩
  filter_upwards [he, hAb, hDb] with s hs hAs hDs r
  rw [hs r, norm_mul]
  calc
    ‖s - a‖ * ‖A s + r * D s‖ ≤ ‖s - a‖ * (‖A s‖ + ‖r‖ * ‖D s‖) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [norm_mul] using norm_add_le (A s) (r * D s))
        (norm_nonneg _)
    _ ≤ ‖s - a‖ * (B + ‖r‖ * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hAs.le
        (mul_le_mul_of_nonneg_left hDs.le (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- Every convergent weight and every center with a controlled first
scaled limit retain this exact complex source. The extra center term
is explicit even when the center grows at reciprocal distance. -/
theorem AnalyticAt.tendsto_logarithmicConvolution_source {f w r : ℂ → ℂ} {a v b : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤)
    (hw : Tendsto w (𝓝[≠] a) (𝓝 v))
    (hr : Tendsto (fun s ↦ (s - a) * r s) (𝓝[≠] a) (𝓝 b)) :
    Tendsto (fun s ↦ (s - a) ^ 2 * w s *
      (deriv (logDeriv f) s + (logDeriv f s) ^ 2 + r s * logDeriv f s)) (𝓝[≠] a)
      (𝓝 (v * ((analyticOrderNatAt f a : ℂ) * ((analyticOrderNatAt f a : ℂ) - 1) +
        b * (analyticOrderNatAt f a : ℂ)))) := by
  obtain ⟨A, D, hA, hD, hDa, he⟩ :=
    AnalyticAt.exists_logarithmicConvolution_uniform_remainder hf hfinite
  have hsub : Tendsto (fun s : ℂ ↦ s - a) (𝓝[≠] a) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ ↦ s - a) (𝓝[≠] a) (𝓝 (a - a)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hAl : Tendsto A (𝓝[≠] a) (𝓝 (A a)) :=
    hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hDl : Tendsto D (𝓝[≠] a) (𝓝 (D a)) :=
    hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hDa] at hDl
  have hl := hw.mul ((tendsto_const_nhds
    (x := (analyticOrderNatAt f a : ℂ) * ((analyticOrderNatAt f a : ℂ) - 1))).add
      ((hsub.mul hAl).add (hr.mul hDl)))
  simp only [zero_mul, zero_add] at hl
  apply hl.congr'
  filter_upwards [he] with s hs
  have h := hs (r s)
  linear_combination -(w s) * h

/-- After subtracting the entire prime pair, the source is linear in
the multiplicity and is still present at a simple zero. This identity
keeps both the complex weight and any scaled moving-center contribution. -/
theorem AnalyticAt.tendsto_logarithmicPrime_source {f w r : ℂ → ℂ} {a v b : ℂ}
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤)
    (hw : Tendsto w (𝓝[≠] a) (𝓝 v))
    (hr : Tendsto (fun s ↦ (s - a) * r s) (𝓝[≠] a) (𝓝 b)) :
    Tendsto (fun s ↦ (s - a) ^ 2 * w s *
      (deriv (logDeriv f) s + r s * logDeriv f s)) (𝓝[≠] a)
      (𝓝 (v * (analyticOrderNatAt f a : ℂ) * (b - 1))) := by
  have hl := AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt hf hfinite
  have hp := hw.mul (hl.pow 2)
  have h := (AnalyticAt.tendsto_logarithmicConvolution_source hf hfinite hw hr).sub hp
  have hv : v * ((analyticOrderNatAt f a : ℂ) * ((analyticOrderNatAt f a : ℂ) - 1) +
      b * (analyticOrderNatAt f a : ℂ)) - v * (analyticOrderNatAt f a : ℂ) ^ 2 =
        v * (analyticOrderNatAt f a : ℂ) * (b - 1) := by ring
  rw [hv] at h
  convert h using 1
  funext s
  ring

private theorem zeta_second_quotient_germ (rho : NontrivialZetaZero) :
    (fun s ↦ deriv (deriv riemannZeta) s / riemannZeta s) =ᶠ[𝓝[≠] rho.1]
      fun s ↦ deriv (logDeriv riemannZeta) s + (logDeriv riemannZeta s) ^ 2 := by
  have ha := analyticAt_riemannZeta_nontrivialZero rho
  have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hn := ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun h ↦ hfinite (analyticOrderAt_eq_top.mpr h))
  filter_upwards [hn, ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with s hs has
  exact (deriv_logDeriv_add_sq has hs).symm

/-- The actual Möbius-convolution continuation has the same local bound
at every nontrivial zeta zero, uniformly for all complex centers and
without a simplicity or right-half-plane assumption. -/
theorem exists_zetaCenteredConvolution_uniform_bound (rho : NontrivialZetaZero) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ s in 𝓝[≠] rho.1, ∀ r : ℂ,
      ‖(s - rho.1) ^ 2 * (deriv (deriv riemannZeta) s / riemannZeta s +
          r * logDeriv riemannZeta s) -
        (analyticZetaZeroMultiplicity rho : ℂ) * ((analyticZetaZeroMultiplicity rho : ℂ) - 1)‖ ≤
          B * (1 + ‖r‖) * ‖s - rho.1‖ := by
  obtain ⟨B, hB, he⟩ := AnalyticAt.exists_logarithmicConvolution_uniform_bound
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  refine ⟨B, hB, ?_⟩
  filter_upwards [he, zeta_second_quotient_germ rho] with s hs hq r
  simpa only [hq, analyticZetaZeroMultiplicity] using hs r

/-- All convergent complex weight families have the same exact source
law for the actual convolution. A center of reciprocal-distance size
contributes `b*m`; it cannot be discarded as a bounded-center error. -/
theorem tendsto_zetaCenteredConvolution_source (rho : NontrivialZetaZero)
    {w r : ℂ → ℂ} {v b : ℂ}
    (hw : Tendsto w (𝓝[≠] rho.1) (𝓝 v))
    (hr : Tendsto (fun s ↦ (s - rho.1) * r s) (𝓝[≠] rho.1) (𝓝 b)) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * w s *
      (deriv (deriv riemannZeta) s / riemannZeta s + r s * logDeriv riemannZeta s)) (𝓝[≠] rho.1)
      (𝓝 (v * ((analyticZetaZeroMultiplicity rho : ℂ) *
        ((analyticZetaZeroMultiplicity rho : ℂ) - 1) + b * (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  have h := AnalyticAt.tendsto_logarithmicConvolution_source
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho) hw hr
  apply h.congr'
  filter_upwards [zeta_second_quotient_germ rho] with s hs
  rw [hs]

/-- Subtracting the whole ordered prime pair preserves the original
linear multiplicity source for all the same weights and moving centers.
There is no source loss in the exact arithmetic identity itself. -/
theorem tendsto_zetaCenteredConvolution_sub_pair_source (rho : NontrivialZetaZero)
    {w r : ℂ → ℂ} {v b : ℂ}
    (hw : Tendsto w (𝓝[≠] rho.1) (𝓝 v))
    (hr : Tendsto (fun s ↦ (s - rho.1) * r s) (𝓝[≠] rho.1) (𝓝 b)) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * w s *
      (deriv (deriv riemannZeta) s / riemannZeta s + r s * logDeriv riemannZeta s -
        (logDeriv riemannZeta s) ^ 2)) (𝓝[≠] rho.1)
      (𝓝 (v * (analyticZetaZeroMultiplicity rho : ℂ) * (b - 1))) := by
  have h := AnalyticAt.tendsto_logarithmicPrime_source
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho) hw hr
  apply h.congr'
  filter_upwards [zeta_second_quotient_germ rho] with s hs
  rw [hs]
  ring

/-- At a simple zero, every fixed-center weighted convolution tends to
zero at the quadratic scale. Its smallness cannot by itself exclude that
zero, even when the weight remains nonzero there. -/
theorem tendsto_zetaCenteredConvolution_simple (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (r : ℂ) {w : ℂ → ℂ} {v : ℂ}
    (hw : Tendsto w (𝓝[≠] rho.1) (𝓝 v)) :
    Tendsto (fun s ↦ (s - rho.1) ^ 2 * w s *
      (deriv (deriv riemannZeta) s / riemannZeta s + r * logDeriv riemannZeta s))
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hr : Tendsto (fun s : ℂ ↦ (s - rho.1) * r) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ ↦ (s - rho.1) * r) (𝓝[≠] rho.1)
      (𝓝 ((rho.1 - rho.1) * r)) from
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds)
  simpa only [hm, Nat.cast_one, sub_self, mul_zero, zero_mul, add_zero] using
    tendsto_zetaCenteredConvolution_source rho hw hr

/-- No weight with a nonzero limiting value can make the complete
signed response vanish at the quadratic scale when the scaled center
tends to zero. This applies also to a simple zero whose separate
Möbius-convolution source vanishes. -/
theorem not_tendsto_zetaCenteredConvolution_sub_pair_zero (rho : NontrivialZetaZero)
    {w r : ℂ → ℂ} {v : ℂ} (hv : v ≠ 0)
    (hw : Tendsto w (𝓝[≠] rho.1) (𝓝 v))
    (hr : Tendsto (fun s ↦ (s - rho.1) * r s) (𝓝[≠] rho.1) (𝓝 0)) :
    ¬Tendsto (fun s ↦ (s - rho.1) ^ 2 * w s *
      (deriv (deriv riemannZeta) s / riemannZeta s + r s * logDeriv riemannZeta s -
        (logDeriv riemannZeta s) ^ 2)) (𝓝[≠] rho.1) (𝓝 0) := by
  have h := tendsto_zetaCenteredConvolution_sub_pair_source rho hw hr
  simp only [zero_sub, mul_neg, mul_one] at h
  intro hzero
  exact (neg_ne_zero.mpr (mul_ne_zero hv (Nat.cast_ne_zero.mpr
    (Nat.ne_zero_of_lt (analyticZetaZeroMultiplicity_positive rho)))))
      (tendsto_nhds_unique h hzero)

end
end RiemannGaussian
