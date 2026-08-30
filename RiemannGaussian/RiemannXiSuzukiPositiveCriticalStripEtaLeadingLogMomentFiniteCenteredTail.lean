import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteOptimizedTail

/-!
# Cutoff-centered finite tails for the leading eta moment

At a nontrivial zero of multiplicity `m`, every eta logarithmic moment below
order `m` vanishes.  This permits the first nonzero moment to be recentered at
the arithmetic cutoff `a_N = log (2N+1)` without changing its value.  The
literal support tail then contains `(t-a_N)^m` instead of `t^m`, and translation
of the Gamma integral gives the full-exponent envelope

`exp (-sigma * a_N) * m! / sigma^(m+1)`.

Unlike the previously optimized split bound, this estimate needs no cutoff
condition and carries no power of `log (2N+1)`.  Lean proves that it is
strictly smaller whenever the older balanced-split cutoff applies.  The
resulting finite lower and upper certificates converge to the exact nonzero
leading eta defect.  The construction uses the entire verified multiplicity
chain; no zero simplicity assumption is made.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The translated real Gamma kernel is integrable on the half-line beginning
at its translation parameter. -/
theorem integrableOn_sub_pow_mul_exp_neg_mul_Ioi (k : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) (a : ℝ) :
    IntegrableOn (fun t : ℝ ↦
      (t - a) ^ k * Real.exp (-sigma * t)) (Ioi a) := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.addRight a
  have hemb : MeasurableEmbedding (fun u : ℝ ↦ u + a) := by
    simpa [e] using e.isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving (fun u : ℝ ↦ u + a) volume volume := by
    refine ⟨hemb.measurable, ?_⟩
    exact map_add_right_eq_self volume a
  have hrestrict := hpres.restrict_preimage_emb hemb (Ioi a)
  have hpreimage : (fun u : ℝ ↦ u + a) ⁻¹' Ioi a = Ioi 0 := by
    ext u
    simp
  apply (hrestrict.integrable_comp_emb hemb).mp
  change Integrable (fun u : ℝ ↦
    (u + a - a) ^ k * Real.exp (-sigma * (u + a)))
      (volume.restrict ((fun u : ℝ ↦ u + a) ⁻¹' Ioi a))
  rw [hpreimage]
  have hbase := integrableOn_pow_mul_exp_neg_mul_Ioi_zero_nat k hsigma
  have hscaled := hbase.const_mul (Real.exp (-sigma * a))
  apply hscaled.congr
  filter_upwards with u
  rw [add_sub_cancel_right,
    show -sigma * (u + a) = -sigma * a + -sigma * u by ring,
    Real.exp_add]
  ring

/-- Translation evaluates the shifted real Gamma tail without losing any
part of the exponential rate. -/
theorem integral_sub_pow_mul_exp_neg_mul_Ioi (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (a : ℝ) :
    (∫ t : ℝ in Ioi a,
      (t - a) ^ k * Real.exp (-sigma * t)) =
      Real.exp (-sigma * a) *
        ((k.factorial : ℝ) / sigma ^ (k + 1)) := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.addRight a
  have hemb : MeasurableEmbedding (fun u : ℝ ↦ u + a) := by
    simpa [e] using e.isClosedEmbedding.measurableEmbedding
  have hpres : MeasurePreserving (fun u : ℝ ↦ u + a) volume volume := by
    refine ⟨hemb.measurable, ?_⟩
    exact map_add_right_eq_self volume a
  have hrestrict := hpres.restrict_preimage_emb hemb (Ioi a)
  have hchange := hrestrict.integral_comp hemb
    (fun t : ℝ ↦ (t - a) ^ k * Real.exp (-sigma * t))
  have hpreimage : (fun u : ℝ ↦ u + a) ⁻¹' Ioi a = Ioi 0 := by
    ext u
    simp
  rw [hpreimage] at hchange
  rw [← hchange]
  calc
    (∫ u : ℝ in Ioi 0,
        (u + a - a) ^ k * Real.exp (-sigma * (u + a))) =
        ∫ u : ℝ in Ioi 0,
          Real.exp (-sigma * a) *
            (u ^ k * Real.exp (-sigma * u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [add_sub_cancel_right,
        show -sigma * (u + a) = -sigma * a + -sigma * u by ring,
        Real.exp_add]
      ring
    _ = Real.exp (-sigma * a) *
        ∫ u : ℝ in Ioi 0, u ^ k * Real.exp (-sigma * u) := by
      rw [integral_const_mul]
    _ = Real.exp (-sigma * a) *
        ((k.factorial : ℝ) / sigma ^ (k + 1)) := by
      have hmoment :=
        positiveHalfLineRealLogLaplaceMoment_eq_factorial k hsigma
      simpa only [positiveHalfLineRealLogLaplaceMoment] using
        congrArg (fun x : ℝ ↦ Real.exp (-sigma * a) * x) hmoment

/-- The cutoff-centered full-exponent envelope for an order-`k` eta support
tail. -/
def pairedEtaLogLaplaceMomentCenteredTailUpper (k : ℕ) (sigma : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) *
    ((k.factorial : ℝ) / sigma ^ (k + 1))

/-- The centered envelope is exactly an arithmetic odd-endpoint power times
the fixed shifted Gamma moment. -/
theorem pairedEtaLogLaplaceMomentCenteredTailUpper_eq_rpow
    (k : ℕ) (sigma : ℝ) (N : ℕ) :
    pairedEtaLogLaplaceMomentCenteredTailUpper k sigma N =
      (((2 * N + 1 : ℕ) : ℝ) ^ (-sigma)) *
        ((k.factorial : ℝ) / sigma ^ (k + 1)) := by
  unfold pairedEtaLogLaplaceMomentCenteredTailUpper
  rw [Real.rpow_def_of_pos (by positivity :
    (0 : ℝ) < (((2 * N + 1 : ℕ) : ℝ)))]
  congr 2
  ring

/-- The cutoff-centered tail envelope is strictly positive at every positive
horizontal tilt. -/
theorem pairedEtaLogLaplaceMomentCenteredTailUpper_pos
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    0 < pairedEtaLogLaplaceMomentCenteredTailUpper k sigma N := by
  unfold pairedEtaLogLaplaceMomentCenteredTailUpper
  exact mul_pos (Real.exp_pos _)
    (div_pos (by positivity) (pow_pos hsigma _))

/-- The cutoff-centered tail envelope tends to zero with the full horizontal
exponent. -/
theorem tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Tendsto (fun N : ℕ ↦ pairedEtaLogLaplaceMomentCenteredTailUpper k sigma N)
      atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ ↦ ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hscaled : Tendsto (fun N : ℕ ↦
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp hbase).const_mul_atTop' hsigma
  have hdecay : Tendsto (fun N : ℕ ↦
      Real.exp (-(sigma * Real.log (((2 * N + 1 : ℕ) : ℝ)))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscaled
  simpa only [pairedEtaLogLaplaceMomentCenteredTailUpper, neg_mul, zero_mul] using
    hdecay.mul_const ((k.factorial : ℝ) / sigma ^ (k + 1))

/-- Whenever the older balanced-split cutoff is valid, the centered envelope
is strictly smaller than that near-sharp envelope. -/
theorem pairedEtaLogLaplaceMomentCenteredTailUpper_lt_nearSharp
    (k N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hcutoff : ((k + 1 : ℕ) : ℝ) <
      sigma * Real.log (((2 * N + 1 : ℕ) : ℝ))) :
    pairedEtaLogLaplaceMomentCenteredTailUpper k sigma N <
      pairedEtaLogLaplaceMomentNearSharpTailUpper k sigma N := by
  let a : ℝ := Real.log (((2 * N + 1 : ℕ) : ℝ))
  let d : ℝ := ((k + 1 : ℕ) : ℝ)
  have hd : 0 < d := by positivity
  have hsa : d < sigma * a := by simpa [a, d] using hcutoff
  have ha : 0 < a := by
    rcases (mul_pos_iff.mp (hd.trans hsa)) with h | h
    · exact h.2
    · exact (not_lt_of_ge hsigma.le h.1).elim
  have hinv : 1 / sigma < a / d := by
    rw [div_lt_div_iff₀ hsigma hd]
    simpa [mul_comm] using hsa
  have hpow : (1 / sigma) ^ (k + 1) < (a / d) ^ (k + 1) :=
    pow_lt_pow_left₀ hinv (by positivity) (by omega)
  have hfactor :
      (k.factorial : ℝ) / sigma ^ (k + 1) <
        (k.factorial : ℝ) * (a / d) ^ (k + 1) := by
    rw [div_eq_mul_inv, ← inv_pow]
    rw [one_div] at hpow
    exact mul_lt_mul_of_pos_left hpow (by positivity)
  have hexp : Real.exp (-sigma * a) <
      Real.exp (-sigma * a + d) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold pairedEtaLogLaplaceMomentCenteredTailUpper
    pairedEtaLogLaplaceMomentNearSharpTailUpper
  change Real.exp (-sigma * a) *
      ((k.factorial : ℝ) / sigma ^ (k + 1)) <
    Real.exp (-sigma * a + d) *
      ((k.factorial : ℝ) * (a / d) ^ (k + 1))
  exact (mul_lt_mul_of_pos_left hfactor (Real.exp_pos _)).trans
    (mul_lt_mul_of_pos_right hexp (mul_pos (by positivity) (pow_pos (by
      exact div_pos ha hd) _)))

/-- The literal complex eta support tail, centered at its first logarithmic
endpoint, obeys the cutoff-centered Gamma envelope. -/
theorem norm_integral_pairedEtaLogLaplaceMoment_centeredTail_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∫ t : ℝ,
        (((t - Real.log (((2 * N + 1 : ℕ) : ℝ)) : ℝ) : ℂ) ^ k) *
          Complex.exp (-s * t)
        ∂pairedEtaLogTailMeasure N‖ ≤
      pairedEtaLogLaplaceMomentCenteredTailUpper k s.re N := by
  let a : ℝ := Real.log (((2 * N + 1 : ℕ) : ℝ))
  let f : ℝ → ℝ := fun t ↦ (t - a) ^ k * Real.exp (-s.re * t)
  have hmeasure : pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi a) := by
    simpa [a] using pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N
  have hfull : Integrable f (volume.restrict (Ioi a)) := by
    exact integrableOn_sub_pow_mul_exp_neg_mul_Ioi k hs a
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi a), 0 ≤ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr ht.le) k)
      (Real.exp_pos _).le
  have hnorm :
      ‖∫ t : ℝ,
          (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := by
    calc
      ‖∫ t : ℝ,
            (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
            ∂pairedEtaLogTailMeasure N‖ ≤
          ∫ t : ℝ,
            ‖(((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)‖
              ∂pairedEtaLogTailMeasure N :=
        norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := by
        apply integral_congr_ae
        filter_upwards
          [ae_restrict_mem (measurableSet_pairedEtaLogTailSupport N)]
            with t ht
        have hta : a < t := by
          simpa [a] using
            (pairedEtaLogTailSupport_subset_Ioi_log_odd N ht)
        rw [norm_mul, norm_pow, norm_real, Complex.norm_exp]
        norm_num [f, Complex.mul_re,
          abs_of_nonneg (sub_nonneg.mpr hta.le)]
  calc
    ‖∫ t : ℝ,
          (((t - Real.log (((2 * N + 1 : ℕ) : ℝ)) : ℝ) : ℂ) ^ k) *
            Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, f t ∂pairedEtaLogTailMeasure N := by
      simpa [a] using hnorm
    _ ≤ ∫ t : ℝ in Ioi a, f t :=
      integral_mono_measure hmeasure hnonneg hfull
    _ = pairedEtaLogLaplaceMomentCenteredTailUpper k s.re N := by
      rw [integral_sub_pow_mul_exp_neg_mul_Ioi k hs a]
      rfl

/-- A finite centered order-`k` moment, expressed arithmetically as the
binomial combination of the uncentered finite moment prefixes. -/
def pairedEtaLogLaplaceMomentCenteredPartialSum
    (k : ℕ) (s : ℂ) (a : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1),
    ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
      pairedEtaLogLaplaceMomentPartialSum j s N

/-- The binomial combination of the uncentered tail moments is exactly the
single centered tail integral. -/
theorem sum_pairedEtaLogLaplaceMoment_centeredTail_eq_integral
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (a : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
        (∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N)) =
      ∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
        ∂pairedEtaLogTailMeasure N := by
  calc
    (∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
          (∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-s * t)
            ∂pairedEtaLogTailMeasure N)) =
        ∑ j ∈ Finset.range (k + 1),
          ∫ t : ℝ,
            (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j)) *
              ((t : ℂ) ^ j * Complex.exp (-s * t))
            ∂pairedEtaLogTailMeasure N := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
        ∑ j ∈ Finset.range (k + 1),
          (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j)) *
            ((t : ℂ) ^ j * Complex.exp (-s * t))
          ∂pairedEtaLogTailMeasure N := by
      rw [integral_finsetSum]
      intro j hj
      exact (integrable_pairedEtaLogLaplaceMoment_tail j hs N).const_mul
        (((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j))
    _ = ∫ t : ℝ, (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)
          ∂pairedEtaLogTailMeasure N := by
      apply integral_congr_ae
      filter_upwards with t
      have hpoly : (((t - a : ℝ) : ℂ) ^ k) =
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) * (-(a : ℂ)) ^ (k - j) *
              (t : ℂ) ^ j := by
        rw [show ((t - a : ℝ) : ℂ) = (t : ℂ) + -(a : ℂ) by
          push_cast
          ring, add_pow]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hpoly, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- At a zero of multiplicity `m`, the full centered binomial moment of order
`m` equals the ordinary leading moment because all lower moments vanish. -/
theorem pairedEtaLogLaplaceMoment_centeredFullSum_eq_leading
    (rho : NontrivialZetaZero) (a : ℝ) :
    (∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
      (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
        (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
          pairedEtaLogLaplaceMoment j rho.1) =
      pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1 := by
  rw [Finset.sum_range_succ]
  have hzero :
      (∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            pairedEtaLogLaplaceMoment j rho.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [pairedEtaLogLaplaceMoment_eq_zero_of_lt_multiplicity rho
      (Finset.mem_range.mp hj), mul_zero]
  rw [hzero, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_self, pow_zero, one_mul]

/-- The leading moment at a nontrivial zero splits exactly into a finite
centered prefix and the literal centered support tail. -/
theorem pairedEtaLeadingLogLaplaceMoment_eq_centeredPartial_add_tail
    (rho : NontrivialZetaZero) (a : ℝ) (N : ℕ) :
    pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1 =
      pairedEtaLogLaplaceMomentCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 a N +
        ∫ t : ℝ,
          (((t - a : ℝ) : ℂ) ^ analyticZetaZeroMultiplicity rho) *
            Complex.exp (-rho.1 * t)
          ∂pairedEtaLogTailMeasure N := by
  rw [← pairedEtaLogLaplaceMoment_centeredFullSum_eq_leading rho a]
  unfold pairedEtaLogLaplaceMomentCenteredPartialSum
  calc
    (∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            pairedEtaLogLaplaceMoment j rho.1) =
      ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            (pairedEtaLogLaplaceMomentPartialSum j rho.1 N +
              ∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-rho.1 * t)
                ∂pairedEtaLogTailMeasure N) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [pairedEtaLogLaplaceMoment_eq_partialSum_add_tail j
          (NontrivialZetaZero.zero_lt_re rho) N]
    _ = (∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            pairedEtaLogLaplaceMomentPartialSum j rho.1 N) +
      ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            (∫ t : ℝ, (t : ℂ) ^ j * Complex.exp (-rho.1 * t)
              ∂pairedEtaLogTailMeasure N) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = (∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho + 1),
        (((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (-(a : ℂ)) ^ (analyticZetaZeroMultiplicity rho - j) *
            pairedEtaLogLaplaceMomentPartialSum j rho.1 N) +
        ∫ t : ℝ,
          (((t - a : ℝ) : ℂ) ^ analyticZetaZeroMultiplicity rho) *
            Complex.exp (-rho.1 * t)
          ∂pairedEtaLogTailMeasure N := by
      rw [sum_pairedEtaLogLaplaceMoment_centeredTail_eq_integral
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re rho) a N]

/-- The centered finite moment whose center is the first endpoint of the
discarded eta support tail. -/
def pairedEtaLogLaplaceMomentCutoffCenteredPartialSum (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  pairedEtaLogLaplaceMomentCenteredPartialSum k s
    (Real.log (((2 * N + 1 : ℕ) : ℝ))) N

/-- The literal order-`k` eta support tail centered at its first arithmetic
endpoint `log (2N+1)`. -/
def pairedEtaLogLaplaceMomentCutoffCenteredTail
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  ∫ t : ℝ,
    (((t - Real.log (((2 * N + 1 : ℕ) : ℝ)) : ℝ) : ℂ) ^ k) *
      Complex.exp (-s * t)
    ∂pairedEtaLogTailMeasure N

/-- The norm of the literal cutoff-centered tail obeys the centered
full-exponent envelope throughout the positive half-plane. -/
theorem norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k s N‖ ≤
      pairedEtaLogLaplaceMomentCenteredTailUpper k s.re N := by
  exact norm_integral_pairedEtaLogLaplaceMoment_centeredTail_le k hs N

/-- The exact leading-moment split specialized to the arithmetic cutoff
center `log (2N+1)`. -/
theorem pairedEtaLeadingLogLaplaceMoment_eq_cutoffCenteredPartial_add_tail
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1 =
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N +
        pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho) rho.1 N := by
  simpa only [pairedEtaLogLaplaceMomentCutoffCenteredPartialSum,
    pairedEtaLogLaplaceMomentCutoffCenteredTail] using
    pairedEtaLeadingLogLaplaceMoment_eq_centeredPartial_add_tail rho
      (Real.log (((2 * N + 1 : ℕ) : ℝ))) N

/-- The cutoff-centered finite prefix approximates the exact leading moment
with the centered full-exponent error envelope. -/
theorem norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N -
        pairedEtaLogLaplaceMoment
          (analyticZetaZeroMultiplicity rho) rho.1‖ ≤
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N := by
  have hsplit := pairedEtaLeadingLogLaplaceMoment_eq_cutoffCenteredPartial_add_tail rho N
  calc
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N -
        pairedEtaLogLaplaceMoment
          (analyticZetaZeroMultiplicity rho) rho.1‖ =
      ‖-pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ := by
        rw [hsplit]
        congr 1
        ring
    _ = ‖pairedEtaLogLaplaceMomentCutoffCenteredTail
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ := norm_neg _
    _ ≤ pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho) rho.1.re N :=
      norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_le
        (analyticZetaZeroMultiplicity rho)
        (NontrivialZetaZero.zero_lt_re rho) N

/-- The cutoff-centered finite prefixes converge to the exact first nonzero
eta moment at every nontrivial zero. -/
theorem tendsto_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦ pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
      (analyticZetaZeroMultiplicity rho) rho.1 N) atTop
      (nhds (pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦
      norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le rho N
  · exact tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho)

/-- The nonnegative centered finite lower certificate for the leading eta
gap-defect norm. -/
def pairedEtaLeadingLogGapMomentCenteredFiniteLower (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  max 0
    (‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N)

/-- The centered finite upper certificate for the leading eta gap-defect
norm. -/
def pairedEtaLeadingLogGapMomentCenteredFiniteUpper (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
      (analyticZetaZeroMultiplicity rho) rho.1 N‖ +
    pairedEtaLogLaplaceMomentCenteredTailUpper
      (analyticZetaZeroMultiplicity rho) rho.1.re N

/-- At every cutoff, the centered lower certificate is strictly smaller than
the centered upper certificate. -/
theorem pairedEtaLeadingLogGapMomentCenteredFiniteLower_lt_upper
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N <
      pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N := by
  have htail :
      0 < pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N :=
    pairedEtaLogLaplaceMomentCenteredTailUpper_pos
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) N
  unfold pairedEtaLeadingLogGapMomentCenteredFiniteLower
    pairedEtaLeadingLogGapMomentCenteredFiniteUpper
  by_cases hdiff : 0 ≤
      ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho) rho.1.re N
  · rw [max_eq_right hdiff]
    nlinarith
  · rw [max_eq_left (le_of_not_ge hdiff)]
    nlinarith [norm_nonneg
      (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho) rho.1 N)]

/-- Every centered finite lower certificate lies below the exact nonzero
leading gap-defect norm. -/
theorem pairedEtaLeadingLogGapMomentCenteredFiniteLower_le_norm_defect
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N ≤
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  unfold pairedEtaLeadingLogGapMomentCenteredFiniteLower
  apply max_le
  · exact norm_nonneg _
  · have hreverse := norm_sub_norm_le
      (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho) rho.1 N)
      (pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1)
    have htail := norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le rho N
    linarith

/-- Every centered finite upper certificate lies above the exact leading
gap-defect norm. -/
theorem norm_defect_le_pairedEtaLeadingLogGapMomentCenteredFiniteUpper
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
      pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N := by
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  unfold pairedEtaLeadingLogGapMomentCenteredFiniteUpper
  calc
    ‖pairedEtaLogLaplaceMoment
        (analyticZetaZeroMultiplicity rho) rho.1‖ =
      ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N -
        (pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
            (analyticZetaZeroMultiplicity rho) rho.1 N -
          pairedEtaLogLaplaceMoment
            (analyticZetaZeroMultiplicity rho) rho.1)‖ := by ring_nf
    _ ≤ ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
            (analyticZetaZeroMultiplicity rho) rho.1 N‖ +
          ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
              (analyticZetaZeroMultiplicity rho) rho.1 N -
            pairedEtaLogLaplaceMoment
              (analyticZetaZeroMultiplicity rho) rho.1‖ := norm_sub_le _ _
    _ ≤ ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
            (analyticZetaZeroMultiplicity rho) rho.1 N‖ +
          pairedEtaLogLaplaceMomentCenteredTailUpper
            (analyticZetaZeroMultiplicity rho) rho.1.re N := by
      linarith [norm_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_sub_le rho N]

/-- Every cutoff gives a rigorous two-sided centered enclosure of the exact
leading gap-defect norm. -/
theorem pairedEtaLeadingLogGapMoment_norm_mem_centeredFiniteEnclosure
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N ≤
        ‖pairedEtaLeadingLogGapMomentDefect rho‖ ∧
      ‖pairedEtaLeadingLogGapMomentDefect rho‖ ≤
        pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N :=
  ⟨pairedEtaLeadingLogGapMomentCenteredFiniteLower_le_norm_defect rho N,
    norm_defect_le_pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N⟩

/-- The centered lower certificates converge to the exact leading
gap-defect norm. -/
theorem tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteLower
    (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaLeadingLogGapMomentCenteredFiniteLower rho) atTop
      (nhds ‖pairedEtaLeadingLogGapMomentDefect rho‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum rho).norm
  have htail := tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)
  have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  change Tendsto (fun N : ℕ ↦ max 0
    (‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N)) atTop
    (nhds ‖pairedEtaLogLaplaceMoment
      (analyticZetaZeroMultiplicity rho) rho.1‖)
  simpa [max_eq_right (norm_nonneg (pairedEtaLogLaplaceMoment
    (analyticZetaZeroMultiplicity rho) rho.1))] using
      hzero.max (hprefix.sub htail)

/-- The centered upper certificates converge to the exact leading
gap-defect norm. -/
theorem tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteUpper
    (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho) atTop
      (nhds ‖pairedEtaLeadingLogGapMomentDefect rho‖) := by
  have hprefix := (tendsto_pairedEtaLogLaplaceMomentCutoffCenteredPartialSum rho).norm
  have htail := tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
    (analyticZetaZeroMultiplicity rho)
    (NontrivialZetaZero.zero_lt_re rho)
  rw [pairedEtaLeadingLogGapMomentDefect_eq_logLaplaceMoment]
  change Tendsto (fun N : ℕ ↦
    ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity rho) rho.1 N‖ +
      pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N) atTop
    (nhds ‖pairedEtaLogLaplaceMoment
      (analyticZetaZeroMultiplicity rho) rho.1‖)
  simpa using hprefix.add htail

/-- The centered enclosure width is bounded explicitly by twice the
full-exponent centered tail envelope. -/
theorem pairedEtaLeadingLogGapMomentCenteredFiniteEnclosure_width_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N -
        pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N ≤
      2 * pairedEtaLogLaplaceMomentCenteredTailUpper
        (analyticZetaZeroMultiplicity rho) rho.1.re N := by
  have htail : 0 ≤ pairedEtaLogLaplaceMomentCenteredTailUpper
      (analyticZetaZeroMultiplicity rho) rho.1.re N :=
    (pairedEtaLogLaplaceMomentCenteredTailUpper_pos
      (analyticZetaZeroMultiplicity rho)
      (NontrivialZetaZero.zero_lt_re rho) N).le
  unfold pairedEtaLeadingLogGapMomentCenteredFiniteUpper
    pairedEtaLeadingLogGapMomentCenteredFiniteLower
  by_cases hdiff : 0 ≤
      ‖pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
          (analyticZetaZeroMultiplicity rho) rho.1 N‖ -
        pairedEtaLogLaplaceMomentCenteredTailUpper
          (analyticZetaZeroMultiplicity rho) rho.1.re N
  · rw [max_eq_right hdiff]
    ring_nf
    exact le_rfl
  · rw [max_eq_left (le_of_not_ge hdiff)]
    linarith

/-- The width of the centered finite enclosure tends to zero. -/
theorem tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteEnclosure_width_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦
      pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho N -
        pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N)
      atTop (nhds 0) := by
  simpa using
    (tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteUpper rho).sub
      (tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteLower rho)

/-- The centered lower certificate is eventually strictly positive at every
nontrivial zero. -/
theorem eventually_pairedEtaLeadingLogGapMomentCenteredFiniteLower_pos
    (rho : NontrivialZetaZero) :
    ∀ᶠ N : ℕ in atTop, 0 < pairedEtaLeadingLogGapMomentCenteredFiniteLower rho N := by
  exact Filter.Tendsto.eventually_const_lt
    (norm_pos_iff.mpr (pairedEtaLeadingLogGapMomentDefect_ne_zero rho))
    (tendsto_pairedEtaLeadingLogGapMomentCenteredFiniteLower rho)

end
end RiemannGaussian
