import RiemannGaussian.EtaNormalizedHeatKernel

/-!
# Independent finite cutoffs for actual eta support/gap heat

Both time variables are restricted at a common cutoff `L`, which remains
independent of the positive heat width. The exact omitted signed integral is
retained. A full-line tilted Gaussian calculation bounds its norm uniformly
over the real phase by `exp(sigma^2 h^2) exp(-2 sigma L) / sigma`.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The box retaining both logarithmic times below a common cutoff. -/
def pairedEtaHeatCutoffBox (L : ℝ) : Set (ℝ × ℝ) := (Iic L) ×ˢ (Iic L)

/-- The actual support/gap heat transfer with both positive times cut off at `L`. -/
def pairedEtaSupportGapGaussianLeakageCutoff (sigma h : ℝ) (phi : ℝ → ℝ) (L : ℝ) : ℝ :=
  ∫ p in pairedEtaHeatCutoffBox L, pairedEtaSupportGapHeatKernel sigma h phi p
    ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- The finite cutoff is exactly integration over the literal square `(0,L]^2`. -/
theorem pairedEtaSupportGapGaussianLeakageCutoff_eq_Ioc (sigma h : ℝ) (phi : ℝ → ℝ) (L : ℝ) :
    pairedEtaSupportGapGaussianLeakageCutoff sigma h phi L =
      ∫ p, pairedEtaSupportGapHeatKernel sigma h phi p
        ∂((volume.restrict (Ioc 0 L)).prod (volume.restrict (Ioc 0 L))) := by
  have hR : (volume.restrict (Ioi (0 : ℝ))).restrict (Iic L) = volume.restrict (Ioc 0 L) := by
    rw [Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  have hp : (volume.restrict (Ioc (0 : ℝ) L)).prod (volume.restrict (Ioc 0 L)) =
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))).restrict (pairedEtaHeatCutoffBox L) := by
    rw [← hR, Measure.prod_restrict]
    rfl
  rw [hp]
  rfl

/-- The exact omitted signed contribution is retained before its norm estimate. -/
theorem pairedEtaSupportGapGaussianLeakage_sub_cutoff_eq_tail {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi : ℝ → ℝ} (hphi : Measurable phi) (L : ℝ) :
    pairedEtaSupportGapGaussianLeakage sigma h phi -
      pairedEtaSupportGapGaussianLeakageCutoff sigma h phi L =
      ∫ p in (pairedEtaHeatCutoffBox L)ᶜ, pairedEtaSupportGapHeatKernel sigma h phi p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hbox : MeasurableSet (pairedEtaHeatCutoffBox L) := measurableSet_Iic.prod measurableSet_Iic
  have hi := integrable_pairedEtaSupportGapHeatKernel hsigma hh hphi
  have he := integral_add_compl hbox hi
  unfold pairedEtaSupportGapGaussianLeakage pairedEtaSupportGapGaussianLeakageCutoff
  linarith

/-- One ordered large-time tail is bounded by completing the square in the
other time variable and evaluating the remaining exponential mass. -/
theorem integral_etaTiltedHeatEnvelope_tail_le {sigma h L : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (hL : 0 ≤ L) :
    (∫ p : ℝ × ℝ, {p : ℝ × ℝ | L < p.1}.indicator (etaTiltedHeatEnvelope sigma h) p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) ≤
      Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * L) / (2 * sigma) := by
  let S : Set (ℝ × ℝ) := {p | L < p.1}
  let H := etaTiltedHeatEnvelope sigma h
  let g : ℝ → ℝ := fun t ↦ ∫ u in Ioi 0, H (t, u)
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_fst
  have hiH := integrable_etaTiltedHeatEnvelope hsigma hh
  have hiT : Integrable (S.indicator H)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := hiH.indicator hS
  have hiG : IntegrableOn g (Ioi 0) := hiH.integral_prod_left
  have hfun : (fun t : ℝ ↦ ∫ u in Ioi 0, S.indicator H (t, u)) = (Ioi L).indicator g := by
    funext t
    by_cases ht : L < t <;> simp [S, g, ht]
  have hsub : Ioi L ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hL
  have heq : (∫ p : ℝ × ℝ, S.indicator H p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) = ∫ t in Ioi L, g t := by
    rw [integral_prod _ hiT, hfun, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr hsub]
  change (∫ p : ℝ × ℝ, S.indicator H p
    ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) ≤ _
  rw [heq]
  have he := integrableOn_exp_mul_Ioi (a := -(2 * sigma)) (by linarith) L
  calc
    (∫ t in Ioi L, g t) ≤ ∫ t in Ioi L,
        Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * t) := by
      apply integral_mono_ae (hiG.mono_set hsub) (he.const_mul _)
      exact Eventually.of_forall fun t ↦ integral_Ioi_etaTiltedHeatEnvelope_slice_le hh sigma t
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq]
      ring

/-- Truncation of both actual time variables has an explicit error uniform
in the phase, with heat width and cutoff kept independent. -/
theorem pairedEtaSupportGapGaussianLeakage_cutoff_error_le {sigma h L : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) (hL : 0 ≤ L)
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    |pairedEtaSupportGapGaussianLeakage sigma h phi -
      pairedEtaSupportGapGaussianLeakageCutoff sigma h phi L| ≤
      Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * L) / sigma := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  let H := etaTiltedHeatEnvelope sigma h
  let F := pairedEtaSupportGapHeatKernel sigma h phi
  let S : Set (ℝ × ℝ) := {p | L < p.1}
  let T : Set (ℝ × ℝ) := {p | L < p.2}
  let U := S.indicator H
  let V := T.indicator H
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_fst
  have hT : MeasurableSet T := measurableSet_lt measurable_const measurable_snd
  have hbox : MeasurableSet (pairedEtaHeatCutoffBox L) := measurableSet_Iic.prod measurableSet_Iic
  have hiH : Integrable H mu := integrable_etaTiltedHeatEnvelope hsigma hh
  have hiU : Integrable U mu := hiH.indicator hS
  have hiV : Integrable V mu := hiH.indicator hT
  have hmajor : ∀ p : ℝ × ℝ, ‖(pairedEtaHeatCutoffBox L)ᶜ.indicator F p‖ ≤ U p + V p := by
    intro p
    have hn : ‖F p‖ ≤ H p := norm_pairedEtaSupportGapHeatKernel_le_envelope hh sigma phi p
    have hp : 0 ≤ H p := (etaTiltedHeatEnvelope_pos hh sigma p).le
    have hUpos : 0 ≤ U p := by
      by_cases hm : p ∈ S <;> simp [U, hm, hp]
    have hVpos : 0 ≤ V p := by
      by_cases hm : p ∈ T <;> simp [V, hm, hp]
    by_cases hboxmem : p ∈ pairedEtaHeatCutoffBox L
    · rw [Set.indicator_of_notMem (show p ∉ (pairedEtaHeatCutoffBox L)ᶜ by simpa), norm_zero]
      exact add_nonneg hUpos hVpos
    · rw [Set.indicator_of_mem (show p ∈ (pairedEtaHeatCutoffBox L)ᶜ from hboxmem)]
      have hor : L < p.1 ∨ L < p.2 := by
        simpa only [pairedEtaHeatCutoffBox, mem_prod, mem_Iic, not_and_or, not_le] using hboxmem
      rcases hor with ht | hu
      · have hU : U p = H p := Set.indicator_of_mem (show p ∈ S from ht) H
        rw [hU]
        exact hn.trans (le_add_of_nonneg_right hVpos)
      · have hV : V p = H p := Set.indicator_of_mem (show p ∈ T from hu) H
        rw [hV]
        exact hn.trans (le_add_of_nonneg_left hUpos)
  have hswap : V = (fun p : ℝ × ℝ ↦ U p.swap) := by
    funext p
    simp only [U, V, S, T, Set.indicator_apply, mem_ofPred_eq]
    change (if L < p.2 then H p else 0) = (if L < p.2 then H p.swap else 0)
    dsimp [H]
    rw [etaTiltedHeatEnvelope_swap]
  have hintSwap : (∫ p, V p ∂mu) = ∫ p, U p ∂mu := by
    rw [hswap]
    exact integral_prod_swap U
  have hb := norm_integral_le_of_norm_le (hiU.add hiV) (Eventually.of_forall hmajor)
  simp only [Real.norm_eq_abs, Pi.add_apply] at hb
  rw [integral_add hiU hiV, hintSwap] at hb
  have htail : (∫ p, U p ∂mu) ≤
      Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * L) / (2 * sigma) :=
    integral_etaTiltedHeatEnvelope_tail_le hsigma hh hL
  rw [pairedEtaSupportGapGaussianLeakage_sub_cutoff_eq_tail hsigma hh hphi L,
    ← integral_indicator hbox.compl]
  calc
    _ ≤ (∫ p, U p ∂mu) + ∫ p, U p ∂mu := hb
    _ ≤ 2 * (Real.exp (sigma ^ 2 * h ^ 2) * Real.exp (-(2 * sigma) * L) / (2 * sigma)) := by
      linarith
    _ = _ := by field_simp

/-- A logarithmically growing critical cutoff has only an order-`h` error,
uniformly over the complete real phase function. -/
theorem pairedEtaSupportGapGaussianLeakage_log_cutoff_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) {phi : ℝ → ℝ} (hphi : Measurable phi) :
    |pairedEtaSupportGapGaussianLeakage (1 / 2) h phi -
      pairedEtaSupportGapGaussianLeakageCutoff (1 / 2) h phi (Real.log (1 / h))| ≤
        (2 * Real.exp (1 / 4)) * h := by
  have hL : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((le_div_iff₀ hh).2 (by linarith))
  have hb := pairedEtaSupportGapGaussianLeakage_cutoff_error_le (sigma := 1 / 2) (by norm_num) hh hL hphi
  have he : Real.exp (-(2 * (1 / 2)) * Real.log (1 / h)) = h := by
    norm_num only [mul_one_div_cancel, one_div, neg_one_mul, Real.log_inv, neg_neg]
    exact Real.exp_log hh
  rw [he] at hb
  have hgauss : Real.exp ((1 / 2) ^ 2 * h ^ 2) ≤ Real.exp (1 / 4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_right hgauss hh.le
  apply hb.trans
  nlinarith

/-- The actual finite time square at `L = log(1/h)` retains the complete
critical phase profile with a constant independent of the ordinate. -/
theorem pairedEtaSupportGapGaussianLeakageCutoff_uniform_error_le {h : ℝ}
    (hh : 0 < h) (hhone : h ≤ 1) (gamma : ℝ) :
    |pairedEtaSupportGapGaussianLeakageCutoff (1 / 2) h (fun t ↦ gamma * t) (Real.log (1 / h)) -
      h * Real.log (1 / h) * pairedEtaHeatPhaseProfile (h * gamma)| ≤
        (32 + 2 * Real.exp (1 / 4)) * h := by
  have hphi : Measurable (fun t : ℝ ↦ gamma * t) := measurable_const.mul measurable_id
  have hc := pairedEtaSupportGapGaussianLeakage_log_cutoff_error_le hh hhone hphi
  have hu := pairedEtaSupportGapGaussianLeakage_uniform_error_le hh hhone gamma
  rw [abs_sub_comm] at hc
  calc
    _ ≤ |pairedEtaSupportGapGaussianLeakageCutoff (1 / 2) h (fun t ↦ gamma * t) (Real.log (1 / h)) -
          pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ gamma * t)| +
        |pairedEtaSupportGapGaussianLeakage (1 / 2) h (fun t ↦ gamma * t) -
          h * Real.log (1 / h) * pairedEtaHeatPhaseProfile (h * gamma)| := abs_sub_le _ _ _
    _ ≤ (2 * Real.exp (1 / 4)) * h + 32 * h := add_le_add hc hu
    _ = _ := by ring

end

end RiemannGaussian
