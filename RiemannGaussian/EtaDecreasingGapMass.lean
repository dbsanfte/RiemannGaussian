import RiemannGaussian.EtaCurrentFullHeatComparison

/-!
# Arithmetic balance of decreasing weights on eta support and gap

Consecutive logarithmic unit intervals have decreasing lengths. A
nonnegative decreasing test therefore puts at least as much mass on each
interval as on the next. Summing the actual alternating intervals traps
the support/gap imbalance by the mass of the first support interval.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Consecutive logarithmic unit intervals have decreasing lengths. -/
theorem logSuccessorInterval_width_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 2) - Real.log (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) hx.ne']
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity) hx).2
  nlinarith

/-- Every nonnegative decreasing integrable test gives decreasing mass
to consecutive actual logarithmic unit intervals. -/
theorem integral_logSuccessorInterval_le {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0))
    (hnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioc (Real.log (x + 1)) (Real.log (x + 2)), f t) ≤
      ∫ t in Ioc (Real.log x) (Real.log (x + 1)), f t := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hLa : 0 ≤ Real.log x := Real.log_nonneg hx
  have hLb : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hab : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hbc : Real.log (x + 1) ≤ Real.log (x + 2) := Real.log_le_log (by positivity) (by linarith)
  have hi₁ : IntegrableOn f (Ioc (Real.log x) (Real.log (x + 1))) :=
    hf.mono_set fun t ht ↦ hLa.trans_lt ht.1
  have hi₂ : IntegrableOn f (Ioc (Real.log (x + 1)) (Real.log (x + 2))) :=
    hf.mono_set fun t ht ↦ hLb.trans_lt ht.1
  have hupper : (∫ t in Ioc (Real.log (x + 1)) (Real.log (x + 2)), f t) ≤
      (Real.log (x + 2) - Real.log (x + 1)) * f (Real.log (x + 1)) := by
    calc
      _ ≤ ∫ _t in Ioc (Real.log (x + 1)) (Real.log (x + 2)), f (Real.log (x + 1)) := by
        apply integral_mono_ae hi₂ (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hanti hLb (hLb.trans ht.1.le) ht.1.le
      _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hbc, smul_eq_mul]
  have hlower : (Real.log (x + 1) - Real.log x) * f (Real.log (x + 1)) ≤
      ∫ t in Ioc (Real.log x) (Real.log (x + 1)), f t := by
    calc
      _ = ∫ _t in Ioc (Real.log x) (Real.log (x + 1)), f (Real.log (x + 1)) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _) hi₁
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hanti (hLa.trans ht.1.le) hLb ht.2
  exact hupper.trans ((mul_le_mul_of_nonneg_right (logSuccessorInterval_width_le hx0)
    (hnonneg _ hLb)).trans hlower)

/-- A decreasing nonnegative test gives each actual gap at most the mass
of its preceding eta support interval. -/
theorem integral_gapInterval_le_supportInterval {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0))
    (hnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) (n : ℕ) :
    (∫ t in pairedEtaLogGapInterval n, f t) ≤ ∫ t in pairedEtaLogInterval n, f t := by
  have hx : (1 : ℝ) ≤ 2 * n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  simpa only [pairedEtaLogGapInterval, pairedEtaLogInterval, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num,
    show (1 : ℝ) + 2 = 3 by norm_num] using integral_logSuccessorInterval_le hf hanti hnonneg hx

/-- A decreasing nonnegative test gives the following eta support
interval at most the mass of the actual gap. -/
theorem integral_supportInterval_succ_le_gapInterval {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0))
    (hnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) (n : ℕ) :
    (∫ t in pairedEtaLogInterval (n + 1), f t) ≤ ∫ t in pairedEtaLogGapInterval n, f t := by
  have hx : (1 : ℝ) ≤ 2 * n + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  simpa only [pairedEtaLogInterval, pairedEtaLogGapInterval, Nat.cast_add, Nat.cast_one,
    mul_add, mul_one, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num,
    show (2 : ℝ) + 2 = 4 by norm_num] using integral_logSuccessorInterval_le hf hanti hnonneg hx

/-- The actual support and gap masses of a decreasing nonnegative test
differ by at most its first support-interval mass. -/
theorem pairedEta_decreasing_support_gap_balance {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0))
    (hnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) :
    (∫ t, f t ∂pairedEtaLogGapMeasure) ≤ (∫ t, f t ∂pairedEtaLogMeasure) ∧
    (∫ t, f t ∂pairedEtaLogMeasure) ≤
      (∫ t in pairedEtaLogInterval 0, f t) + (∫ t, f t ∂pairedEtaLogGapMeasure) := by
  have hiS := Integrable.mono_measure hf pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
  have hiG := Integrable.mono_measure hf pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero
  rw [pairedEtaLogMeasure_eq_sum_restrict] at hiS
  rw [pairedEtaLogGapMeasure_eq_sum_restrict] at hiG
  have hs : Summable (fun n : ℕ ↦ ∫ t in pairedEtaLogInterval n, f t) :=
    hiS.summable_integral.of_norm_bounded fun _ ↦ norm_integral_le_integral_norm _
  have hg : Summable (fun n : ℕ ↦ ∫ t in pairedEtaLogGapInterval n, f t) :=
    hiG.summable_integral.of_norm_bounded fun _ ↦ norm_integral_le_integral_norm _
  rw [pairedEtaLogMeasure_eq_sum_restrict, pairedEtaLogGapMeasure_eq_sum_restrict,
    integral_sum_measure hiS, integral_sum_measure hiG]
  constructor
  · exact hg.tsum_le_tsum (integral_gapInterval_le_supportInterval hf hanti hnonneg) hs
  · rw [hs.tsum_eq_zero_add]
    apply add_le_add le_rfl
    exact ((summable_nat_add_iff 1).2 hs).tsum_le_tsum
      (integral_supportInterval_succ_le_gapInterval hf hanti hnonneg) hg

/-- The first support mass is at most its width times the value at zero. -/
theorem pairedEta_first_support_mass_le {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0)) :
    (∫ t in pairedEtaLogInterval 0, f t) ≤ Real.log 2 * f 0 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have heq : pairedEtaLogInterval 0 = Ioc 0 (Real.log 2) := by simp [pairedEtaLogInterval]
  rw [heq]
  calc
    _ ≤ ∫ _t in Ioc 0 (Real.log 2), f 0 := by
      apply integral_mono_ae (hf.mono_set fun _ ht ↦ ht.1) (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hanti (by simp) ht.1.le ht.1.le
    _ = _ := by rw [setIntegral_const, Real.volume_real_Ioc_of_le hlog, smul_eq_mul, sub_zero]

/-- A decreasing nonnegative test sees one half of its positive-time
mass in the eta gap, with error controlled by the first interval. -/
theorem pairedEta_decreasing_gap_mass_bounds {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hanti : AntitoneOn f (Ici 0))
    (hnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t) :
    ((∫ t in Ioi 0, f t) - Real.log 2 * f 0) / 2 ≤ (∫ t, f t ∂pairedEtaLogGapMeasure) ∧
    (∫ t, f t ∂pairedEtaLogGapMeasure) ≤ (∫ t in Ioi 0, f t) / 2 := by
  obtain ⟨hGS, hSG⟩ := pairedEta_decreasing_support_gap_balance hf hanti hnonneg
  have hfirst := pairedEta_first_support_mass_le hf hanti
  have he : (∫ t in Ioi 0, f t) = (∫ t, f t ∂pairedEtaLogMeasure) + (∫ t, f t ∂pairedEtaLogGapMeasure) := by
    rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure]
    exact integral_add_measure
      (Integrable.mono_measure hf pairedEtaLogMeasure_le_volume_restrict_Ioi_zero)
      (Integrable.mono_measure hf pairedEtaLogGapMeasure_le_volume_restrict_Ioi_zero)
  constructor <;> linarith

end

end RiemannGaussian
