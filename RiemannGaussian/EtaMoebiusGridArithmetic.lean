import RiemannGaussian.EtaMoebiusTrialHead
import RiemannGaussian.EtaTranslatedFiniteIntervals

/-!
# Exact signed arithmetic of the full physical-grid Möbius combination

Every eta interval is the difference of its two original causal steps.
Discrete summation by parts evaluates the complete coefficient sum against
each step at the rounded arithmetic primitive. The resulting signed
finite formula is the actual combination on the entire specified time
range, including the exterior of the compact target.
-/

open Complex Set

namespace RiemannGaussian

noncomputable section

private theorem indicator_Ioc_eq_steps {l u : ℝ} (hlu : l ≤ u) (t : ℝ) :
    (Ioc l u).indicator (fun _ ↦ (1 : ℝ)) t =
      (if l < t then 1 else 0) - (if u < t then 1 else 0) := by
  by_cases hl : l < t
  · by_cases hu : u < t
    · simp [Set.indicator, mem_Ioc, hl, hu.not_ge, hu]
    · simp [Set.indicator, mem_Ioc, hl, hu, le_of_not_gt hu]
  · have hu : ¬ u < t := by linarith
    simp [Set.indicator, mem_Ioc, hl, hu]

/-- Both original endpoints of each eta interval survive as a signed pair of causal steps. -/
theorem pairedEtaTranslatedInterval_indicator_eq_steps (a t : ℝ) (n : ℕ) :
    (pairedEtaTranslatedInterval a n).indicator (fun _ ↦ (1 : ℝ)) t =
      (if a < t - Real.log (2 * n + 1 : ℝ) then 1 else 0) -
        (if a < t - Real.log (2 * n + 2 : ℝ) then 1 else 0) := by
  have hlog : Real.log (2 * n + 1 : ℝ) ≤ Real.log (2 * n + 2 : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  unfold pairedEtaTranslatedInterval
  rw [indicator_Ioc_eq_steps (by linarith)]
  congr 2 <;> apply propext <;> constructor <;> intro h <;> linarith

/-- The exact paired arithmetic primitive formula, retaining every odd and even endpoint and the full physical-grid rounding. -/
def pairedEtaMoebiusTrialArithmeticPrefix (N d M : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (pairedEtaMoebiusTrialPrimitive M w
      (pairedEtaMoebiusTrialHeadCoordinate d (t - Real.log (2 * n + 1 : ℝ))) -
    pairedEtaMoebiusTrialPrimitive M w
      (pairedEtaMoebiusTrialHeadCoordinate d (t - Real.log (2 * n + 2 : ℝ))))

/-- The complete actual Möbius combination is the signed arithmetic primitive formula on the whole original eta cutoff interval, not just on the target support. -/
theorem pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix (N d M : ℕ) (w : ℕ → ℝ)
    {t : ℝ} (ht : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaMoebiusTrialGridCombination d M w t =
      (pairedEtaMoebiusTrialArithmeticPrefix N d M w t : ℂ) := by
  have hreal : pairedEtaMoebiusTrialGridCombination d M w t =
      ((∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j *
        pairedEtaTranslatedColour (pairedEtaMoebiusTrialGridPoint d (j.1 + 1)) t) : ℝ) := by
    simp [pairedEtaMoebiusTrialGridCombination, pairedEtaTranslatedCombination]
  rw [hreal]
  congr 1
  calc
    _ = ∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j *
        ∑ n ∈ Finset.range N,
          (pairedEtaTranslatedInterval (pairedEtaMoebiusTrialGridPoint d (j.1 + 1)) n).indicator
            (fun _ ↦ (1 : ℝ)) t := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pairedEtaTranslatedColour_eq_prefix (pairedEtaMoebiusTrialGridPoint_nonneg _ _) ht]
      rfl
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [pairedEtaTranslatedInterval_indicator_eq_steps, mul_sub, Finset.sum_sub_distrib,
        pairedEtaMoebiusTrialGridStep_sum]
      simp only [pairedEtaMoebiusTrialArithmeticPrefix, Finset.sum_sub_distrib]

/-- The exact arithmetic prefix retains the unchanged complex residual on every part of the original finite time range. -/
theorem pairedEtaMoebiusTrialResidual_eq_arithmeticPrefix (N d M : ℕ) (w : ℕ → ℝ)
    {t : ℝ} (ht : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaProjectionHead t - pairedEtaMoebiusTrialGridCombination d M w t =
      pairedEtaProjectionHead t - (pairedEtaMoebiusTrialArithmeticPrefix N d M w t : ℂ) := by
  rw [pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix N d M w ht]

end

end RiemannGaussian
