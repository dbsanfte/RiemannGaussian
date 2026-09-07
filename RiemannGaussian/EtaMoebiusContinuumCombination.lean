import RiemannGaussian.EtaMoebiusContinuumPrimitive

/-!
# The actual signed arithmetic limit of the complete Möbius combinations

The continuum combination is a locally finite odd/even primitive sum.
Every original finite-grid combination converges to it at every time,
including all arithmetic endpoints. Measurability and the complete
dimension-independent norm bound are inherited from the actual carriers.
This identifies a candidate, not convergence of its target residual as the
arithmetic cutoff grows.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The complete signed arithmetic continuum combination, with both original endpoint channels retained and only finitely many nonzero terms at every time. -/
def pairedEtaMoebiusContinuumCombination (M : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ((∑' n : ℕ,
    (pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 1 : ℝ))) -
      pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 2 : ℝ))))) : ℝ)

private theorem continuum_primitive_eq_zero_past_cutoff (M : ℕ) (w : ℕ → ℝ)
    {N n : ℕ} (hn : N ≤ n) {t : ℝ} (ht : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 1 : ℝ))) = 0 ∧
      pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 2 : ℝ))) = 0 := by
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ho : Real.log (2 * N + 1 : ℝ) ≤ Real.log (2 * n + 1 : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  have he : Real.log (2 * N + 1 : ℝ) ≤ Real.log (2 * n + 2 : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  constructor <;> apply pairedEtaMoebiusContinuumPrimitive_eq_zero_of_le_one <;>
    apply Real.exp_le_one_iff.mpr <;> linarith

/-- The complete signed continuum combination is exactly its original odd/even finite prefix on the entire specified time interval. -/
theorem pairedEtaMoebiusContinuumCombination_eq_prefix (N M : ℕ) (w : ℕ → ℝ)
    {t : ℝ} (ht : t ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaMoebiusContinuumCombination M w t =
      ((∑ n ∈ Finset.range N,
        (pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 1 : ℝ))) -
          pairedEtaMoebiusContinuumPrimitive M w (Real.exp (t - Real.log (2 * n + 2 : ℝ))))) : ℝ) := by
  unfold pairedEtaMoebiusContinuumCombination
  congr 1
  apply tsum_eq_sum
  intro n hn
  have hz := continuum_primitive_eq_zero_past_cutoff M w (by simpa using hn) ht
  rw [hz.1, hz.2, sub_self]

/-- At fixed arithmetic cutoff and weights, the entire actual finite-grid carrier converges to the explicit signed continuum arithmetic at every real time. -/
theorem pairedEtaMoebiusTrialGridCombination_tendsto_continuum (M : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    Tendsto (fun d : ℕ ↦ pairedEtaMoebiusTrialGridCombination d M w t) atTop
      (𝓝 (pairedEtaMoebiusContinuumCombination M w t)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp t)
  have ht : t ≤ Real.log (2 * N + 1 : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos t)
      (show Real.exp t ≤ (2 * N + 1 : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) N])
    simpa only [Real.log_exp] using h
  simp_rw [pairedEtaMoebiusTrialGridCombination_eq_arithmeticPrefix N _ M w ht]
  rw [pairedEtaMoebiusContinuumCombination_eq_prefix N M w ht]
  apply Complex.continuous_ofReal.continuousAt.tendsto.comp
  apply tendsto_finsetSum
  intro n _
  exact (pairedEtaMoebiusTrialPrimitive_tendsto_continuum M w (t - Real.log (2 * n + 1 : ℝ))).sub
    (pairedEtaMoebiusTrialPrimitive_tendsto_continuum M w (t - Real.log (2 * n + 2 : ℝ)))

/-- Every original finite-grid arithmetic carrier is measurable on the complete real axis. -/
theorem measurable_pairedEtaMoebiusTrialGridCombination (d M : ℕ) (w : ℕ → ℝ) :
    Measurable (pairedEtaMoebiusTrialGridCombination d M w) :=
  measurable_pairedEtaTranslatedCombination
      (fun j : Fin d ↦ pairedEtaMoebiusTrialGridPoint d (j.1 + 1))
      (fun j ↦ (pairedEtaMoebiusTrialCoefficient d M w j : ℂ))

/-- The actual signed continuum combination is measurable as the everywhere pointwise limit of the original measurable carriers. -/
theorem measurable_pairedEtaMoebiusContinuumCombination (M : ℕ) (w : ℕ → ℝ) :
    Measurable (pairedEtaMoebiusContinuumCombination M w) :=
  measurable_of_tendsto_metrizable (fun d ↦ measurable_pairedEtaMoebiusTrialGridCombination d M w)
    (tendsto_pi_nhds.mpr (pairedEtaMoebiusTrialGridCombination_tendsto_continuum M w))

/-- The complete original carrier has the same arithmetic mass bound at every grid size. -/
theorem norm_pairedEtaMoebiusTrialGridCombination_le (d M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (t : ℝ) :
    ‖pairedEtaMoebiusTrialGridCombination d M w t‖ ≤ 2 * M := by
  apply (norm_pairedEtaTranslatedCombination_le _ _ t).trans
  simpa only [Complex.norm_real, Real.norm_eq_abs] using pairedEtaMoebiusTrialCoefficient_sum_abs_le d M hw

/-- The complete limiting arithmetic carrier inherits the same bound on the entire real time axis. -/
theorem norm_pairedEtaMoebiusContinuumCombination_le (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (t : ℝ) :
    ‖pairedEtaMoebiusContinuumCombination M w t‖ ≤ 2 * M :=
  le_of_tendsto (pairedEtaMoebiusTrialGridCombination_tendsto_continuum M w t).norm
    (Eventually.of_forall fun d ↦ norm_pairedEtaMoebiusTrialGridCombination_le d M hw t)

end

end RiemannGaussian
