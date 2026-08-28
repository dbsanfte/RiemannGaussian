import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourLocalEtaAsymptotic

/-!
# Sublinear negative critical-zeta logarithm on the selected heights

Paired eta equals the critical-line zeta value times the elementary factor
`1 - 2 * 2 ^ (-s)`.  The factor is already bounded uniformly away from zero;
here we also prove its uniform upper bound by three.  The resulting exact
logarithmic comparison transfers the checked `o(T)` negative-log estimate
from paired eta to zeta.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The elementary eta factor has norm at most three on the critical line. -/
lemma norm_pairedEtaFactor_critical_le_three (T : ℝ) :
    ‖1 - (2 : ℂ) * (2 : ℂ) ^
        (-(staticContourCriticalEndpoint T))‖ ≤ 3 := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt 2) ^ 2 = 2 := by
    rw [sq, Real.mul_self_sqrt (by norm_num)]
  have hsqrt : Real.sqrt 2 ≤ 2 := by nlinarith
  calc
    ‖1 - (2 : ℂ) * (2 : ℂ) ^
        (-(staticContourCriticalEndpoint T))‖ ≤
        ‖(1 : ℂ)‖ +
          ‖(2 : ℂ) * (2 : ℂ) ^
            (-(staticContourCriticalEndpoint T))‖ := norm_sub_le _ _
    _ = 1 + Real.sqrt 2 := by
      rw [norm_one]
      simpa [staticContourCriticalEndpoint] using
        norm_two_mul_two_cpow_neg_critical T
    _ ≤ 3 := by linarith

/-- At each quantitative endpoint, the negative zeta logarithm is bounded by
the negative paired-eta logarithm plus the fixed factor penalty `log 3`. -/
lemma neg_log_norm_riemannZeta_critical_quantitative_le_eta_add_log_three
    (n : ℕ) :
    -Real.log
        ‖riemannZeta
          (staticContourCriticalEndpoint
            (quantitativeSpectralBoundaryTruncation n))‖ ≤
      -Real.log
          ‖pairedEtaCore
            (staticContourCriticalEndpoint
              (quantitativeSpectralBoundaryTruncation n))‖ +
        Real.log 3 := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let s : ℂ := staticContourCriticalEndpoint T
  let e : ℂ := 1 - (2 : ℂ) * (2 : ℂ) ^ (-s)
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have heta := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := s) (by simp [s, staticContourCriticalEndpoint])
    (by simpa [s, staticContourCriticalEndpoint] using hT)
  have heLower : (1 / 3 : ℝ) ≤ ‖e‖ := by
    simpa [e, s, staticContourCriticalEndpoint] using
      one_third_le_norm_pairedEtaFactor_critical T
  have hePos : 0 < ‖e‖ :=
    (by norm_num : (0 : ℝ) < 1 / 3).trans_le heLower
  have heUpper : ‖e‖ ≤ 3 := by
    simpa [e, s] using norm_pairedEtaFactor_critical_le_three T
  have hzeta : riemannZeta s ≠ 0 := by
    simpa [s, T] using
      riemannZeta_staticContourCriticalEndpoint_quantitative_ne_zero n
  have hzetaPos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hzeta
  have hlogFactor : Real.log ‖e‖ ≤ Real.log 3 :=
    Real.log_le_log hePos heUpper
  have hlogEta :
      Real.log ‖pairedEtaCore s‖ =
        Real.log ‖e‖ + Real.log ‖riemannZeta s‖ := by
    rw [heta]
    change Real.log ‖e * riemannZeta s‖ = _
    rw [norm_mul, Real.log_mul hePos.ne' hzetaPos.ne']
  change -Real.log ‖riemannZeta s‖ ≤
    -Real.log ‖pairedEtaCore s‖ + Real.log 3
  linarith

/-- The negative part of the critical-line zeta logarithm, divided by the
selected height, tends to zero. -/
theorem tendsto_criticalZeta_log_negativePart_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        max 0
            (-Real.log
              ‖riemannZeta
                (staticContourCriticalEndpoint
                  (quantitativeSpectralBoundaryTruncation n))‖) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let E : ℕ → ℝ := fun n =>
    max 0
      (-Real.log
        ‖pairedEtaCore (staticContourCriticalEndpoint (T n))‖)
  let Z : ℕ → ℝ := fun n =>
    max 0
      (-Real.log
        ‖riemannZeta (staticContourCriticalEndpoint (T n))‖)
  have hT : Tendsto T atTop atTop :=
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hTpos (n : ℕ) : 0 < T n :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have heta : Tendsto (fun n : ℕ => E n / T n) atTop (nhds 0) := by
    simpa [E, T] using
      tendsto_pairedEtaCore_critical_log_negativePart_div_quantitative_zero
  have hconstant : Tendsto
      (fun n : ℕ => Real.log 3 / T n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hT
  have hupperLimit : Tendsto
      (fun n : ℕ => (E n + Real.log 3) / T n) atTop (nhds 0) := by
    have hsum : Tendsto
        (fun n : ℕ => E n / T n + Real.log 3 / T n)
        atTop (nhds 0) := by
      simpa using heta.add hconstant
    refine hsum.congr' (Eventually.of_forall fun n => ?_)
    field_simp [(hTpos n).ne']
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      div_nonneg (le_max_left _ _) (hTpos n).le
  · exact Eventually.of_forall fun n => by
      have hraw :=
        neg_log_norm_riemannZeta_critical_quantitative_le_eta_add_log_three n
      have hlogThree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hZE : Z n ≤ E n + Real.log 3 := by
        apply max_le
        · exact add_nonneg (by dsimp [E]; exact le_max_left _ _) hlogThree
        · calc
            -Real.log
                ‖riemannZeta (staticContourCriticalEndpoint (T n))‖ ≤
                -Real.log
                    ‖pairedEtaCore (staticContourCriticalEndpoint (T n))‖ +
                  Real.log 3 := by simpa [T] using hraw
            _ ≤ E n + Real.log 3 := by
              have hetaMax :
                  -Real.log
                      ‖pairedEtaCore (staticContourCriticalEndpoint (T n))‖ ≤
                    E n := le_max_right _ _
              linarith
      exact div_le_div_of_nonneg_right hZE (hTpos n).le
  · simpa [Z, T] using hupperLimit

end

end RiemannGaussian
