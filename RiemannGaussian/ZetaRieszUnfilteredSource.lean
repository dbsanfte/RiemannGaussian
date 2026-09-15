/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaExposedPrimeFilter

/-!
# The actual arithmetic source without an isolating polynomial

The original Riesz band differs from the complete prime filter by an
independently vanishing error for every fixed polynomial. At exposed zeros,
the constant filter one retains the full negative multiplicity source,
including all existing actual semiprime and earlier arithmetic deletions.
The independent whole-residual floor remains an explicit open premise.
-/

namespace RiemannGaussian.ZetaRieszUnfilteredSource
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedPrimeFilter

/-- The original Riesz band differs from the complete prime response
by an independently vanishing normalized error for every fixed filter.
No pole-annihilation or hypothetical-zero premise is required. -/
theorem tendsto_actual_riesz_band_sub_prime (P : Polynomial ℂ) (y : ℝ)
    (hy : 1 < |y|) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N)) P N y -
        zetaPrimeLogFilter P N (3 / 2 + Complex.I * y))) atTop (𝓝 0) := by
  let L := SquarefreeVaughanLogSource.length u
  have huc : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hu.le] using hu1
  have hp := tendsto_zetaProperPrimePowerFilter_mul_pow P y (a := (u : ℂ)) huc
  have hs := SquarefreeVaughanBudget.tendsto_small_mixture_of_budget P y hy hu
    (fun N => VaughanLogAverage.cutoffPairs (L N))
    (fun N => VaughanLogAverage.cellWeight (L N)) (fun _ => Prod.fst) (fun _ => Prod.snd)
    (fun N q _ => VaughanLogAverage.cellWeight_nonneg (SquarefreeVaughanLogSource.length_pos u N) q)
    (SquarefreeVaughanLogSource.tendsto_average_budget hu hu1)
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one huc).comp (tendsto_add_atTop_nat 1)
  have he := hpow.mul (tendsto_zetaDominatedFilter_sub_band
    (fun N => SquarefreeVaughanLogSource.coefficient (L N))
    (fun N => SquarefreeVaughanLogSource.norm_coefficient_le (SquarefreeVaughanLogSource.length_pos u N)) P y)
  simp only [mul_zero] at he
  have h := ((hp.neg).sub hs).sub he
  simp only [neg_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hm := SquarefreeVaughanBudget.hasSum_mixture (VaughanLogAverage.cutoffPairs (L N))
    (VaughanLogAverage.cellWeight (L N)) Prod.fst Prod.snd
    (VaughanLogAverage.sum_cellWeight (SquarefreeVaughanLogSource.length_pos u N)) P N
    (by norm_num : 1 < (3 / 2 + Complex.I * (y : ℂ)).re)
  have hid : zetaArithmeticFilter (SquarefreeVaughanLogSource.coefficient (L N)) P N
      (3 / 2 + Complex.I * y) =
      zetaPrimeLogFilter P N (3 / 2 + Complex.I * y) -
        zetaProperPrimePowerFilter P N (3 / 2 + Complex.I * y) -
        ∑ q ∈ VaughanLogAverage.cutoffPairs (L N), (VaughanLogAverage.cellWeight (L N) q : ℂ) *
          zetaArithmeticFilter
            (SquarefreeVaughanProjection.squarefreePart (ZetaVaughanReduction.small q.1 q.2))
            P N (3 / 2 + Complex.I * y) := by
    apply HasSum.tsum_eq
    apply hm.congr_fun
    intro n
    rw [SquarefreeVaughanLogSource.coefficient_eq_mixture (SquarefreeVaughanLogSource.length_pos u N)]
  rw [hid]
  change _ = (u : ℂ) ^ (N + 1) * (zetaArithmeticBand
    (SquarefreeVaughanLogSource.coefficient (L N)) P N y - _)
  simp only [Function.comp_def]
  ring

/-- The original finite Riesz band with constant filter one retains the
full negative multiplicity source at exposed zeros. Its physical cutoff,
support and kernel are unchanged. -/
theorem tendsto_actual_riesz_band_one_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)) 1 N rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (tendsto_actual_riesz_band_sub_prime 1 rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hu hu1).add
    (tendsto_primeFilter_one_exposed rho hrho hexposed)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- Every previously proved component deletion transfers to the constant
filter. The final actual semiprime-free residual still carries exactly
the negative zero multiplicity without any isolating polynomial. -/
theorem tendsto_unfiltered_semiprimeResidual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ZetaRieszSemiprimeDeletion.residualResponse 1 N rho.1.im
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_actual_riesz_band_one_exposed rho hrho hexposed).sub
    (ZetaRieszSemiprimeDeletion.tendsto_actual_band_sub_residual rho hrho hexposed 1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- The normalized actual remaining sum with constant filter one. Its
definition needs no choice of zero-isolating polynomial. -/
def normalizedUnfilteredResidual (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    ZetaRieszSemiprimeDeletion.residualResponse 1 N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- A strict cofinal floor for the unfiltered whole residual contradicts
the actual negative multiplicity source. The floor remains a premise. -/
theorem false_of_unfiltered_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedUnfilteredResidual rho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_unfiltered_semiprimeResidual rho hrho hexposed)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent floors for just the unfiltered actual residuals at
exposed zeros suffice for Mathlib RH. All source and selection obligations
are discharged, while the global arithmetic floor is still open. -/
theorem rh_of_exposed_unfiltered_floors
    (hfloor : ∀ (rho : NontrivialZetaZero), 1 / 2 < rho.1.re →
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedUnfilteredResidual rho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact false_of_unfiltered_cofinal_floor sigma hsigma hexposed hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszUnfilteredSource
