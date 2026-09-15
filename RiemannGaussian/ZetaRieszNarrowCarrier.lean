/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCosineCarrier
import RiemannGaussian.ZetaArithmeticLogWindow

/-!
# Independent outer-band deletion in the actual signed carrier

The actual remaining Riesz sum is narrowed to
2*N/5 < log(n) <= 8*N*log(2), intersecting every earlier arithmetic cut.
Both discarded outer pieces have explicit geometric bounds, uniformly
in height and positive physical length, for every fixed filter. They
vanish without a zero premise for 0<u<1. At exposed right-half zeros the
constant filter preserves the whole negative multiplicity source.
The signed cosine identity and conditional Mathlib RH closure are checked;
the independent cofinal floor for the full narrowed sum remains open.
-/

namespace RiemannGaussian.ZetaRieszNarrowCarrier
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaArithmeticLogWindow

/-- The actual residual keeps every earlier support deletion and is now
restricted to the smaller logarithmic window. -/
def residualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  narrowBand (ZetaRieszSemiprimeDeletion.residualBand u N) N

/-- The narrowed residual retains the physical coefficient, full
complex phase and every fixed factorial filter shift. -/
def residualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ residualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The new support is an intersection with the old one, so all prior
arithmetic exclusions and their original source-scale ranges survive. -/
theorem residualBand_subset (u : ℝ) (N : ℕ) :
    residualBand u N ⊆ ZetaRieszSemiprimeDeletion.residualBand u N := Finset.filter_subset _ _

/-- The literal finite support has the exact narrowed logarithmic
endpoints in addition to every earlier residual restriction. -/
theorem mem_residualBand {u : ℝ} {N n : ℕ} :
    n ∈ residualBand u N ↔ n ∈ ZetaRieszSemiprimeDeletion.residualBand u N ∧
      (2 / 5 : ℝ) * N < Real.log n ∧ Real.log n ≤ 8 * (N : ℝ) * Real.log 2 := by
  simp only [residualBand, narrowBand, Finset.mem_filter]

/-- The actual discarded arithmetic coefficients have a fully explicit
two-rate allowance, uniform in the ordinate and all positive lengths. -/
theorem norm_actual_residual_sub_narrow (P : Polynomial ℂ) (N : ℕ) (y u : ℝ)
    {L : ℝ} (hL : 0 < L) :
    ‖ZetaRieszSemiprimeDeletion.residualResponse P N y L u - residualResponse P N y L u‖ ≤
      lowerRate ^ N * tiltConstant P 2 (17 / 16) +
        upperRate ^ N * tiltConstant P (1 / 5) (121 / 120) :=
  norm_sub_narrowBand_le _ _
    (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le hL n) P N y

/-- The normalized discarded actual arithmetic contribution has its
original source factor and the two independently controlled geometric rates. -/
theorem norm_normalized_residual_sub_narrow (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (N + 1) *
      (ZetaRieszSemiprimeDeletion.residualResponse P N y
        (SquarefreeVaughanLogSource.length u N) u -
      residualResponse P N y (SquarefreeVaughanLogSource.length u N) u)‖ ≤
        u ^ (N + 1) * (lowerRate ^ N * tiltConstant P 2 (17 / 16) +
          upperRate ^ N * tiltConstant P (1 / 5) (121 / 120)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  exact mul_le_mul_of_nonneg_left
    (norm_actual_residual_sub_narrow P N y u (SquarefreeVaughanLogSource.length_pos u N))
    (by positivity)

/-- Both newly removed parts of the actual residual vanish independently,
for every fixed filter and 0<u<1, without assuming a zeta zero. -/
theorem tendsto_actual_residual_sub_narrow (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszSemiprimeDeletion.residualResponse P N y
        (SquarefreeVaughanLogSource.length u N) u -
      residualResponse P N y (SquarefreeVaughanLogSource.length u N) u)) atTop (𝓝 0) :=
  tendsto_sub_narrowBand (fun N => ZetaRieszSemiprimeDeletion.residualBand u N)
    (fun N => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (fun N n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u N) n) P y hu hu1

/-- The original full arithmetic band differs from this narrower residual
by a vanishing source-normalized error at exposed right-half zeros. -/
theorem tendsto_original_band_sub_narrow (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)) P N rho.1.im -
        residualResponse P N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (3 / 2 - rho.1.re))) atTop (𝓝 0) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (ZetaRieszSemiprimeDeletion.tendsto_actual_band_sub_residual rho hrho hexposed P).add
    (tendsto_actual_residual_sub_narrow P rho.1.im hu hu1)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- The normalized narrower carrier with the constant filter one. -/
def normalizedResidual (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    residualResponse 1 N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
      (3 / 2 - rho.1.re)

/-- The full negative multiplicity source survives the smaller actual
window with the constant filter, so no source margin has been spent. -/
theorem tendsto_normalizedResidual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (normalizedResidual rho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (ZetaRieszUnfilteredSource.tendsto_actual_riesz_band_one_exposed rho hrho hexposed).sub
    (tendsto_original_band_sub_narrow rho hrho hexposed 1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedResidual
  ring

/-- The narrowed real carrier still shows the complete arithmetic sign,
nonnegative factorial amplitude and cosine of the actual product phase. -/
theorem re_normalizedResidual_eq_cosine_sum (rho : NontrivialZetaZero) (N : ℕ) :
    (normalizedResidual rho N).re =
      (3 / 2 - rho.1.re) ^ (N + 1) *
        ∑ n ∈ residualBand (3 / 2 - rho.1.re) N,
          (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n).re *
            (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
              Real.cos (rho.1.im * Real.log n) := by
  simp only [normalizedResidual, residualResponse, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.re_sum, ZetaRieszCosineCarrier.re_coefficient_filter_one]

/-- A cofinal floor strictly above minus one contradicts the narrowed
source. Only this independent whole-sum arithmetic floor remains a premise. -/
theorem false_of_narrow_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedResidual rho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedResidual rho hrho hexposed)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent cofinal floors for the whole narrowed carriers at exposed
zeros imply Mathlib RH. The arithmetic floors are explicit open premises. -/
theorem rh_of_exposed_narrow_floors
    (hfloor : ∀ (rho : NontrivialZetaZero), 1 / 2 < rho.1.re →
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedResidual rho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact false_of_narrow_cofinal_floor sigma hsigma hexposed hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszNarrowCarrier
