/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourExtremeBound

/-!
# Actual four-extreme-prime deletion and the full signed source

The whole narrowed carrier loses every label with four or more primes
at or above the physical cutoff on u<exp(-1/2), with an unchanged fallback
elsewhere. Its normalized deletion error vanishes independently. All
earlier support cuts, the exact cosine identity and negative multiplicity
source at exposed zeros survive. The new support has at most three
extreme primes on this interval; intermediate primes remain unrestricted
by that count. The independent whole-residual cofinal floor is still open,
and the Mathlib RH closure theorem keeps it as an explicit premise.
-/

namespace RiemannGaussian.ZetaRieszFourExtremeDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszExtremePrimeCount
open ZetaRieszExtremeDegreeBounds
open ZetaRieszFourExtremeBound

/-- Remove the now-paid four-or-more-extreme class on its source interval;
all other scales retain the complete previously narrowed support. -/
def fourResidualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u < Real.exp (-(1 / 2 : ℝ)) then
    (ZetaRieszNarrowCarrier.residualBand u N).filter (fun n => (extremePrimes u N n).card < 4)
  else ZetaRieszNarrowCarrier.residualBand u N

/-- The full new signed residual uses the same coefficient, physical
length, integer labels and complete factorial filter. -/
def fourResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ fourResidualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Every earlier narrowed arithmetic restriction is retained. -/
theorem fourResidualBand_subset (u : ℝ) (N : ℕ) :
    fourResidualBand u N ⊆ ZetaRieszNarrowCarrier.residualBand u N := by
  unfold fourResidualBand
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

/-- On the new deletion interval every surviving label now has at most
three primes at or above the physical cutoff, at every moment order. -/
theorem surviving_extreme_count_le_three {u : ℝ} {N n : ℕ}
    (hcontact : u < Real.exp (-(1 / 2 : ℝ))) (hn : n ∈ fourResidualBand u N) :
    (extremePrimes u N n).card ≤ 3 := by
  rw [fourResidualBand, if_pos hcontact] at hn
  have hh := (Finset.mem_filter.mp hn).2
  omega

/-- The actual four-prime deletion has vanishing normalized error. Its
fallback is unchanged outside the proved interval, and no zero is assumed. -/
theorem tendsto_narrow_sub_fourResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszNarrowCarrier.residualResponse P N y (SquarefreeVaughanLogSource.length u N) u -
        fourResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u)) atTop (𝓝 0) := by
  by_cases hcontact : u < Real.exp (-(1 / 2 : ℝ))
  · have h := tendsto_four_extreme_sum
      (fun N => (ZetaRieszNarrowCarrier.residualBand u N).filter
        (fun n => 4 ≤ (extremePrimes u N n).card)) P y hu hcontact
      (fun _ _ hn => (Finset.mem_filter.mp hn).2)
    apply h.congr'
    filter_upwards [] with N
    have he := Finset.sum_filter_add_sum_filter_not (ZetaRieszNarrowCarrier.residualBand u N)
      (fun n => (extremePrimes u N n).card < 4)
      (fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    simp only [not_lt] at he
    dsimp only [ZetaRieszNarrowCarrier.residualResponse, fourResidualResponse, fourResidualBand]
    rw [if_pos hcontact]
    rw [← he]
    ring
  · simpa only [fourResidualResponse, fourResidualBand, if_neg hcontact,
      ZetaRieszNarrowCarrier.residualResponse, sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The new constant-filter residual retains the original source factor. -/
def normalizedFourResidual (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    fourResidualResponse 1 N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
      (3 / 2 - rho.1.re)

/-- The negative multiplicity source survives removal of the actual four-
or-more-extreme-prime class, with an unchanged fallback at other scales. -/
theorem tendsto_normalizedFourResidual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (normalizedFourResidual rho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszNarrowCarrier.tendsto_normalizedResidual rho hrho hexposed).sub
    (tendsto_narrow_sub_fourResidual 1 rho.1.im hu)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedFourResidual ZetaRieszNarrowCarrier.normalizedResidual
  ring

/-- The whole new real residual is still the original signed coefficient
times a nonnegative factorial envelope times the full cosine phase. -/
theorem re_normalizedFourResidual_eq_cosine_sum (rho : NontrivialZetaZero) (N : ℕ) :
    (normalizedFourResidual rho N).re =
      (3 / 2 - rho.1.re) ^ (N + 1) *
        ∑ n ∈ fourResidualBand (3 / 2 - rho.1.re) N,
          (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n).re *
            (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
              Real.cos (rho.1.im * Real.log n) := by
  simp only [normalizedFourResidual, fourResidualResponse, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.re_sum, ZetaRieszCosineCarrier.re_coefficient_filter_one]

/-- A strict cofinal floor for the whole new residual contradicts the
unchanged negative multiplicity source. The floor is still an open premise. -/
theorem false_of_fourResidual_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedFourResidual rho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedFourResidual rho hrho hexposed)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- The remaining whole-residual cofinal floors imply Mathlib RH. The
actual four-prime deletion, all-scale fallback, source and exposed-zero
selection are proved; only the independent arithmetic floors are premises. -/
theorem rh_of_exposed_fourResidual_floors
    (hfloor : ∀ (rho : NontrivialZetaZero), 1 / 2 < rho.1.re →
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedFourResidual rho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact false_of_fourResidual_cofinal_floor sigma hsigma hexposed hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszFourExtremeDeletion
