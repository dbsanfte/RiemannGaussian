/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity

/-!
# Quadratic-head correction deletion in the literal arithmetic band

The complete correction coupled to the actual head through N^2 has independently vanishing error at every original factorial order. Exact prime support, physical cutoff, signed boundary and negative multiplicity source are retained. The final RH implication is conditional on the independent floor for the complete residual; that floor remains open.
-/

namespace RiemannGaussian.ZetaRieszEulerQuadraticHead
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
open ZetaRieszEulerMultiplier ZetaRieszEulerHead ZetaRieszEulerGrowingHead
open ZetaRieszEulerWindowDeletion ZetaRieszEulerMoments
open ZetaRieszEulerPrimeHeadDensity

/-- The actual prime head through the square of the original order
can multiply its complete complementary correction with vanishing error at
every order, retaining the physical length and full factorial filter. -/
theorem tendsto_actual_quadratic_head_correction (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun n : ℕ => (u : ℂ) ^ (n + 1) *
      headFilteredResponse (actualWindowHead n (n ^ 2)) (actualWindowTail n (n ^ 2)) P n
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u n)) atTop (nhds 0) := by
  let R : ℝ := (u + 1) / 2
  have hS (n p : ℕ) (hp : p ∈ actualWindowHead n (n ^ 2)) : p.Prime ∧ p ≤ n ^ 2 :=
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hQ : ∀ᶠ n : ℕ in atTop, ∀ p ∈ actualWindowTail n (n ^ 2), 16 ≤ p := by
    filter_upwards [eventually_ge_atTop 4] with n hn p hp
    have hs : 16 ≤ n ^ 2 := by nlinarith
    have hp' := (Finset.mem_filter.mp hp).2
    omega
  apply tendsto_quadratic_headFilteredResponse
    (fun n => actualWindowHead n (n ^ 2)) (fun n => actualWindowTail n (n ^ 2)) hS hQ P
    (SquarefreeVaughanLogSource.length u) (Real.log_pos (by norm_num : (1 : ℝ) < 4))
    (ZetaRieszFixedCofactor.length_ge_log_four u) hu (show u < R by dsimp [R]; linarith)
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs]
  dsimp [R]
  linarith

/-- The full head through the square of each original order is paid
inside the literal arithmetic band. The independently vanishing deletion
error now uses every order, with the whole explicit signed residual retained. -/
theorem tendsto_actual_band_sub_quadraticResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun n : ℕ => (u : ℂ) ^ (n + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u n)) P n y -
        windowResidualResponse P n (n ^ 2) y (SquarefreeVaughanLogSource.length u n)))
      atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (1 / (2 * (Real.pi : ℂ))) * ((u : ℂ) ^ (n + 1) *
      headFilteredResponse (actualWindowHead n (n ^ 2)) (actualWindowTail n (n ^ 2)) P n
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u n))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_actual_quadratic_head_correction P y hu hu1).const_mul
      (1 / (2 * (Real.pi : ℂ)))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [actual_band_eq_windowResidual_response P n (n ^ 2) (by nlinarith)]
  ring

/-- The quadratic-window residual keeps the original hypothetical-zero
filter and source normalization at every original factorial order. -/
def normalizedQuadraticResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (n : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (n + 1) *
    windowResidualResponse (zetaRightHalfPoleJetFilter rho hrho) n (n ^ 2) rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) n)

/-- The independent quadratic-head deletion preserves the exact
negative-multiplicity source at every original order. The full signed
compensated-leading/mixed/boundary residual still lacks its independent floor. -/
theorem tendsto_normalizedQuadraticResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedQuadraticResidual rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hsource := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have herror := tendsto_actual_band_sub_quadraticResidual (zetaRightHalfPoleJetFilter rho hrho)
    rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at herror
  have h := hsource.sub herror
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with n
  unfold normalizedQuadraticResidual
  ring

/-- Only a strict cofinal real floor for the whole quadratic residual
is needed for contradiction. The independent floor is the unproved premise. -/
theorem false_of_quadraticResidual_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ n in atTop, -c ≤ (normalizedQuadraticResidual rho hrho n).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedQuadraticResidual rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- An independent joint floor for every quadratic-window residual
would close Mathlib RH. This implication does not establish that floor. -/
theorem rh_of_quadraticResidual_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ n in atTop, -c ≤ (normalizedQuadraticResidual rho hrho n).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_quadraticResidual_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszEulerQuadraticHead
