/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLargeSmoothClass
import RiemannGaussian.ZetaRieszCompositeDeletion

/-!
# Large smooth-factor deletion inside the complete Riesz remainder

On 1/2<u and 2*u^2<1, every nonzero surviving integer has its complete
smooth factor below the physical cutoff. All earlier arithmetic deletions
remain. An all-scale fallback preserves the exact hypothetical-zero source
and independent bridge to the signed Euler-window residual. The joint
cofinal signed floor remains unproved; the RH implication assumes it.
-/

namespace RiemannGaussian.ZetaRieszLargeSmoothDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszLargeSmoothClass

/-- The actual integer labels of the previous adaptive carrier,
including its proved complete-composite range and its other-scale fallback. -/
def previousBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u < Real.exp (-(1 / 2 : ℝ)) then ZetaRieszCompositeDeletion.compositeResidualBand u N
  else ZetaRieszSmoothCofactor.optimizedRoughBand u N

/-- The previous adaptive carrier is exactly the unchanged signed
sum on its literal adaptive integer band. -/
theorem sum_previousBand_eq_response (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    (∑ n ∈ previousBand u N, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ZetaRieszCompositeDeletion.adaptiveCompositeResponse P N y L u := by
  by_cases h : u < Real.exp (-(1 / 2 : ℝ)) <;>
    simp only [previousBand, ZetaRieszCompositeDeletion.adaptiveCompositeResponse, h,
      ite_true, ite_false, ZetaRieszCompositeDeletion.compositeResidualResponse,
      ZetaRieszSmoothCofactor.optimizedRoughResponse]

/-- Every label in the previous adaptive carrier lies in the original band. -/
theorem previousBand_subset (u : ℝ) (N : ℕ) : previousBand u N ⊆ zetaPrimeLogBand N := by
  intro n hn
  have hold : n ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N := by
    by_cases h : u < Real.exp (-(1 / 2 : ℝ))
    · rw [previousBand, if_pos h] at hn
      exact ZetaRieszPhysicalPrefixDeletion.prefixResidualBand_subset u N
        (Finset.mem_sdiff.mp hn).1
    · simpa only [previousBand, if_neg h] using hn
  exact ZetaRieszSmoothCofactor.optimizedReducedBand_subset u N
    (ZetaRieszSmoothCofactor.optimizedRoughBand_support hold).1

/-- The independently paid large-smooth-factor class is selected
inside the previous full adaptive residual, preserving all earlier deletions. -/
def largeSmoothDeletionBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  largeSmoothFactorBand (fun n => n ∈ previousBand u N) u N

/-- The new deletion is literally contained in the previous adaptive carrier. -/
theorem largeSmoothDeletionBand_subset (u : ℝ) (N : ℕ) :
    largeSmoothDeletionBand u N ⊆ previousBand u N := by
  intro n hn
  exact ((mem_largeSmoothFactorBand_iff _ u N n).mp hn).1.2

/-- Remaining labels after the complete large-smooth-factor deletion. -/
def largeSmoothResidualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  previousBand u N \ largeSmoothDeletionBand u N

/-- The full original signed response on the remaining integer class. -/
def largeSmoothResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ largeSmoothResidualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The previous adaptive response splits exactly before any norm,
retaining signs, factorial shifts, physical length and logarithmic phases. -/
theorem previousResponse_eq_largeSmooth_split (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    ZetaRieszCompositeDeletion.adaptiveCompositeResponse P N y L u =
      (∑ n ∈ largeSmoothDeletionBand u N, SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      largeSmoothResidualResponse P N y L u := by
  rw [← sum_previousBand_eq_response]
  unfold largeSmoothResidualResponse largeSmoothResidualBand
  simpa only [add_comm] using (Finset.sum_sdiff
    (f := fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (largeSmoothDeletionBand_subset u N)).symm

/-- The new complete component decays independently inside the
previous residual for every positive source scale with 2*u^2<1. -/
theorem tendsto_largeSmoothDeletionBand (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu2 : 2 * u ^ 2 < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ largeSmoothDeletionBand u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) :=
  tendsto_actual_largeSmoothFactorBand (fun N n => n ∈ previousBand u N) P y hu hu2

/-- The original band differs negligibly from the carrier with every
large smooth factor removed, including arbitrary rough-prime counts. -/
theorem tendsto_actual_band_sub_largeSmoothResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu2 : 2 * u ^ 2 < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        largeSmoothResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have hu0 : 0 < u := by linarith
  have hu1 : u < 1 := by nlinarith
  have h := (ZetaRieszCompositeDeletion.tendsto_actual_band_sub_adaptiveComposite P y hu hu1).add
    (tendsto_largeSmoothDeletionBand P y hu0 hu2)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [previousResponse_eq_largeSmooth_split]
  ring

/-- Every surviving smooth/rough factorization has its complete
smooth factor strictly below the physical cutoff, regardless of rough prime count. -/
theorem surviving_smooth_factor_lt_physical {u : ℝ} {N n a b : ℕ}
    (hn : n ∈ largeSmoothResidualBand u N) (ha : Squarefree a)
    (hsmall : ∀ p ∈ a.primeFactors, p ≤ N ^ 2) (hb : Squarefree b)
    (hrough : ∀ p ∈ b.primeFactors, N ^ 2 < p) (he : n = b * a) :
    a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  obtain ⟨hold, hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra h
  apply hnot
  exact (mem_largeSmoothFactorBand_iff _ u N n).mpr
    ⟨⟨previousBand_subset u N hold, hold⟩, a, b, ha, hsmall, by omega, hb, hrough, he⟩

/-- Every nonzero surviving integer has a complete smooth factor
strictly below the physical cutoff; its rough factor retains all large primes. -/
theorem surviving_support_with_small_smooth_factor {u L : ℝ} {N n : ℕ}
    (hn : n ∈ largeSmoothResidualBand u N) (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    ∃ a b : ℕ, Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, N ^ 2 < p) ∧ n = b * a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  have hsf : Squarefree n := by
    by_contra h
    exact hc (by simp [SquarefreeVaughanLogSource.coefficient, h])
  obtain ⟨a, b, ha, hsmall, hb, hrough, he⟩ := exists_smooth_rough_factorization hsf N
  exact ⟨a, b, ha, hsmall, hb, hrough, he,
    surviving_smooth_factor_lt_physical hn ha hsmall hb hrough he⟩

/-- Use the large-smooth-factor residual on the proved interval, retaining
the previous joint residual at every other source scale. -/
def adaptiveSmoothResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  if 2 * u ^ 2 < 1 then largeSmoothResidualResponse P N y L u
  else ZetaRieszCompositeDeletion.adaptiveCompositeResponse P N y L u

/-- The original normalized band has independently vanishing error
against the adaptive carrier at every right-half source scale. -/
theorem tendsto_actual_band_sub_adaptiveSmooth (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        adaptiveSmoothResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  by_cases h : 2 * u ^ 2 < 1
  · simpa only [adaptiveSmoothResponse, if_pos h] using tendsto_actual_band_sub_largeSmoothResidual P y hu h
  · simpa only [adaptiveSmoothResponse, if_neg h] using
      ZetaRieszCompositeDeletion.tendsto_actual_band_sub_adaptiveComposite P y hu hu1

/-- The exact original hypothetical-zero normalization on the adaptive
carrier, with the physical length and fixed pole-jet filter retained. -/
def normalizedAdaptiveSmooth (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    adaptiveSmoothResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- Every hypothetical right-half zero retains its exact negative
multiplicity source after the large-smooth-factor deletion and its all-scale fallback. -/
theorem tendsto_normalizedAdaptiveSmooth (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedAdaptiveSmooth rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_adaptiveSmooth (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedAdaptiveSmooth
  ring

/-- A strict cofinal floor for the whole adaptive residual suffices
for contradiction. The independent arithmetic floor is still a premise. -/
theorem false_of_adaptiveSmooth_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedAdaptiveSmooth rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedAdaptiveSmooth rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent full floors for the adaptive remaining carriers would
prove Mathlib RH. This implication does not establish their arithmetic floors. -/
theorem rh_of_adaptiveSmooth_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedAdaptiveSmooth rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_adaptiveSmooth_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- The signed Euler-window residual remains independently connected
to the more tightly supported adaptive arithmetic carrier at every scale. -/
theorem tendsto_quadraticResidual_sub_adaptiveSmooth (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszEulerWindowDeletion.windowResidualResponse P N (N ^ 2) y
        (SquarefreeVaughanLogSource.length u N) -
        adaptiveSmoothResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have h := (tendsto_actual_band_sub_adaptiveSmooth P y hu hu1).sub
    (ZetaRieszEulerQuadraticHead.tendsto_actual_band_sub_quadraticResidual P y
      (show 0 < u by linarith) hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end
end RiemannGaussian.ZetaRieszLargeSmoothDeletion
