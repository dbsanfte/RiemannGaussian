/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothPrimePrefix
import RiemannGaussian.ZetaRieszSmoothCofactor

/-!
# Physical-prefix deletion inside the joint arithmetic residual

The new independent prime-prefix bound is applied inside the previously
retained prime/cofactor residual. Single-large-prime survivors lie beyond
the physical cutoff on the proved source interval. An adaptive fallback
preserves the exact negative multiplicity source at every right-half scale.
The final RH implication assumes the still-open full independent floor.
-/

namespace RiemannGaussian.ZetaRieszPhysicalPrefixDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothPrimePrefix

/-- The new physical-prefix class is selected inside the previous
joint residual, preserving both the smooth-prime and cofactor deletions. -/
def prefixDeletionBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  actualProductBand (fun n => n ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N) u N

/-- The new deletion is literally a subband of the previously retained carrier. -/
theorem prefixDeletionBand_subset (u : ℝ) (N : ℕ) :
    prefixDeletionBand u N ⊆ ZetaRieszSmoothCofactor.optimizedRoughBand u N := by
  intro n hn
  exact ((mem_actualProductBand_iff _ u N n).mp hn).1.2

/-- The exact remaining integer labels after all three arithmetic deletions. -/
def prefixResidualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  ZetaRieszSmoothCofactor.optimizedRoughBand u N \ prefixDeletionBand u N

/-- The unchanged original signed coefficient and full factorial filter
on the class left after the new physical-prime-prefix deletion. -/
def prefixResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ prefixResidualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The old residual splits exactly into the independently paid
physical-prefix class and the new residual, with no duplicate integer labels. -/
theorem optimizedRoughResponse_eq_prefix_split (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    ZetaRieszSmoothCofactor.optimizedRoughResponse P N y L u =
      (∑ n ∈ prefixDeletionBand u N, SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      prefixResidualResponse P N y L u := by
  unfold ZetaRieszSmoothCofactor.optimizedRoughResponse prefixResidualResponse prefixResidualBand
  simpa only [add_comm] using (Finset.sum_sdiff
    (f := fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (prefixDeletionBand_subset u N)).symm

/-- The entire new subband vanishes independently inside the previous
residual; no previous arithmetic restriction is given up. -/
theorem tendsto_prefixDeletionBand (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ prefixDeletionBand u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) :=
  tendsto_actualProductBand_of_small_source
    (fun N n => n ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N) P y hu hcontact

/-- The literal original band differs negligibly from the new
three-deletion residual. This bound assumes no hypothetical zeta zero. -/
theorem tendsto_actual_band_sub_prefixResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        prefixResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have hu1 : u < 1 := hcontact.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have h := (ZetaRieszSmoothCofactor.tendsto_actual_band_sub_optimizedRoughResponse P y hu hu1).add
    (tendsto_prefixDeletionBand P y hu hcontact)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [optimizedRoughResponse_eq_prefix_split]
  ring

/-- Every remaining label retains the previously proved prime and
cofactor support restrictions. -/
theorem prefixResidualBand_subset (u : ℝ) (N : ℕ) :
    prefixResidualBand u N ⊆ ZetaRieszSmoothCofactor.optimizedRoughBand u N :=
  Finset.sdiff_subset

/-- If a remaining label has only one prime above the quadratic head,
that prime is strictly beyond the original physical Riesz cutoff. -/
theorem surviving_single_prime_above_physical_cutoff {u : ℝ} {N n a p : ℕ}
    (hn : n ∈ prefixResidualBand u N) (ha : Squarefree a)
    (hsmall : ∀ r ∈ a.primeFactors, r ≤ N ^ 2) (hp : p.Prime) (hbig : N ^ 2 < p)
    (he : n = p * a) :
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
  obtain ⟨hold, hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra hle
  have hb : n ∈ zetaPrimeLogBand N :=
    ZetaRieszSmoothCofactor.optimizedReducedBand_subset u N
      (ZetaRieszSmoothCofactor.optimizedRoughBand_support hold).1
  apply hnot
  exact (mem_actualProductBand_iff _ u N n).mpr
    ⟨⟨hb, hold⟩, a, p, ha, hsmall, hp, hbig, by omega, he⟩

/-- Use the stronger prefix residual on the proved interval, retaining
the previous joint residual at every other source scale. -/
def adaptivePrefixResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  if u < Real.exp (-(1 / 2 : ℝ)) then prefixResidualResponse P N y L u
  else ZetaRieszSmoothCofactor.optimizedRoughResponse P N y L u

/-- The original normalized band has independently vanishing error
against the adaptive carrier at every right-half source scale. -/
theorem tendsto_actual_band_sub_adaptivePrefix (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        adaptivePrefixResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  by_cases h : u < Real.exp (-(1 / 2 : ℝ))
  · simpa only [adaptivePrefixResponse, if_pos h] using tendsto_actual_band_sub_prefixResidual P y hu h
  · simpa only [adaptivePrefixResponse, if_neg h] using
      ZetaRieszSmoothCofactor.tendsto_actual_band_sub_optimizedRoughResponse P y hu hu1

/-- The exact original hypothetical-zero normalization on the adaptive
carrier, with the physical length and fixed pole-jet filter retained. -/
def normalizedAdaptivePrefix (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    adaptivePrefixResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- Every hypothetical right-half zero retains its exact negative
multiplicity source after the new deletion and its all-scale fallback. -/
theorem tendsto_normalizedAdaptivePrefix (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedAdaptivePrefix rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_adaptivePrefix (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedAdaptivePrefix
  ring

/-- A strict cofinal floor for the whole adaptive residual suffices
for contradiction. The independent arithmetic floor is still a premise. -/
theorem false_of_adaptivePrefix_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedAdaptivePrefix rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedAdaptivePrefix rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent full floors for the adaptive remaining carriers would
prove Mathlib RH. This implication does not establish their arithmetic floors. -/
theorem rh_of_adaptivePrefix_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedAdaptivePrefix rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_adaptivePrefix_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszPhysicalPrefixDeletion
