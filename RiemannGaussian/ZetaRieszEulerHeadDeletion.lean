/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerHead

/-!
# Deleting the complete small-head correction from the original arithmetic band

The entire actual small-head correction has independently vanishing source-scale error. The explicit remainder keeps the compensated leading quotient, its mixed correction and the signed completion boundary. The hypothetical-zero source survives. The conditional RH implication does not prove its independent floor premise.
-/

namespace RiemannGaussian.ZetaRieszEulerHeadDeletion
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter
open ZetaRieszEulerCutoff ZetaRieszEulerMoments ZetaRieszEulerCorrectionDeletion
open ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerMultiplier ZetaRieszEulerHead

/-- The growing large-prime Euler quotient is kept explicit, separately
from the finite small-prime head whose correction interaction is now paid. -/
def largeLeadingResponse (m : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (∏ p ∈ largePrimes m, (1 - zetaPrimeFeature s p * zetaPrimeFeature (Complex.I * xi) p)) /
    (∏ p ∈ largePrimes m, (1 - zetaPrimeFeature s p))

/-- The original leading response retains its exact small-prime head
and its growing large-prime quotient, with the literal prime orientation. -/
theorem leadingResponse_eq_head_mul_large (N : ℕ) (s : ℂ) (xi : ℝ) :
    leadingResponse (primorial (2 ^ (32 * N))) s xi =
      headCharacter (actualSmallPrimes N) s (-xi) *
        largeLeadingResponse (primorial (2 ^ (32 * N))) s xi := by
  unfold leadingResponse largeLeadingResponse
  congr 1
  unfold headCharacter actualSmallPrimes
  apply Finset.prod_congr rfl
  intro p _hp
  rw [ZetaRieszCompositeProduct.imaginary_feature_eq_character]
  rfl

/-- The explicit remainder after paying the full small-head correction:
the leading response, all ordinary-prime compensation, the mixed term with
the growing large-prime quotient, and the entire signed completion boundary. -/
def headResidualCompletedBand (N : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  (leadingResponse (primorial (2 ^ (32 * N))) s xi - 1 -
    ∑ p ∈ (primorial (2 ^ (32 * N))).primeFactors,
      zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)) +
  headCharacter (actualSmallPrimes N) s (-xi) *
    (largeLeadingResponse (primorial (2 ^ (32 * N))) s xi - 1) *
      (correctionProduct (originalCorrectionPrimes N) (zetaPrimeFeature s)
        (fun p => Real.log p) (-xi) - 1) -
  ∑ n ∈ (((primorial (2 ^ (32 * N))).divisors.erase 1).filter
    (fun n => ¬ n.Prime)).filter (fun n => n ∉ zetaPrimeLogBand N),
      zetaPrimeFeature s n * ZetaRieszPrimeFourier.primeProduct n xi

/-- The literal completed band splits into the proved-decaying full
small-head correction and its explicit remainder. No growing quotient,
ordinary-prime compensation or signed off-band boundary is discarded. -/
theorem completedBand_eq_headResidual_add_head (N : ℕ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    ZetaRieszFilteredCompletion.completedBand N xi s = headResidualCompletedBand N xi s +
      headCorrectionBand (actualSmallPrimes N) (originalCorrectionPrimes N) xi s := by
  unfold ZetaRieszFilteredCompletion.completedBand
  rw [compositeResponse_eq_leading_split _ hs]
  unfold headResidualCompletedBand headCorrectionBand
  rw [leadingResponse_eq_head_mul_large]
  unfold originalCorrectionPrimes largePrimes
  ring

/-- The actual completed-band split is a local analytic identity on
the whole Cauchy neighborhood, so no center-only equality is differentiated. -/
theorem completedBand_head_split_eventually (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.completedBand N xi =ᶠ[nhds s]
      (fun z => headResidualCompletedBand N xi z +
        headCorrectionBand (actualSmallPrimes N) (originalCorrectionPrimes N) xi z) := by
  have hh : ∀ᶠ z : ℂ in nhds s, (1 / 2 : ℝ) < z.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hs)
  filter_upwards [hh] with z hz
  exact completedBand_eq_headResidual_add_head N hz.le xi

/-- The explicit leading/large-mixed/boundary remainder is analytic by
its exact completed-source identity, without a new arithmetic assumption. -/
theorem analyticAt_headResidualCompletedBand (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (headResidualCompletedBand N xi) s := by
  have he : (fun z => ZetaRieszFilteredCompletion.completedBand N xi z -
      headCorrectionBand (actualSmallPrimes N) (originalCorrectionPrimes N) xi z)
      =ᶠ[nhds s] headResidualCompletedBand N xi := by
    filter_upwards [completedBand_head_split_eventually N xi hs] with z hz
    rw [hz]
    ring
  exact ((analyticAt_completedBand N xi s).sub
    (analyticAt_headCorrectionBand _ _ (fun _ hp => (Finset.mem_filter.mp hp).2) xi hs.le)).congr he

/-- Every original factorial moment retains the exact new remainder
and the independently paid small-head correction. -/
theorem moment_completedBand_eq_head_split (N : ℕ) (xi : ℝ) {s : ℂ}
    (hs : 1 / 2 < s.re) (n : ℕ) :
    signedTaylorMoment n (ZetaRieszFilteredCompletion.completedBand N xi) s =
      signedTaylorMoment n (headResidualCompletedBand N xi) s +
        signedTaylorMoment n
          (headCorrectionBand (actualSmallPrimes N) (originalCorrectionPrimes N) xi) s := by
  rw [signedTaylorMoment_congr n (completedBand_head_split_eventually N xi hs)]
  exact signedTaylorMoment_add n (analyticAt_headResidualCompletedBand N xi hs)
    (analyticAt_headCorrectionBand _ _ (fun _ hp => (Finset.mem_filter.mp hp).2) xi hs.le)

/-- The original logarithm-marked fixed filter preserves the complete
small-head split with every factorial offset unchanged. -/
theorem filteredCompletedBand_eq_head_split (P : Polynomial ℂ) (N : ℕ) (xi : ℝ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.filteredCompletedBand P N s xi =
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headResidualCompletedBand N xi) s) N +
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1)
          (headCorrectionBand (actualSmallPrimes N) (originalCorrectionPrimes N) xi) s) N := by
  simp only [ZetaRieszFilteredCompletion.filteredCompletedBand, zetaMomentSequenceFilter,
    Polynomial.sum, moment_completedBand_eq_head_split N xi hs, mul_add, Finset.sum_add_distrib]

/-- The new residual frequency kernel retains the compensated leading
quotient, its mixed correction and the entire signed completion boundary. -/
def headResidualKernel (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  (phase (L * xi) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headResidualCompletedBand N xi) s) N +
  phase (-(L * xi)) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headResidualCompletedBand N (-xi)) s) N) /
      ((L : ℂ) * (xi : ℂ) ^ 2)

/-- Both physical phases of the literal finite band split exactly into
the new explicit residual and the full small-head correction kernel. -/
theorem actual_kernel_eq_headResidual_add_head (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 / 2 < s.re) (L xi : ℝ) :
    ZetaRieszPrimeFourier.bandPrimePair (zetaPrimeLogBand N)
      (fun n => zetaPrimeFilterKernel P N s n) L xi =
        headResidualKernel P N s L xi +
          headFilteredKernel (actualSmallPrimes N) (originalCorrectionPrimes N) P N s L xi := by
  rw [ZetaRieszFilteredCompletion.bandPrimePair_eq_filtered_completion,
    filteredCompletedBand_eq_head_split P N xi hs, filteredCompletedBand_eq_head_split P N (-xi) hs,
    headFilteredKernel_eq_pair (actualSmallPrimes N) (originalCorrectionPrimes N)
      (fun _ hp => (Finset.mem_filter.mp hp).2) P N hs.le]
  unfold headResidualKernel phase
  rw [show xi * L = L * xi by ring, show -xi * L = -(L * xi) by ring]
  ring

/-- The new remainder is genuinely integrable as the original finite
band kernel minus the independently integrable small-head correction. -/
theorem integrable_headResidualKernel (P : Polynomial ℂ) (N : ℕ) {s : ℂ}
    (hs : 1 / 2 < s.re) (L : ℝ) : IntegrableOn (headResidualKernel P N s L) (Ioi 0) := by
  have hi := (ZetaRieszPrimeFourier.integrable_bandPrimePair (zetaPrimeLogBand N)
    (fun n => zetaPrimeFilterKernel P N s n) L).sub
      (integrable_headFilteredKernel (actualSmallPrimes N) (originalCorrectionPrimes N)
        (fun _ hp => (Finset.mem_filter.mp hp).2) P N hs L)
  apply hi.congr
  filter_upwards [] with xi
  simp only [Pi.sub_apply]
  rw [actual_kernel_eq_headResidual_add_head P N hs]
  ring

/-- The explicitly unpaid response after removing the whole small-head
correction, with the literal physical filter and signed boundary intact. -/
def headResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in Ioi 0, headResidualKernel P N (3 / 2 + Complex.I * y) L xi

/-- The literal original arithmetic band is exactly the new explicit
remainder plus the independently controlled full small-head correction. -/
theorem actual_band_eq_headResidual_response (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      headResidualResponse P N y L + (1 / (2 * (Real.pi : ℂ))) *
        headFilteredResponse (actualSmallPrimes N) (originalCorrectionPrimes N) P N
          (3 / 2 + Complex.I * y) L := by
  have hs : 1 / 2 < (3 / 2 + Complex.I * (y : ℂ)).re := by norm_num
  have h16 : ∀ p ∈ originalCorrectionPrimes N, 16 ≤ p := fun _ hp => (Finset.mem_filter.mp hp).2
  rw [ZetaRieszPrimeFourier.actual_band_eq_primePair_integral]
  simp_rw [actual_kernel_eq_headResidual_add_head P N hs]
  rw [integral_add (integrable_headResidualKernel P N hs L)
    (integrable_headFilteredKernel _ _ h16 P N hs L),
    ← headFilteredResponse_eq_integral _ _ h16 P N hs L]
  unfold headResidualResponse
  ring

/-- Removing the complete small-head correction changes the actual
normalized arithmetic band by a quantity tending to zero. The compensated
leading quotient, its large-prime mixed term and signed boundary stay coupled. -/
theorem tendsto_actual_band_sub_headResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
        P N y - headResidualResponse P N y (SquarefreeVaughanLogSource.length u N)))
      Filter.atTop (nhds 0) := by
  have he (N : ℕ) : (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
        P N y - headResidualResponse P N y (SquarefreeVaughanLogSource.length u N)) =
      (1 / (2 * (Real.pi : ℂ))) * ((u : ℂ) ^ (N + 1) *
        headFilteredResponse (actualSmallPrimes N) (originalCorrectionPrimes N) P N
          (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N)) := by
    rw [actual_band_eq_headResidual_response]
    ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_actual_headFilteredResponse P y hu hu1).const_mul
    (1 / (2 * (Real.pi : ℂ)))


/-- The explicit remaining response at the original hypothetical-zero
filter and physical cutoff, with its source normalization unchanged. -/
def normalizedHeadResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    headResidualResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)

/-- The independently vanishing small-head correction leaves the exact
negative multiplicity source in the explicit leading/large-mixed/boundary residual.
This source identity is conditional on the hypothetical zero, not a floor. -/
theorem tendsto_normalizedHeadResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedHeadResidual rho hrho) atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hsource := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have herror := tendsto_actual_band_sub_headResidual (zetaRightHalfPoleJetFilter rho hrho)
    rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at herror
  have h := hsource.sub herror
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedHeadResidual
  ring

/-- Only a strict cofinal lower floor is required for the full explicit
residual. Its independent arithmetic proof remains the open premise. -/
theorem false_of_headResidual_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedHeadResidual rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedHeadResidual rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- A full arithmetic floor for every such residual would close Mathlib's
RH by the existing zero reflection. No extra analytic premise remains after
that floor; the floor itself is not proved by this implication. -/
theorem rh_of_headResidual_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedHeadResidual rho hrho N).re) : RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_headResidual_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszEulerHeadDeletion
