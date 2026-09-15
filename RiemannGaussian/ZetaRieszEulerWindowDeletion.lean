/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerGrowingHead

/-!
# Growing-head deletion with the original signed band and source retained

The moving prime threshold has an exact Euler factorization and explicit compensated-leading, mixed-correction and signed-boundary residual. Local analytic identities, every factorial coordinate and genuine frequency integrals transport the independent growing-head decay to the literal original band along a cofinal stride. The negative-multiplicity source survives; the joint independent residual floor remains open.
-/

namespace RiemannGaussian.ZetaRieszEulerWindowDeletion
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter
open ZetaRieszEulerCutoff ZetaRieszEulerMoments ZetaRieszEulerCorrectionDeletion
open ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerMultiplier ZetaRieszEulerHead ZetaRieszEulerGrowingHead

/-- The exact Euler quotient over the complement of the growing head. -/
def windowLeadingResponse (N b : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (∏ p ∈ actualWindowTail N b, (1 - zetaPrimeFeature s p * zetaPrimeFeature (Complex.I * xi) p)) /
    (∏ p ∈ actualWindowTail N b, (1 - zetaPrimeFeature s p))

/-- The literal full character has the exact head/quotient/correction
factorization at every admissible moving threshold. All phases are retained. -/
theorem full_character_eq_window (N b : ℕ) (hb : 16 ≤ b + 1) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    (∏ p ∈ (primorial (2 ^ (32 * N))).primeFactors,
      (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))) =
      headCharacter (actualWindowHead N b) s (-xi) * windowLeadingResponse N b s xi *
        correctionProduct (actualWindowTail N b) (zetaPrimeFeature s) (fun p => Real.log p) (-xi) := by
  have hpart := Finset.prod_filter_mul_prod_filter_not
    (primorial (2 ^ (32 * N))).primeFactors (fun p => p ≤ b)
    (fun p => (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)))
  simp only [Nat.not_le] at hpart
  have ht := actual_character_eq_euler_quotient_correction (actualWindowTail N b)
    (fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega) hs (-xi)
  simp_rw [← ZetaRieszCompositeProduct.imaginary_feature_eq_character] at ht
  have hhead : (∏ p ∈ actualWindowHead N b,
      (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))) =
        headCharacter (actualWindowHead N b) s (-xi) := by
    apply Finset.prod_congr rfl
    intro p _hp
    rw [ZetaRieszCompositeProduct.imaginary_feature_eq_character]
    rfl
  rw [← hpart]
  change (∏ p ∈ actualWindowHead N b, _) * (∏ p ∈ actualWindowTail N b, _) = _
  rw [hhead, ht]
  unfold windowLeadingResponse
  ring

/-- The remaining completed band after deleting the full moving-head
correction: compensated leading response, mixed term with its complementary
quotient, and the entire original signed off-band boundary. -/
def windowResidualCompletedBand (N b : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  (headCharacter (actualWindowHead N b) s (-xi) * windowLeadingResponse N b s xi - 1 -
    ∑ p ∈ (primorial (2 ^ (32 * N))).primeFactors,
      zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)) +
  headCharacter (actualWindowHead N b) s (-xi) * (windowLeadingResponse N b s xi - 1) *
    (correctionProduct (actualWindowTail N b) (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 1) -
  ∑ n ∈ (((primorial (2 ^ (32 * N))).divisors.erase 1).filter
    (fun n => ¬ n.Prime)).filter (fun n => n ∉ zetaPrimeLogBand N),
      zetaPrimeFeature s n * ZetaRieszPrimeFourier.primeProduct n xi

/-- The original completed band splits exactly at any admissible
moving prime threshold, with the whole signed boundary still present. -/
theorem completedBand_eq_windowResidual_add_head (N b : ℕ) (hb : 16 ≤ b + 1) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    ZetaRieszFilteredCompletion.completedBand N xi s = windowResidualCompletedBand N b xi s +
      headCorrectionBand (actualWindowHead N b) (actualWindowTail N b) xi s := by
  unfold ZetaRieszFilteredCompletion.completedBand ZetaRieszCompositeProduct.compositeResponse
  rw [full_character_eq_window N b hb hs]
  unfold windowResidualCompletedBand headCorrectionBand
  ring

/-- The actual completed-band split is a local analytic identity on
the whole Cauchy neighborhood, so no center-only equality is differentiated. -/
theorem completedBand_window_split_eventually (N b : ℕ) (hb : 16 ≤ b + 1) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.completedBand N xi =ᶠ[nhds s]
      (fun z => windowResidualCompletedBand N b xi z +
        headCorrectionBand (actualWindowHead N b) (actualWindowTail N b) xi z) := by
  have hh : ∀ᶠ z : ℂ in nhds s, (1 / 2 : ℝ) < z.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hs)
  filter_upwards [hh] with z hz
  exact completedBand_eq_windowResidual_add_head N b hb hz.le xi

/-- The explicit leading/large-mixed/boundary remainder is analytic by
its exact completed-source identity, without a new arithmetic assumption. -/
theorem analyticAt_windowResidualCompletedBand (N b : ℕ) (hb : 16 ≤ b + 1) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (windowResidualCompletedBand N b xi) s := by
  have he : (fun z => ZetaRieszFilteredCompletion.completedBand N xi z -
      headCorrectionBand (actualWindowHead N b) (actualWindowTail N b) xi z)
      =ᶠ[nhds s] windowResidualCompletedBand N b xi := by
    filter_upwards [completedBand_window_split_eventually N b hb xi hs] with z hz
    rw [hz]
    ring
  exact ((analyticAt_completedBand N xi s).sub
    (analyticAt_headCorrectionBand _ _ (fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega) xi hs.le)).congr he

/-- Every original factorial moment retains the exact new remainder
and the independently paid moving-head correction. -/
theorem moment_completedBand_eq_window_split (N b : ℕ) (hb : 16 ≤ b + 1) (xi : ℝ) {s : ℂ}
    (hs : 1 / 2 < s.re) (n : ℕ) :
    signedTaylorMoment n (ZetaRieszFilteredCompletion.completedBand N xi) s =
      signedTaylorMoment n (windowResidualCompletedBand N b xi) s +
        signedTaylorMoment n
          (headCorrectionBand (actualWindowHead N b) (actualWindowTail N b) xi) s := by
  rw [signedTaylorMoment_congr n (completedBand_window_split_eventually N b hb xi hs)]
  exact signedTaylorMoment_add n (analyticAt_windowResidualCompletedBand N b hb xi hs)
    (analyticAt_headCorrectionBand _ _ (fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega) xi hs.le)

/-- The original logarithm-marked fixed filter preserves the complete
moving-head split with every factorial offset unchanged. -/
theorem filteredCompletedBand_eq_window_split (P : Polynomial ℂ) (N b : ℕ) (hb : 16 ≤ b + 1) (xi : ℝ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.filteredCompletedBand P N s xi =
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (windowResidualCompletedBand N b xi) s) N +
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1)
          (headCorrectionBand (actualWindowHead N b) (actualWindowTail N b) xi) s) N := by
  simp only [ZetaRieszFilteredCompletion.filteredCompletedBand, zetaMomentSequenceFilter,
    Polynomial.sum, moment_completedBand_eq_window_split N b hb xi hs, mul_add, Finset.sum_add_distrib]

/-- The new residual frequency kernel retains the compensated leading
quotient, its mixed correction and the entire signed completion boundary. -/
def windowResidualKernel (P : Polynomial ℂ) (N b : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  (phase (L * xi) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (windowResidualCompletedBand N b xi) s) N +
  phase (-(L * xi)) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (windowResidualCompletedBand N b (-xi)) s) N) /
      ((L : ℂ) * (xi : ℂ) ^ 2)

/-- Both physical phases of the literal finite band split exactly into
the new explicit residual and the full moving-head correction kernel. -/
theorem actual_kernel_eq_windowResidual_add_head (P : Polynomial ℂ) (N b : ℕ) (hb : 16 ≤ b + 1)
    {s : ℂ} (hs : 1 / 2 < s.re) (L xi : ℝ) :
    ZetaRieszPrimeFourier.bandPrimePair (zetaPrimeLogBand N)
      (fun n => zetaPrimeFilterKernel P N s n) L xi =
        windowResidualKernel P N b s L xi +
          headFilteredKernel (actualWindowHead N b) (actualWindowTail N b) P N s L xi := by
  rw [ZetaRieszFilteredCompletion.bandPrimePair_eq_filtered_completion,
    filteredCompletedBand_eq_window_split P N b hb xi hs, filteredCompletedBand_eq_window_split P N b hb (-xi) hs,
    headFilteredKernel_eq_pair (actualWindowHead N b) (actualWindowTail N b)
      (fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega) P N hs.le]
  unfold windowResidualKernel phase
  rw [show xi * L = L * xi by ring, show -xi * L = -(L * xi) by ring]
  ring

/-- The new remainder is genuinely integrable as the original finite
band kernel minus the independently integrable moving-head correction. -/
theorem integrable_windowResidualKernel (P : Polynomial ℂ) (N b : ℕ) (hb : 16 ≤ b + 1) {s : ℂ}
    (hs : 1 / 2 < s.re) (L : ℝ) : IntegrableOn (windowResidualKernel P N b s L) (Ioi 0) := by
  have hi := (ZetaRieszPrimeFourier.integrable_bandPrimePair (zetaPrimeLogBand N)
    (fun n => zetaPrimeFilterKernel P N s n) L).sub
      (integrable_headFilteredKernel (actualWindowHead N b) (actualWindowTail N b)
        (fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega) P N hs L)
  apply hi.congr
  filter_upwards [] with xi
  simp only [Pi.sub_apply]
  rw [actual_kernel_eq_windowResidual_add_head P N b hb hs]
  ring

/-- The explicitly unpaid response after removing the whole moving-head
correction, with the literal physical filter and signed boundary intact. -/
def windowResidualResponse (P : Polynomial ℂ) (N b : ℕ) (y L : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in Ioi 0, windowResidualKernel P N b (3 / 2 + Complex.I * y) L xi

/-- The literal original arithmetic band is exactly the new explicit
remainder plus the independently controlled full moving-head correction. -/
theorem actual_band_eq_windowResidual_response (P : Polynomial ℂ) (N b : ℕ) (hb : 16 ≤ b + 1) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      windowResidualResponse P N b y L + (1 / (2 * (Real.pi : ℂ))) *
        headFilteredResponse (actualWindowHead N b) (actualWindowTail N b) P N
          (3 / 2 + Complex.I * y) L := by
  have hs : 1 / 2 < (3 / 2 + Complex.I * (y : ℂ)).re := by norm_num
  have h16 : ∀ p ∈ actualWindowTail N b, 16 ≤ p := fun _ hp => by have := (Finset.mem_filter.mp hp).2; omega
  rw [ZetaRieszPrimeFourier.actual_band_eq_primePair_integral]
  simp_rw [actual_kernel_eq_windowResidual_add_head P N b hb hs]
  rw [integral_add (integrable_windowResidualKernel P N b hb hs L)
    (integrable_headFilteredKernel _ _ h16 P N hs L),
    ← headFilteredResponse_eq_integral _ _ h16 P N hs L]
  unfold windowResidualResponse
  ring

/-- An entire growing head can be deleted from the literal original
arithmetic band along a cofinal stride, with independently vanishing error.
The residual keeps its moving complementary quotient, all ordinary-prime
compensation, the mixed correction and the entire signed boundary. -/
theorem exists_stride_actual_band_sub_windowResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ d : ℕ, 0 < d ∧ Tendsto (fun n : ℕ => (u : ℂ) ^ (d * n + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u (d * n)))
        P (d * n) y - windowResidualResponse P (d * n) (n + 16) y
          (SquarefreeVaughanLogSource.length u (d * n)))) atTop (nhds 0) := by
  obtain ⟨d, hd0, hd⟩ := exists_stride_actual_window_correction_decay P y hu hu1
  refine ⟨d, hd0, ?_⟩
  have he (n : ℕ) : (u : ℂ) ^ (d * n + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u (d * n)))
        P (d * n) y - windowResidualResponse P (d * n) (n + 16) y
          (SquarefreeVaughanLogSource.length u (d * n))) =
      (1 / (2 * (Real.pi : ℂ))) * ((u : ℂ) ^ (d * n + 1) *
        headFilteredResponse (actualWindowHead (d * n) (n + 16)) (actualWindowTail (d * n) (n + 16))
          P (d * n) (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u (d * n))) := by
    rw [actual_band_eq_windowResidual_response P (d * n) (n + 16) (by omega)]
    ring
  simp_rw [he]
  simpa only [mul_zero] using hd.const_mul (1 / (2 * (Real.pi : ℂ)))

/-- The moving-window residual retains the literal hypothetical-zero
filter, source normalization and physical length along its integer stride. -/
def normalizedWindowResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (d n : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (d * n + 1) *
    windowResidualResponse (zetaRightHalfPoleJetFilter rho hrho) (d * n) (n + 16) rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) (d * n))

/-- The growing-head deletion preserves the exact negative multiplicity
source on a genuinely cofinal sequence of original orders. It proves no
independent lower floor for the compensated leading/mixed/boundary residual. -/
theorem exists_stride_normalizedWindowResidual_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ d : ℕ, 0 < d ∧ Tendsto (normalizedWindowResidual rho hrho d) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  obtain ⟨d, hd0, herror⟩ := exists_stride_actual_band_sub_windowResidual
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1
  refine ⟨d, hd0, ?_⟩
  have ht : Tendsto (fun n : ℕ => d * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simpa using Nat.mul_le_mul_right n (Nat.succ_le_of_lt hd0)) tendsto_id
  have hsource := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).comp ht
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at herror
  have h := hsource.sub herror
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with n
  unfold normalizedWindowResidual
  dsimp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszEulerWindowDeletion
