/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerMoments
import RiemannGaussian.ZetaRieszFilteredCompletion

/-!
# Independent deletion of the full Euler correction from the actual band

The exact finite Euler quotient retains the entire small-prime head. The
completed response splits into its standalone correction and an explicit
remainder containing the leading response, prime compensation, mixed
interaction and signed completion boundary. This analytic identity passes
through every factorial shift, the fixed filter, both physical phases and
the ordinary frequency integral. The normalized difference between the
literal original arithmetic band and that remainder tends to zero.
The joint independent floor for the remaining signed response is open.
-/

namespace RiemannGaussian.ZetaRieszEulerCorrectionDeletion
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open ZetaRieszEulerQuotient ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerCutoff
open ZetaRieszEulerMoments

/-- The original filter applied before the frequency integral, with its
literal prime-frequency orientation and inverse-length normalization. -/
def filteredKernel (Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  zetaMomentSequenceFilter P (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1)
    (fun z => shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) (-L) xi /
      (xi : ℂ) ^ 2) s) N / (L : ℂ)

/-- Every summand of the actual fixed filter is integrable, justifying
the finite filter--integral exchange used for the correction response. -/
theorem integrable_filteredKernel (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 ≤ s.re - R) (L : ℝ) :
    IntegrableOn (filteredKernel Q P N s L) (Ioi 0) := by
  unfold filteredKernel zetaMomentSequenceFilter Polynomial.sum
  apply Integrable.div_const
  apply integrable_finsetSum
  intro k _hk
  exact ((integrable_actual_shiftedCorrection_moment Q h16 hR hhalf (-L)
    (N + k + 1)).const_mul _).const_mul _

/-- The bounded response is exactly the original fixed filter integrated
after applying all its factorial shifts, with genuine integrability. -/
theorem filteredResponse_eq_integral (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hhalf : 1 / 2 ≤ s.re - R) (L : ℝ) :
    filteredResponse Q P N s L = ∫ xi : ℝ in Ioi 0, filteredKernel Q P N s L xi := by
  unfold filteredResponse filteredKernel zetaMomentSequenceFilter Polynomial.sum momentResponse
  rw [integral_div, integral_finsetSum P.support (fun k _hk =>
    ((integrable_actual_shiftedCorrection_moment Q h16 hR hhalf (-L)
      (N + k + 1)).const_mul _).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _hk => by ring)

/-- Only the fixed finite small-prime head lies outside the quarter-disk
correction product; its contribution remains in the leading response. -/
def largePrimes (m : ℕ) : Finset ℕ := m.primeFactors.filter (fun p => 16 ≤ p)

/-- The leading response retains the entire small-prime head and exact
finite Euler quotient, with every original complex prime phase. -/
def leadingResponse (m : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (∏ p ∈ m.primeFactors.filter (fun p => p < 16),
    (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))) *
    ((∏ p ∈ largePrimes m, (1 - zetaPrimeFeature s p * zetaPrimeFeature (Complex.I * xi) p)) /
      (∏ p ∈ largePrimes m, (1 - zetaPrimeFeature s p)))

/-- The whole finite prime character is reconstructed exactly, including
small primes and the original orientation of both frequencies. -/
theorem full_character_eq_leading_correction (m : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    (∏ p ∈ m.primeFactors,
      (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))) =
        leadingResponse m s xi *
          correctionProduct (largePrimes m) (zetaPrimeFeature s) (fun p => Real.log p) (-xi) := by
  have hpart := Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p < 16)
    (fun p => (1 + zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)))
  simp only [Nat.not_lt] at hpart
  have ht := actual_character_eq_euler_quotient_correction (largePrimes m)
    (fun _ hp => (Finset.mem_filter.mp hp).2) hs (-xi)
  simp_rw [← ZetaRieszCompositeProduct.imaginary_feature_eq_character] at ht
  rw [← hpart]
  change _ * (∏ p ∈ largePrimes m, _) = _
  rw [ht]
  simp only [leadingResponse, mul_assoc]

/-- The removable correction is exposed additively without dropping its
mixed leading coupling, the unit subtraction or any ordinary-prime term. -/
theorem compositeResponse_eq_leading_split (m : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    ZetaRieszCompositeProduct.compositeResponse m s xi =
      (leadingResponse m s xi - 1 - ∑ p ∈ m.primeFactors,
        zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)) +
      (correctionProduct (largePrimes m) (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 1) +
      (leadingResponse m s xi - 1) *
        (correctionProduct (largePrimes m) (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 1) := by
  unfold ZetaRieszCompositeProduct.compositeResponse
  rw [full_character_eq_leading_correction m hs xi]
  ring

/-- The precise remainder after isolating the proved-decaying correction:
leading quotient and small-prime head, ordinary-prime compensation, mixed
coupling, and the entire signed off-band boundary. -/
def residualCompletedBand (N : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  (leadingResponse (primorial (2 ^ (32 * N))) s xi - 1 -
    ∑ p ∈ (primorial (2 ^ (32 * N))).primeFactors,
      zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p)) +
  (leadingResponse (primorial (2 ^ (32 * N))) s xi - 1) *
    (correctionProduct (originalCorrectionPrimes N) (zetaPrimeFeature s)
      (fun p => Real.log p) (-xi) - 1) -
  ∑ n ∈ (((primorial (2 ^ (32 * N))).divisors.erase 1).filter
    (fun n => ¬ n.Prime)).filter (fun n => n ∉ zetaPrimeLogBand N),
      zetaPrimeFeature s n * ZetaRieszPrimeFourier.primeProduct n xi

/-- The original completed band splits into the bounded correction and
its full explicit remainder. Every completion-boundary sign is retained. -/
theorem completedBand_eq_residual_add_correction (N : ℕ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    ZetaRieszFilteredCompletion.completedBand N xi s =
      residualCompletedBand N xi s +
        (correctionProduct (originalCorrectionPrimes N) (zetaPrimeFeature s)
          (fun p => Real.log p) (-xi) - 1) := by
  unfold ZetaRieszFilteredCompletion.completedBand
  rw [compositeResponse_eq_leading_split _ hs xi]
  unfold residualCompletedBand originalCorrectionPrimes largePrimes
  ring

/-- The isolated correction keeps the exact orientation used by the
completed band before its physical Fourier phases are applied. -/
def correctionBand (N : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  correctionProduct (originalCorrectionPrimes N) (zetaPrimeFeature s)
    (fun p => Real.log p) (-xi) - 1

/-- The isolated band correction is analytic throughout the required
arithmetic half-plane, so all factorial shifts are justified. -/
theorem analyticAt_correctionBand (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    AnalyticAt ℂ (correctionBand N xi) s :=
  (analyticAt_actual_correctionProduct (originalCorrectionPrimes N)
    (fun _ hp => (Finset.mem_filter.mp hp).2) hs (-xi)).sub analyticAt_const

/-- The source-exact completed band is an entire finite Dirichlet
polynomial, including its signed boundary subtraction. -/
theorem analyticAt_completedBand (N : ℕ) (xi : ℝ) (s : ℂ) :
    AnalyticAt ℂ (ZetaRieszFilteredCompletion.completedBand N xi) s := by
  have hd : Differentiable ℂ (ZetaRieszFilteredCompletion.completedBand N xi) := by
    rw [ZetaRieszFilteredCompletion.completedBand_eq_finite]
    unfold zetaFiniteDirichletSeries zetaPrimeFeature
    fun_prop
  exact hd.analyticAt s

/-- The exact completed-band split holds as a local analytic identity,
not merely at the center where the factorial filter is evaluated. -/
theorem completedBand_split_eventually (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.completedBand N xi =ᶠ[nhds s]
      (fun z => residualCompletedBand N xi z + correctionBand N xi z) := by
  have hh : ∀ᶠ z : ℂ in nhds s, (1 / 2 : ℝ) < z.re :=
    Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hs)
  filter_upwards [hh] with z hz
  exact completedBand_eq_residual_add_correction N hz.le xi

/-- The explicit leading/mixed/boundary remainder inherits analyticity
from the exact source identity; no convergence assertion is introduced. -/
theorem analyticAt_residualCompletedBand (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (residualCompletedBand N xi) s := by
  have he : (fun z => ZetaRieszFilteredCompletion.completedBand N xi z - correctionBand N xi z)
      =ᶠ[nhds s] residualCompletedBand N xi := by
    filter_upwards [completedBand_split_eventually N xi hs] with z hz
    rw [hz]
    ring
  exact ((analyticAt_completedBand N xi s).sub (analyticAt_correctionBand N xi hs.le)).congr he

/-- Every original factorial moment splits exactly into its bounded
correction coordinate and the explicit leading/mixed/boundary coordinate. -/
theorem moment_completedBand_eq_split (N : ℕ) (xi : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) (n : ℕ) :
    signedTaylorMoment n (ZetaRieszFilteredCompletion.completedBand N xi) s =
      signedTaylorMoment n (residualCompletedBand N xi) s +
        signedTaylorMoment n (correctionBand N xi) s := by
  rw [signedTaylorMoment_congr n (completedBand_split_eventually N xi hs)]
  exact signedTaylorMoment_add n (analyticAt_residualCompletedBand N xi hs)
    (analyticAt_correctionBand N xi hs.le)

/-- The complete original logarithm-marked fixed filter passes through
the exact split, retaining all factorial shifts and every residual term. -/
theorem filteredCompletedBand_eq_split (P : Polynomial ℂ) (N : ℕ) (xi : ℝ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ZetaRieszFilteredCompletion.filteredCompletedBand P N s xi =
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (residualCompletedBand N xi) s) N +
      zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (correctionBand N xi) s) N := by
  simp only [ZetaRieszFilteredCompletion.filteredCompletedBand, zetaMomentSequenceFilter,
    Polynomial.sum, moment_completedBand_eq_split N xi hs, mul_add, Finset.sum_add_distrib]

/-- Constant Fourier weights and their common denominator commute with
every signed factorial moment after both analytic channels are retained. -/
theorem moment_weighted_pair_div (n : ℕ) {fp fm : ℂ → ℂ} {s : ℂ}
    (hp : AnalyticAt ℂ fp s) (hm : AnalyticAt ℂ fm s) (Vp Vm d : ℂ) :
    signedTaylorMoment n (fun z => (Vp * fp z + Vm * fm z) / d) s =
      (Vp * signedTaylorMoment n fp s + Vm * signedTaylorMoment n fm s) / d := by
  have he : (fun z => (Vp * fp z + Vm * fm z) / d) =
      (fun z => d⁻¹ * (Vp * fp z + Vm * fm z)) := by funext z; ring
  have hVp : AnalyticAt ℂ (fun z => Vp * fp z) s := analyticAt_const.mul hp
  have hVm : AnalyticAt ℂ (fun z => Vm * fm z) s := analyticAt_const.mul hm
  rw [he, signedTaylorMoment_const_mul,
    signedTaylorMoment_add n hVp hVm,
    signedTaylorMoment_const_mul, signedTaylorMoment_const_mul]
  ring

/-- The bounded moment has exactly the original two Fourier phases,
including the negative prime-character orientation in its positive branch. -/
theorem moment_shiftedCorrection_eq_pair (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) (n : ℕ) :
    signedTaylorMoment n (fun z =>
      shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) (-L) xi / (xi : ℂ) ^ 2) s =
      (phase (L * xi) * signedTaylorMoment n (fun z =>
        correctionProduct Q (zetaPrimeFeature z) (fun p => Real.log p) (-xi) - 1) s +
      phase (-(L * xi)) * signedTaylorMoment n (fun z =>
        correctionProduct Q (zetaPrimeFeature z) (fun p => Real.log p) xi - 1) s) / (xi : ℂ) ^ 2 := by
  have he : (fun z => shiftedCorrection Q (zetaPrimeFeature z) (fun p => Real.log p) (-L) xi /
      (xi : ℂ) ^ 2) = (fun z =>
        (phase (L * xi) * (correctionProduct Q (zetaPrimeFeature z) (fun p => Real.log p) (-xi) - 1) +
        phase (-(L * xi)) * (correctionProduct Q (zetaPrimeFeature z) (fun p => Real.log p) xi - 1)) /
          (xi : ℂ) ^ 2) := by
    funext z
    unfold shiftedCorrection
    simp only [neg_mul, neg_neg, add_comm]
  rw [he]
  exact moment_weighted_pair_div n
    ((analyticAt_actual_correctionProduct Q h16 hs (-xi)).sub analyticAt_const)
    ((analyticAt_actual_correctionProduct Q h16 hs xi).sub analyticAt_const) _ _ _

/-- The original fixed-filter correction inside the completed-band
split is exactly the frequency kernel whose response has proved decay. -/
theorem filteredKernel_eq_original_correction_pair (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) :
    filteredKernel (originalCorrectionPrimes N) P N s L xi =
      (phase (L * xi) * zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (correctionBand N xi) s) N +
      phase (-(L * xi)) * zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (correctionBand N (-xi)) s) N) /
          ((L : ℂ) * (xi : ℂ) ^ 2) := by
  have h16 : ∀ p ∈ originalCorrectionPrimes N, 16 ≤ p := fun _ hp => (Finset.mem_filter.mp hp).2
  unfold correctionBand
  simp only [filteredKernel, zetaMomentSequenceFilter, Polynomial.sum,
    moment_shiftedCorrection_eq_pair _ h16 hs, neg_neg, mul_add, add_div,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _hk <;> ring

/-- The exact residual kernel contains the whole leading response,
prime compensation, mixed correction and signed completion boundary. -/
def residualKernel (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  (phase (L * xi) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (residualCompletedBand N xi) s) N +
  phase (-(L * xi)) * zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (residualCompletedBand N (-xi)) s) N) /
      ((L : ℂ) * (xi : ℂ) ^ 2)

/-- The literal finite-band Fourier kernel splits into the full explicit
residual and the independently bounded correction, with both phases intact. -/
theorem actual_kernel_eq_residual_add_correction (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 / 2 < s.re) (L xi : ℝ) :
    ZetaRieszPrimeFourier.bandPrimePair (zetaPrimeLogBand N)
      (fun n => zetaPrimeFilterKernel P N s n) L xi =
        residualKernel P N s L xi + filteredKernel (originalCorrectionPrimes N) P N s L xi := by
  rw [ZetaRieszFilteredCompletion.bandPrimePair_eq_filtered_completion,
    filteredCompletedBand_eq_split P N xi hs, filteredCompletedBand_eq_split P N (-xi) hs,
    filteredKernel_eq_original_correction_pair P N hs.le]
  unfold residualKernel phase
  rw [show xi * L = L * xi by ring, show -xi * L = -(L * xi) by ring]
  ring

/-- The explicit residual has an ordinary frequency integral because it
is the original integrable band kernel minus the proved-integrable correction. -/
theorem integrable_residualKernel (P : Polynomial ℂ) (N : ℕ) {s : ℂ}
    (hs : 1 / 2 < s.re) (L : ℝ) : IntegrableOn (residualKernel P N s L) (Ioi 0) := by
  let R : ℝ := (s.re - 1 / 2) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hh : 1 / 2 ≤ s.re - R := by dsimp [R]; linarith
  have hi := (ZetaRieszPrimeFourier.integrable_bandPrimePair (zetaPrimeLogBand N)
    (fun n => zetaPrimeFilterKernel P N s n) L).sub
      (integrable_filteredKernel (originalCorrectionPrimes N)
        (fun _ hp => (Finset.mem_filter.mp hp).2) P N hR hh L)
  apply hi.congr
  filter_upwards [] with xi
  simp only [Pi.sub_apply]
  rw [actual_kernel_eq_residual_add_correction P N hs]
  ring

/-- The full explicitly unpaid response, after the original factorial
filter, both physical phases and the signed completion boundary. -/
def residualResponse (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in Ioi 0, residualKernel P N (3 / 2 + Complex.I * y) L xi

/-- The literal original arithmetic band is exactly the explicit residual
plus the independently controlled full correction response. -/
theorem actual_band_eq_residual_response (P : Polynomial ℂ) (N : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      residualResponse P N y L + (1 / (2 * (Real.pi : ℂ))) *
        filteredResponse (originalCorrectionPrimes N) P N (3 / 2 + Complex.I * y) L := by
  have hs : 1 / 2 < (3 / 2 + Complex.I * (y : ℂ)).re := by norm_num
  have hh : 1 / 2 ≤ (3 / 2 + Complex.I * (y : ℂ)).re - (1 / 2 : ℝ) := by norm_num
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have h16 : ∀ p ∈ originalCorrectionPrimes N, 16 ≤ p := fun _ hp => (Finset.mem_filter.mp hp).2
  rw [ZetaRieszPrimeFourier.actual_band_eq_primePair_integral]
  simp_rw [actual_kernel_eq_residual_add_correction P N hs]
  rw [integral_add (integrable_residualKernel P N hs L)
    (integrable_filteredKernel _ h16 P N hR hh L),
    ← filteredResponse_eq_integral _ h16 P N hR hh L]
  unfold residualResponse
  ring

/-- Removing the complete standalone Euler correction changes the actual
normalized arithmetic carrier by a quantity tending to zero. All other
leading, mixed, prime-compensation and boundary terms stay in the residual. -/
theorem tendsto_actual_band_sub_residual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
        P N y - residualResponse P N y (SquarefreeVaughanLogSource.length u N)))
          Filter.atTop (nhds 0) := by
  have he (N : ℕ) : (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
        P N y - residualResponse P N y (SquarefreeVaughanLogSource.length u N)) =
      (1 / (2 * (Real.pi : ℂ))) * ((u : ℂ) ^ (N + 1) *
        filteredResponse (originalCorrectionPrimes N) P N (3 / 2 + Complex.I * y)
          (SquarefreeVaughanLogSource.length u N)) := by
    rw [actual_band_eq_residual_response]
    ring
  simp_rw [he]
  simpa only [mul_zero] using (tendsto_original_correction_response P y hu hu1).const_mul
    (1 / (2 * (Real.pi : ℂ)))

end
end RiemannGaussian.ZetaRieszEulerCorrectionDeletion
