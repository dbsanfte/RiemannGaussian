/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerMultiplier

/-!
# Exact finite Fourier heads on the full Euler correction

Every finite head expands with exact signed entire coefficients and subset log frequencies. The expansion passes through every factorial moment, the original filter and the ordinary frequency integral. The actual fixed small-prime head is covered with no arithmetic bound assumed.
-/

namespace RiemannGaussian.ZetaRieszEulerHead
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter
open ZetaRieszEulerCutoff ZetaRieszEulerMoments ZetaRieszEulerCorrectionDeletion
open ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerMultiplier

/-- Every subset of a fixed prime head retains its exact signed entire
coefficient in the finite Fourier expansion. -/
def headCoefficient (S T : Finset ℕ) (s : ℂ) : ℂ :=
  (∏ p ∈ T, -zetaPrimeFeature s p) * ∏ p ∈ S \ T, (1 + zetaPrimeFeature s p)

/-- The logarithmic frequency of a head subset is retained exactly. -/
def headFrequency (T : Finset ℕ) : ℝ := ∑ p ∈ T, Real.log p

/-- The full fixed-head character retains all its local prime phases. -/
def headCharacter (S : Finset ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∏ p ∈ S, (1 + zetaPrimeFeature s p * (1 - phase (Real.log p * xi)))

/-- The finite-head coefficients are entire, so their fixed-circle
bounds are available independently of the arithmetic tail. -/
theorem differentiable_headCoefficient (S T : Finset ℕ) : Differentiable ℂ (headCoefficient S T) := by
  unfold headCoefficient zetaPrimeFeature
  fun_prop

/-- Multiplying the literal prime phases preserves the exact subset
logarithmic frequency, without discarding any relative phase. -/
theorem prod_head_phase (T : Finset ℕ) (xi : ℝ) :
    (∏ p ∈ T, phase (Real.log p * xi)) = phase (headFrequency T * xi) := by
  unfold phase
  rw [← Complex.exp_sum]
  congr 1
  simp only [headFrequency, Finset.sum_mul, Complex.ofReal_sum]

/-- Every fixed head has an exact finite Fourier expansion with entire
coefficients. This covers all finite heads, not a selected weight family. -/
theorem headCharacter_eq_expansion (S : Finset ℕ) (s : ℂ) (xi : ℝ) :
    headCharacter S s xi =
      ∑ T ∈ S.powerset, headCoefficient S T s * phase (headFrequency T * xi) := by
  have he : headCharacter S s xi =
      ∏ p ∈ S, ((-zetaPrimeFeature s p * phase (Real.log p * xi)) + (1 + zetaPrimeFeature s p)) := by
    apply Finset.prod_congr rfl
    intro p _hp
    ring
  rw [he, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro T _hT
  rw [Finset.prod_mul_distrib, prod_head_phase]
  unfold headCoefficient
  ring

/-- The full small-head multiplier remains coupled to both physical
phases of the Euler correction before differentiation and integration. -/
def headKernel (S Q : Finset ℕ) (L xi : ℝ) (s : ℂ) : ℂ :=
  (phase (L * xi) * headCharacter S s (-xi) *
    (correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 1) +
  phase (-(L * xi)) * headCharacter S s xi *
    (correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi - 1)) / (xi : ℂ) ^ 2

/-- The literal finite-head action is precisely a coupled finite sum of
the weighted shifted corrections already covered by the decay theorem. -/
theorem headKernel_eq_sum_weighted (S Q : Finset ℕ) (L xi : ℝ) (s : ℂ) :
    headKernel S Q L xi s =
      ∑ T ∈ S.powerset, weightedKernel (headCoefficient S T) Q (headFrequency T) L xi s := by
  unfold headKernel
  rw [headCharacter_eq_expansion, headCharacter_eq_expansion]
  simp only [Finset.mul_sum, Finset.sum_mul, add_div, Finset.sum_div, mul_neg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _hT
  unfold weightedKernel shiftedCorrection
  have hp : phase ((headFrequency T - L) * xi) =
      phase (headFrequency T * xi) * phase (-(L * xi)) := by
    rw [show (headFrequency T - L) * xi = headFrequency T * xi + -(L * xi) by ring,
      phase_add]
  have hn : phase (-((headFrequency T - L) * xi)) =
      phase (L * xi) * phase (-(headFrequency T * xi)) := by
    rw [show -((headFrequency T - L) * xi) = L * xi + -(headFrequency T * xi) by ring,
      phase_add]
  rw [hp, hn]
  ring

/-- The exact finite Fourier expansion passes through every factorial
moment while retaining the entire coefficients inside the derivatives. -/
theorem moment_headKernel_eq_sum (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) (n : ℕ) :
    signedTaylorMoment n (headKernel S Q L xi) s =
      ∑ T ∈ S.powerset,
        signedTaylorMoment n (weightedKernel (headCoefficient S T) Q (headFrequency T) L xi) s := by
  have he : headKernel S Q L xi = fun z =>
      ∑ T ∈ S.powerset, weightedKernel (headCoefficient S T) Q (headFrequency T) L xi z := by
    funext z
    exact headKernel_eq_sum_weighted S Q L xi z
  rw [he]
  exact signedTaylorMoment_sum _ n _ (fun T _hT =>
    analyticAt_weightedKernel _ (differentiable_headCoefficient S T) Q h16 hs _ L xi)

/-- A fixed entire coefficient requires no additional integrability
premise anywhere strictly to the right of the correction boundary. -/
theorem integrable_weightedMoment_of_half (A : ℂ → ℂ) (hA : Differentiable ℂ A)
    (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re)
    (delta L : ℝ) (n : ℕ) :
    IntegrableOn (fun xi : ℝ => signedTaylorMoment n (weightedKernel A Q delta L xi) s)
      (Ioi 0) := by
  let R : ℝ := (s.re - 1 / 2) / 2
  obtain ⟨C, _hC0, hC⟩ := exists_coefficient_circle_bound A hA s R
  exact integrable_weightedMoment A hA Q h16 (show 0 < R by dsimp [R]; linarith)
    (show 1 / 2 ≤ s.re - R by dsimp [R]; linarith) hC delta L n

/-- The full finite-head moment uses the original physical denominator. -/
def headMomentResponse (S Q : Finset ℕ) (s : ℂ) (L : ℝ) (n : ℕ) : ℂ :=
  (∫ xi : ℝ in Ioi 0, signedTaylorMoment n (headKernel S Q L xi) s) / (L : ℂ)

/-- Genuine integrability justifies the finite Fourier expansion inside
the original frequency integral at every factorial order. -/
theorem headMomentResponse_eq_sum (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1 / 2 < s.re) (L : ℝ) (n : ℕ) :
    headMomentResponse S Q s L n =
      ∑ T ∈ S.powerset, weightedMomentResponse (headCoefficient S T) Q s (headFrequency T) L n := by
  unfold headMomentResponse weightedMomentResponse
  simp_rw [moment_headKernel_eq_sum S Q h16 hs.le]
  rw [integral_finsetSum S.powerset (fun T _hT =>
    integrable_weightedMoment_of_half _ (differentiable_headCoefficient S T) Q h16 hs _ L n),
    Finset.sum_div]

/-- The exact original fixed factorial filter acts on the complete
finite-head correction, retaining its logarithmic mark. -/
def headFilteredResponse (S Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * headMomentResponse S Q s L (k + 1)) N

/-- All head phases stay coupled through the complete fixed filter;
every shifted factorial coordinate is preserved in this exact identity. -/
theorem headFilteredResponse_eq_sum (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) (L : ℝ) :
    headFilteredResponse S Q P N s L =
      ∑ T ∈ S.powerset, weightedFilteredResponse (headCoefficient S T) Q P N s (headFrequency T) L := by
  simp only [headFilteredResponse, weightedFilteredResponse, zetaMomentSequenceFilter,
    Polynomial.sum, headMomentResponse_eq_sum S Q h16 hs, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Every fixed finite small-prime head, including all its mixed local
phases, preserves source-scale decay of the full correction at the actual
growing physical cutoff and for every fixed factorial polynomial filter. -/
theorem tendsto_headFilteredResponse (S : Finset ℕ) (P : Polynomial ℂ) (y : ℝ)
    (Q : ℕ → Finset ℕ) (h16 : ∀ N p, p ∈ Q N → 16 ≤ p)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      headFilteredResponse S (Q N) P N (3 / 2 + Complex.I * y)
        (SquarefreeVaughanLogSource.length u N)) Filter.atTop (nhds 0) := by
  have hs : 1 / 2 < (3 / 2 + Complex.I * (y : ℂ)).re := by norm_num
  simp_rw [headFilteredResponse_eq_sum S _ (h16 _) P _ hs]
  exact tendsto_finite_weighted_correction S.powerset (headCoefficient S)
    (fun T _hT => differentiable_headCoefficient S T) headFrequency P y Q h16 hu hu1

/-- Every differentiated head kernel is ordinarily integrable because
its exact finite Fourier expansion consists of integrable weighted kernels. -/
theorem integrable_headMoment (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1 / 2 < s.re) (L : ℝ) (n : ℕ) :
    IntegrableOn (fun xi : ℝ => signedTaylorMoment n (headKernel S Q L xi) s) (Ioi 0) := by
  simp_rw [moment_headKernel_eq_sum S Q h16 hs.le]
  exact integrable_finsetSum _ (fun T _hT =>
    integrable_weightedMoment_of_half _ (differentiable_headCoefficient S T) Q h16 hs _ L n)

/-- The full fixed-head filter before integrating the original frequency
variable, with its original inverse-length normalization. -/
def headFilteredKernel (S Q : Finset ℕ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  zetaMomentSequenceFilter P
    (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headKernel S Q L xi) s) N / (L : ℂ)

/-- Every term of the full finite-head filter is genuinely integrable,
including all factorial offsets and both physical Fourier phases. -/
theorem integrable_headFilteredKernel (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) (L : ℝ) :
    IntegrableOn (headFilteredKernel S Q P N s L) (Ioi 0) := by
  unfold headFilteredKernel zetaMomentSequenceFilter Polynomial.sum
  apply Integrable.div_const
  exact integrable_finsetSum _ (fun k _hk =>
    ((integrable_headMoment S Q h16 hs L (N + k + 1)).const_mul _).const_mul _)

/-- The proved-decaying head response is the literal frequency integral
of the original fixed filter, with all integral exchanges justified. -/
theorem headFilteredResponse_eq_integral (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) (L : ℝ) :
    headFilteredResponse S Q P N s L =
      ∫ xi : ℝ in Ioi 0, headFilteredKernel S Q P N s L xi := by
  unfold headFilteredResponse headFilteredKernel zetaMomentSequenceFilter Polynomial.sum headMomentResponse
  rw [integral_div, integral_finsetSum P.support (fun k _hk =>
    ((integrable_headMoment S Q h16 hs L (N + k + 1)).const_mul _).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _hk => by ring)

/-- The original finite prime universe has a literal head below sixteen. -/
def actualSmallPrimes (N : ℕ) : Finset ℕ :=
  (primorial (2 ^ (32 * N))).primeFactors.filter (fun p => p < 16)

/-- From the first nonzero order onward the actual small-prime head is
exactly the fixed set of primes at most fifteen. No limiting identification
or approximation of the original prime universe is used. -/
theorem actualSmallPrimes_eq {N : ℕ} (hN : 1 ≤ N) : actualSmallPrimes N = Nat.primesLE 15 := by
  have hb : 16 ≤ 2 ^ (32 * N) := by
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (32 * N) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold actualSmallPrimes
  rw [primeFactors_primorial]
  ext p
  simp only [Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_hpN, hp⟩, hp16⟩
    exact ⟨by omega, hp⟩
  · rintro ⟨hp15, hp⟩
    exact ⟨⟨by omega, hp⟩, by omega⟩

/-- The complete head-times-correction from the actual prime universe
decays under the original physical cutoff, source normalization and every
fixed factorial polynomial filter. The growing leading quotient is absent. -/
theorem tendsto_actual_headFilteredResponse (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      headFilteredResponse (actualSmallPrimes N) (originalCorrectionPrimes N) P N
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N))
      Filter.atTop (nhds 0) := by
  apply (tendsto_headFilteredResponse (Nat.primesLE 15) P y originalCorrectionPrimes
    (fun _ _ hp => (Finset.mem_filter.mp hp).2) hu hu1).congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [actualSmallPrimes_eq hN]

/-- The exact head-weighted correction has the negative prime-frequency
orientation used by the original completed arithmetic band. -/
def headCorrectionBand (S Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  headCharacter S s (-xi) *
    (correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 1)

/-- The entire finite head preserves local analyticity of the complete
correction in the half-plane needed for the original factorial moments. -/
theorem analyticAt_headCorrectionBand (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (xi : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) : AnalyticAt ℂ (headCorrectionBand S Q xi) s := by
  have hhead : Differentiable ℂ (fun z => headCharacter S z (-xi)) := by
    unfold headCharacter zetaPrimeFeature
    fun_prop
  exact (hhead.analyticAt s).mul
    ((analyticAt_actual_correctionProduct Q h16 hs (-xi)).sub analyticAt_const)

/-- Both original physical phases act on the actual head-weighted
correction inside every factorial derivative. -/
theorem moment_headKernel_eq_pair (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) (n : ℕ) :
    signedTaylorMoment n (headKernel S Q L xi) s =
      (phase (L * xi) * signedTaylorMoment n (headCorrectionBand S Q xi) s +
      phase (-(L * xi)) * signedTaylorMoment n (headCorrectionBand S Q (-xi)) s) /
        (xi : ℂ) ^ 2 := by
  have he : headKernel S Q L xi = fun z =>
      (phase (L * xi) * headCorrectionBand S Q xi z +
        phase (-(L * xi)) * headCorrectionBand S Q (-xi) z) / (xi : ℂ) ^ 2 := by
    funext z
    simp only [headKernel, headCorrectionBand, neg_neg, mul_assoc]
  rw [he]
  exact moment_weighted_pair_div n (analyticAt_headCorrectionBand S Q h16 xi hs)
    (analyticAt_headCorrectionBand S Q h16 (-xi) hs) _ _ _

/-- The integrable finite-head kernel is precisely the original paired
fixed filter on the head-weighted correction, with its physical denominator. -/
theorem headFilteredKernel_eq_pair (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (L xi : ℝ) :
    headFilteredKernel S Q P N s L xi =
      (phase (L * xi) * zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headCorrectionBand S Q xi) s) N +
      phase (-(L * xi)) * zetaMomentSequenceFilter P
        (fun k => ((k + 1 : ℕ) : ℂ) * signedTaylorMoment (k + 1) (headCorrectionBand S Q (-xi)) s) N) /
          ((L : ℂ) * (xi : ℂ) ^ 2) := by
  simp only [headFilteredKernel, zetaMomentSequenceFilter, Polynomial.sum,
    moment_headKernel_eq_pair S Q h16 hs, mul_add, add_div,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _hk <;> ring

end
end RiemannGaussian.ZetaRieszEulerHead
