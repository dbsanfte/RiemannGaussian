/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeClearedSource
import RiemannGaussian.GaussianSimplePoleHeat

/-!
# The selected source inside the complete cleared prime heat

The original cleared prime heat, including every Leibniz and Hermite term,
splits exactly into the negative multiplicity times the evaluated Gaussian
pole factor and the actual residual heat. A quadratic width keeps at least
exp(-c) of the pole contribution at every order. No estimate for the whole
residual heat or independent arithmetic lower bound is assumed or claimed.
-/

namespace RiemannGaussian.SquarefreeEulerQuadratic
noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
open GaussianPolynomialTransport GaussianSimplePoleHeat

/-- The actual cleared prime continuation after its selected principal part
has been subtracted. Its definition retains the whole prime response. -/
def clearedPrimeRemainder (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  (normalizedPrimeTailClearingPolynomial D S rho).eval z * primeTailContinuation D S z +
    (analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1)

private theorem euler_ne_zero {s : ℂ} (hs : 1 < s.re) (rho : NontrivialZetaZero) : s ≠ rho.1 := by
  intro h
  rw [h] at hs
  linarith [NontrivialZetaZero.re_lt_one rho]

/-- The actual residual is analytic throughout the Euler half-plane;
neither its Dirichlet continuation nor the selected denominator is singular. -/
theorem analyticAt_clearedPrimeRemainder (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero)
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (clearedPrimeRemainder D S rho) s := by
  have hq := (normalizedPrimeTailClearingPolynomial D S rho).differentiable.analyticAt s
  exact (hq.mul (analyticAt_primeTailContinuation D S hs)).add
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (euler_ne_zero hs rho)))

/-- Every signed factorial residual retains the exact actual prime
moment and the complete selected principal-part moment. -/
theorem signedTaylorMoment_clearedPrimeRemainder {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    signedTaylorMoment N (clearedPrimeRemainder D S rho) s =
      clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N s +
        (analyticZetaZeroMultiplicity rho : ℂ) * ((s - rho.1)⁻¹) ^ (N + 1) := by
  have hq := (normalizedPrimeTailClearingPolynomial D S rho).differentiable.analyticAt s
  have hp : AnalyticAt ℂ (fun z ↦ (analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (euler_ne_zero hs rho))
  have hprod : AnalyticAt ℂ (fun z ↦ (normalizedPrimeTailClearingPolynomial D S rho).eval z *
      primeTailContinuation D S z) s := hq.mul (analyticAt_primeTailContinuation D S hs)
  unfold clearedPrimeRemainder
  rw [signedTaylorMoment_add N hprod hp,
    ← clearedPrimeMoment_eq_continuation _ hD S hS N hs]
  simp_rw [div_eq_mul_inv]
  rw [signedTaylorMoment_const_mul, signedTaylorMoment_inv_sub]

/-- The exact real distance between the Euler center and the selected zero. -/
def clearedPrimeSourceDistance (rho : NontrivialZetaZero) : ℝ := 3 / 2 - rho.1.re

/-- Every selected nontrivial zero has strictly positive Euler distance. -/
theorem clearedPrimeSourceDistance_pos (rho : NontrivialZetaZero) :
    0 < clearedPrimeSourceDistance rho := by
  unfold clearedPrimeSourceDistance
  linarith [NontrivialZetaZero.re_lt_one rho]

private theorem shifted_center_sub (rho : NontrivialZetaZero) (y : ℝ) :
    zetaWronskianMomentCenter rho - I * y - rho.1 = (clearedPrimeSourceDistance rho : ℂ) - I * y := by
  rw [sub_right_comm, zetaWronskianMomentCenter_sub]
  rfl

/-- The whole residual moment is Gaussian integrable on its actual Euler
line, using the original full prime moment and the exact pole integral. -/
theorem integrable_clearedPrimeRemainder_heat {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (N : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun y : ℝ ↦ (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)) := by
  have hprim := integrable_clearedPrimeMoment_heat hB
    (normalizedPrimeTailClearingPolynomial D S rho) D S hS N
    (by norm_num [zetaWronskianMomentCenter] : 1 < (zetaWronskianMomentCenter rho).re)
  have hpole := (integrable_poleMoment N (clearedPrimeSourceDistance_pos rho) hB).const_mul
    (analyticZetaZeroMultiplicity rho : ℂ)
  have he (y : ℝ) : (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y) =
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
        clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N
          (zetaWronskianMomentCenter rho - I * y) +
        (analyticZetaZeroMultiplicity rho : ℂ) * ((Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
          (((clearedPrimeSourceDistance rho : ℂ) - I * y)⁻¹) ^ (N + 1)) := by
    rw [signedTaylorMoment_clearedPrimeRemainder hD S hS rho N (by norm_num [zetaWronskianMomentCenter]),
      shifted_center_sub]
    ring
  simp_rw [he]
  exact hprim.add hpole

/-- The entire corrected prime arithmetic heat with its unchanged
geometric source normalization. -/
def normalizedClearedPrimeHeat (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero) (N : ℕ) (B : ℝ) : ℂ :=
  (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
    clearedHeatPrimeResponse B (normalizedPrimeTailClearingPolynomial D S rho) D S N
      (zetaWronskianMomentCenter rho)

/-- The actual residual Gaussian integral, with exactly the same source
and mass normalization as the full corrected prime heat. -/
def normalizedClearedPrimeRemainderHeat (D : ℕ) (S : Finset ℕ) (rho : NontrivialZetaZero)
    (N : ℕ) (B : ℝ) : ℂ :=
  (clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) / (mass B : ℂ) *
    ∫ y : ℝ, (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)

/-- The complete arithmetic heat is exactly the preserved negative pole
source plus the original residual integral. Every source coefficient, sign,
factorial order and Gaussian normalization is retained. -/
theorem normalizedClearedPrimeHeat_eq_source_add_remainder {D : ℕ} (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (N : ℕ) {B : ℝ} (hB : 0 < B) :
    normalizedClearedPrimeHeat D S rho N B =
      -(analyticZetaZeroMultiplicity rho : ℂ) *
        (attenuation N (clearedPrimeSourceDistance rho) B : ℂ) +
      normalizedClearedPrimeRemainderHeat D S rho N B := by
  have heuler : 1 < (zetaWronskianMomentCenter rho).re := by norm_num [zetaWronskianMomentCenter]
  have hp := integrable_clearedPrimeMoment_heat hB (normalizedPrimeTailClearingPolynomial D S rho)
    D S hS N heuler
  have hm := (integrable_poleMoment N (clearedPrimeSourceDistance_pos rho) hB).const_mul
    (analyticZetaZeroMultiplicity rho : ℂ)
  have he (y : ℝ) : (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y) =
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
        clearedPrimeMoment (normalizedPrimeTailClearingPolynomial D S rho) D S N
          (zetaWronskianMomentCenter rho - I * y) +
        (analyticZetaZeroMultiplicity rho : ℂ) * ((Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
          (((clearedPrimeSourceDistance rho : ℂ) - I * y)⁻¹) ^ (N + 1)) := by
    rw [signedTaylorMoment_clearedPrimeRemainder hD S hS rho N (by norm_num [zetaWronskianMomentCenter]),
      shifted_center_sub]
    ring
  have hrem : normalizedClearedPrimeRemainderHeat D S rho N B =
      normalizedClearedPrimeHeat D S rho N B + (analyticZetaZeroMultiplicity rho : ℂ) *
        poleHeat N (clearedPrimeSourceDistance rho) B := by
    unfold normalizedClearedPrimeRemainderHeat
    simp_rw [he]
    rw [integral_add hp hm, integral_const_mul,
      integral_clearedPrimeMoment_heat hB _ D S hS N heuler]
    unfold normalizedClearedPrimeHeat poleHeat
    have hmass : (mass B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mass_pos hB).ne'
    field_simp
  rw [poleHeat_eq_attenuation N (clearedPrimeSourceDistance_pos rho) hB] at hrem
  rw [hrem]
  ring

/-- At every quadratic width, the actual full arithmetic heat has at
least the negative exp(-c) pole contribution, with its complete signed
residual still explicit. This does not bound that residual independently. -/
theorem normalizedClearedPrimeHeat_re_le {D : ℕ} (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r.Prime) (rho : NontrivialZetaZero) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    (normalizedClearedPrimeHeat D S rho N (quadraticWidth c (clearedPrimeSourceDistance rho) N)).re ≤
      -(analyticZetaZeroMultiplicity rho : ℝ) * Real.exp (-c) +
        (normalizedClearedPrimeRemainderHeat D S rho N
          (quadraticWidth c (clearedPrimeSourceDistance rho) N)).re := by
  have hu := clearedPrimeSourceDistance_pos rho
  have hB := quadraticWidth_pos hc hu N
  have hb := (poleHeat_quadraticWidth_bounds hc hu N).1
  rw [poleHeat_eq_attenuation N hu hB, Complex.ofReal_re] at hb
  rw [normalizedClearedPrimeHeat_eq_source_add_remainder hD S hS rho N hB]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.natCast_re,
    Complex.ofReal_re, Complex.neg_im, Complex.natCast_im, Complex.ofReal_im,
    neg_zero, mul_zero, sub_zero]
  have hm : -(analyticZetaZeroMultiplicity rho : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg _)
  exact add_le_add (mul_le_mul_of_nonpos_left hb hm) le_rfl

/-- The actual residual has an analytic representative on the entire
cleared compact disc, agreeing with its original Euler germs. The selected
pole and every nonselected pole have genuinely been removed. This is the
local Cauchy interface for bounding its Gaussian average. -/
theorem exists_clearedPrimeRemainder_analyticRepresentative (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)) ∧
      ∀ s ∈ closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho),
        1 < s.re → R =ᶠ[𝓝 s] clearedPrimeRemainder D S rho := by
  let K := closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hspec := zetaWronskianMomentRadius_spec rho hrho
  have ha : rho.1 ∈ K := by
    simpa [K, mem_closedBall, dist_eq_norm, norm_sub_rev] using hspec.2.1.le
  have hf : MeromorphicOn (primeTailContinuation D S) K := by
    intro s hs
    have hnorm : ‖s - zetaWronskianMomentCenter rho‖ ≤ zetaWronskianMomentRadius rho := by
      simpa [K, mem_closedBall, dist_eq_norm] using hs
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (s - zetaWronskianMomentCenter rho)).trans hnorm)).1
    have hc : (zetaWronskianMomentCenter rho).re = 3 / 2 := by simp [zetaWronskianMomentCenter]
    rw [Complex.sub_re, hc] at hre
    exact meromorphicAt_primeTailContinuation D S (by linarith [hspec.2.2])
  let G := meromorphicPairSimpleRegular (primeTailContinuation D S) (fun _ ↦ 0) K rho.1
  let w := (primeTailClearingPolynomial D S rho).eval rho.1
  have hw : w ≠ 0 := primeTailClearingPolynomial_eval_ne_zero D S rho
  have hG : AnalyticOnNhd ℂ G K := analyticOnNhd_meromorphicPairSimpleRegular hK hf
    (by rw [meromorphicOrderAt_primeTailContinuation D S rho hrho])
  have hGa : G rho.1 = w * (-(analyticZetaZeroMultiplicity rho : ℂ)) := by
    dsimp only [G]
    rw [meromorphicPairSimpleRegular_apply hK hf ha (meromorphicOrderAt_primeTailContinuation D S rho hrho),
      meromorphicTrailingCoeffAt_primeTailContinuation D S rho hrho]
    congr 1
    exact (meromorphicPairClearingPolynomial_eval _ _ hK rho.1 rho.1).symm
  refine ⟨fun z ↦ w⁻¹ * dslope G rho.1 z, ?_, ?_⟩
  · exact fun z hz ↦ analyticAt_const.mul (analyticOnNhd_dslope_of_mem hG ha z hz)
  · intro s hs heuler
    have hraw : AnalyticAt ℂ ((fun z : ℂ ↦ z - rho.1) *
        (meromorphicPairClearingWeight (primeTailContinuation D S) (fun _ ↦ 0) K rho.1 *
          primeTailContinuation D S)) s :=
      (analyticAt_id.sub analyticAt_const).mul
        ((analyticAt_meromorphicPairClearingWeight _ _ _ _ s).mul (analyticAt_primeTailContinuation D S heuler))
    have he := ((hG s hs).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hraw.continuousAt).mp
      (meromorphicPairSimpleRegular_eventuallyEq (g := fun _ ↦ 0) (a := rho.1) hf hs)
    filter_upwards [he, eventually_ne_nhds (euler_ne_zero heuler rho)] with z hz hza
    rw [dslope_of_ne _ hza, slope, hGa]
    change w⁻¹ * ((z - rho.1)⁻¹ * (G z - w * (-(analyticZetaZeroMultiplicity rho : ℂ)))) = _
    rw [hz]
    simp only [Pi.mul_apply, clearedPrimeRemainder, normalizedPrimeTailClearingPolynomial,
      Polynomial.eval_mul, Polynomial.eval_C]
    have hq : (primeTailClearingPolynomial D S rho).eval z =
        meromorphicPairClearingWeight (primeTailContinuation D S) (fun _ ↦ 0) K rho.1 z :=
      meromorphicPairClearingPolynomial_eval _ _ hK rho.1 z
    rw [hq]
    change w⁻¹ * ((z - rho.1)⁻¹ *
      ((z - rho.1) * (meromorphicPairClearingWeight (primeTailContinuation D S) (fun _ ↦ 0) K rho.1 z *
        primeTailContinuation D S z) - w * (-(analyticZetaZeroMultiplicity rho : ℂ)))) =
      w⁻¹ * meromorphicPairClearingWeight (primeTailContinuation D S) (fun _ ↦ 0) K rho.1 z *
        primeTailContinuation D S z + (analyticZetaZeroMultiplicity rho : ℂ) / (z - rho.1)
    field_simp
    ring

/-- A common Cauchy radius strictly between the selected distance and
the full clearing radius, independent of moment order and heat width. -/
def clearedPrimeCentralRadius (rho : NontrivialZetaZero) : ℝ :=
  (clearedPrimeSourceDistance rho + zetaWronskianMomentRadius rho) / 2

/-- The explicit vertical neighborhood on which those Cauchy discs fit
inside the actual full clearing domain. -/
def clearedPrimeCentralWindow (rho : NontrivialZetaZero) : ℝ :=
  (zetaWronskianMomentRadius rho - clearedPrimeSourceDistance rho) / 4

/-- The original right-half-zero geometry gives a positive central
window and a Cauchy radius larger than the selected source distance. -/
theorem clearedPrimeCentralGeometry (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    0 < clearedPrimeCentralWindow rho ∧
      clearedPrimeSourceDistance rho < clearedPrimeCentralRadius rho ∧
      clearedPrimeCentralWindow rho + clearedPrimeCentralRadius rho < zetaWronskianMomentRadius rho := by
  have huR : clearedPrimeSourceDistance rho < zetaWronskianMomentRadius rho := by
    unfold clearedPrimeSourceDistance zetaWronskianMomentRadius
    linarith
  unfold clearedPrimeCentralWindow clearedPrimeCentralRadius
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The actual residual moment has a uniform geometric bound on the
entire central vertical neighborhood. The radius, neighborhood, and
constant are shared by every order and every Gaussian width. -/
theorem exists_clearedPrimeRemainder_central_bound (D : ℕ) (S : Finset ℕ)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (y : ℝ), |y| ≤ clearedPrimeCentralWindow rho →
      ‖(clearedPrimeSourceDistance rho : ℂ) ^ (N + 1) *
        signedTaylorMoment N (clearedPrimeRemainder D S rho) (zetaWronskianMomentCenter rho - I * y)‖ ≤
      C * (clearedPrimeSourceDistance rho / clearedPrimeCentralRadius rho) ^ N := by
  obtain ⟨F, hF, he⟩ := exists_clearedPrimeRemainder_analyticRepresentative D S rho hrho
  have hg := clearedPrimeCentralGeometry rho hrho
  have hu := clearedPrimeSourceDistance_pos rho
  have hr : 0 < clearedPrimeCentralRadius rho := hu.trans hg.2.1
  have hbig : 0 < zetaWronskianMomentRadius rho := lt_trans hr (by linarith [hg.1, hg.2.2])
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho)).image_of_continuousOn
    hF.continuousOn).isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM _ ⟨zetaWronskianMomentCenter rho, mem_closedBall_self hbig.le, rfl⟩)
  refine ⟨(M + 1) * clearedPrimeSourceDistance rho, by positivity, fun N y hy ↦ ?_⟩
  have hshift : ‖(zetaWronskianMomentCenter rho - I * y) - zetaWronskianMomentCenter rho‖ = |y| := by
    simp
  have hsubset : closedBall (zetaWronskianMomentCenter rho - I * y) (clearedPrimeCentralRadius rho) ⊆
      closedBall (zetaWronskianMomentCenter rho) (zetaWronskianMomentRadius rho) := by
    intro z hz
    have hn : ‖z - (zetaWronskianMomentCenter rho - I * y)‖ ≤ clearedPrimeCentralRadius rho := by
      simpa [mem_closedBall, dist_eq_norm] using hz
    have ht := norm_add_le (z - (zetaWronskianMomentCenter rho - I * y))
      ((zetaWronskianMomentCenter rho - I * y) - zetaWronskianMomentCenter rho)
    rw [sub_add_sub_cancel, hshift] at ht
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    linarith [hg.2.2]
  have hcenter := hsubset (mem_closedBall_self hr.le)
  have hd : DiffContOnCl ℂ F (ball (zetaWronskianMomentCenter rho - I * y) (clearedPrimeCentralRadius rho)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact (hF.mono hsubset).differentiableOn
  have hb := norm_signedTaylorMoment_le hr hd (fun z hz ↦
    (hM _ ⟨z, hsubset (sphere_subset_closedBall hz), rfl⟩).trans (by linarith : M ≤ M + 1)) N
  rw [← signedTaylorMoment_congr N (he _ hcenter (by norm_num [zetaWronskianMomentCenter])),
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ clearedPrimeSourceDistance rho ^ (N + 1) * ((M + 1) / clearedPrimeCentralRadius rho ^ N) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [div_pow, pow_succ]; ring

end
end RiemannGaussian.SquarefreeEulerQuadratic
