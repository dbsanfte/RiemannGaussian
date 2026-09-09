/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHalfStripSource
import RiemannGaussian.ZetaPhaseZeroBudget

/-!
# Complete phase constraints for every zero right of the critical line

The adaptive canonical source is transported to arbitrary summable real
frequency families. The arithmetic prime sum remains signed and complete.
For integer frequencies, its true mass and logarithmic moment give a
uniform source-deficit interface throughout the right half of the strip.
The independent arithmetic estimate needed to beat this allowance is open.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The exact canonical response of the selected zero with its full
multiplicity. Its regular correction remains coupled to the singular term. -/
def halfStripCanonicalSource (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (x : ℝ) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    (zetaCanonicalZeroResponse
      (adaptiveZetaCanonicalRadius (zetaRightHalfDiscParameter rho hrho) rho.1.im)
      ((rho.1.re - 3 / 2 : ℝ) : ℂ) ((x - 1 / 2 : ℝ) : ℂ)).re

/-- A positive lower bound on the exact source exposes the critical-line
distance; the exact source remains available for stronger applications. -/
theorem halfStripCanonicalSource_distance_lower (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (analyticZetaZeroMultiplicity rho : ℝ) * (rho.1.re - 1 / 2) /
      (3 * (x + 1 - rho.1.re)) ≤ halfStripCanonicalSource rho hrho x := by
  have h := mul_le_mul_of_nonneg_left (halfStripCanonicalSource_lower rho hrho hx hx1)
    (show (0 : ℝ) ≤ analyticZetaZeroMultiplicity rho by positivity)
  rwa [← mul_div_assoc] at h

/-- Every selected off-critical zero has a strictly positive canonical
source; its full analytic multiplicity is included. -/
theorem halfStripCanonicalSource_pos (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < halfStripCanonicalSource rho hrho x := by
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  apply lt_of_lt_of_le _ (halfStripCanonicalSource_distance_lower rho hrho hx hx1)
  exact div_pos (mul_pos (by linarith) (sub_pos.mpr hrho))
    (by linarith [NontrivialZetaZero.re_lt_one rho])

/-- An arbitrary real-frequency family retains the full arithmetic work
beside the multiplicity source of any actual zero right of the critical line. -/
theorem zetaPhase_halfStripCanonicalSource_add_primeWork_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (k : ℕ) (hk : ω k = 1)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : Summable (fun n ↦ a n * localZetaLogHeight (ω n * rho.1.im))) :
    a k * halfStripCanonicalSource rho hrho x +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * rho.1.im) := by
  let T := halfStripCanonicalSource rho hrho x
  have hD := summable_zetaPhase_logDeriv (ω := ω) ha hs (by linarith : 1 < 1 + x) rho.1.im
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs hx rho.1.im
  have hT := hasSum_ite_eq k (a k * T)
  have hpoint (n : ℕ) :
      a n * (-logDeriv riemannZeta (((1 + x : ℝ) : ℂ) + I * ((ω n * rho.1.im : ℝ) : ℂ))).re +
          (if n = k then a k * T else 0) ≤
        a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2)) +
          448 * (a n * localZetaLogHeight (ω n * rho.1.im)) := by
    by_cases hn : n = k
    · subst n
      simp only [ite_true, hk, one_mul]
      have h := mul_le_mul_of_nonneg_left
        (neg_logDeriv_add_halfStripCanonicalSource_le rho hrho hx hx1) (ha k)
      dsimp only [T, halfStripCanonicalSource]
      linarith
    · simp only [if_neg hn, add_zero]
      have h := mul_le_mul_of_nonneg_left
        (neg_logDeriv_re_le_adaptive_exactPole (ω n * rho.1.im) hx hx1) (ha n)
      linarith
  have h := (hD.add hT.summable).tsum_le_tsum hpoint (hP.add (hL.mul_left 448))
  rw [hD.tsum_add hT.summable, hT.tsum_eq,
    hP.tsum_add (hL.mul_left 448), tsum_mul_left] at h
  rw [← (hasSum_zetaPhase_arithmetic (ω := ω) ha hs (by linarith : 1 < 1 + x) rho.1.im).tsum_eq] at h
  dsimp only [T] at h
  simpa only [add_comm] using h

/-- The simpler critical-distance source is a downstream consequence
of the full canonical phase inequality, for every actual right-half zero. -/
theorem zetaPhase_halfStripSource_add_primeWork_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (k : ℕ) (hk : ω k = 1)
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : Summable (fun n ↦ a n * localZetaLogHeight (ω n * rho.1.im))) :
    a k * (analyticZetaZeroMultiplicity rho : ℝ) * (rho.1.re - 1 / 2) /
        (3 * (x + 1 - rho.1.re)) +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * rho.1.im) := by
  have h := zetaPhase_halfStripCanonicalSource_add_primeWork_le ha hs k hk rho hrho hx hx1 hL
  have hl := mul_le_mul_of_nonneg_left (halfStripCanonicalSource_distance_lower rho hrho hx hx1) (ha k)
  have hls : a k * (analyticZetaZeroMultiplicity rho : ℝ) * (rho.1.re - 1 / 2) /
      (3 * (x + 1 - rho.1.re)) ≤ a k * halfStripCanonicalSource rho hrho x := by
    calc
      _ = a k * ((analyticZetaZeroMultiplicity rho : ℝ) * (rho.1.re - 1 / 2) /
        (3 * (x + 1 - rho.1.re))) := by ring
      _ ≤ _ := hl
  exact (add_le_add hls le_rfl).trans h

/-- Every finite arithmetic window at such a zero is constrained by the
same complete source and actual analytic costs when the kernel is nonnegative. -/
theorem zetaPhase_halfStripCanonicalSource_add_finite_primeWork_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (k : ℕ) (hk : ω k = 1) (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : Summable (fun n ↦ a n * localZetaLogHeight (ω n * rho.1.im))) (S : Finset ℕ) :
    a k * halfStripCanonicalSource rho hrho x +
      (∑ m ∈ S, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * rho.1.im) := by
  have h := zetaPhase_halfStripCanonicalSource_add_primeWork_le ha hs k hk rho hrho hx hx1 hL
  have hf := zetaPhase_finite_primeWork_le ha hs hp (by linarith : 1 < 1 + x) rho.1.im S
  linarith

/-- The true mass/logarithmic budget now applies to every actual zero
right of the critical line. The exact canonical source, complete signed
arithmetic sum, and multiplicity remain available before any lower estimate. -/
theorem phase_halfStrip_source_add_primeWork_le_split_budget {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ ↦ a n * Real.log n))
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ * (1 - rho.1.re) ≤ 1) :
    (1 - rho.1.re) * a 1 * halfStripCanonicalSource rho hrho (κ * (1 - rho.1.re)) - a 0 / κ +
      (1 - rho.1.re) * (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) *
        (a 0 * localZetaLogHeight 0 + phaseOscillatoryMass a * localZetaLogHeight rho.1.im +
          phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hL := summable_phase_height_of_logFrequency ha hs hlog rho.1.im
  have h := zetaPhase_halfStripCanonicalSource_add_primeWork_le (ω := fun n ↦ (n : ℝ)) ha hs 1 (by norm_num)
    rho hrho hx hκsmall hL
  simp only [zetaPhaseKernel_natCast] at h
  have hp := phase_exactPole_le_split_budget ha hs hx (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hheight := phase_height_le_split_budget ha hs hlog rho.1.im hL
  have hsum : a 1 * halfStripCanonicalSource rho hrho (κ * d) +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * d) m * phaseContactKernel a (rho.1.im * Real.log m)) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        448 * (a 0 * localZetaLogHeight 0 + phaseOscillatoryMass a * localZetaLogHeight rho.1.im +
          phaseLogFrequencyMass a) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  have he0 : d * (a 0 / (κ * d)) = a 0 / κ := by field_simp
  simp only [mul_add] at hm
  rw [he0] at hm
  dsimp only [d] at hm ⊢
  linear_combination hm

end

end RiemannGaussian
