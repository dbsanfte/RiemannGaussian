/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactSparsity
import RiemannGaussian.ZetaSignedInfiniteHeight

/-!
# Arbitrary phase families retain the prime work in the zero inequality

For every summable nonnegative coefficient sequence, the full coupled zeta
logarithmic derivative is exactly the prime-power series evaluated against
its cosine kernel. Both infinite sums and their interchange are justified.

The local zero inequality retains this arithmetic term, every local zero
sum, the exact pole at one, and the actual logarithmic cost of each height.
No prescribed support, optimizer, shift ratio, or linear frequency cost is
used. Nonnegative kernels allow any finite set of prime-power contributions
to be retained as an independent improvement to the zero inequality.

This is a transport of actual arithmetic information, not a proof of the
open global signed inequality for RH.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- A countable cosine family with arbitrary real frequencies. Finite
families are included by taking all remaining coefficients to be zero. -/
def zetaPhaseKernel (a ω : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, a n * Real.cos (ω n * t)

/-- The previously optimized integer-frequency kernel is one instance
of the arbitrary real-frequency kernel. -/
theorem zetaPhaseKernel_natCast (a : ℕ → ℝ) (t : ℝ) :
    zetaPhaseKernel a (fun n ↦ (n : ℝ)) t = phaseContactKernel a t := rfl

variable {ω : ℕ → ℝ}

/-- Absolute summability of the coefficients suffices for every angle;
there is no prescribed frequency cost. -/
theorem summable_zetaPhaseKernel {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (t : ℝ) :
    Summable (fun n : ℕ ↦ a n * Real.cos (ω n * t)) := by
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_of_le_one_right (ha n) (Real.abs_cos_le_one _)

/-- The literal von Mangoldt amplitude, including every prime power. -/
def zetaPhasePrimeWeight (σ : ℝ) (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * Real.exp (-σ * Real.log m)

/-- Every prime-power amplitude is nonnegative. -/
theorem zetaPhasePrimeWeight_nonneg (σ : ℝ) (m : ℕ) :
    0 ≤ zetaPhasePrimeWeight σ m := by
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

private theorem zetaPhase_prime_hasSum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasSum (fun m : ℕ ↦ zetaPhasePrimeWeight σ m * Real.cos (t * Real.log m))
      (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re := by
  have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  rw [neg_logDeriv_riemannZeta_eq_vonMangoldt (by simpa using hσ), Complex.re_tsum hs]
  have hsre : Summable (fun m ↦ (LSeries.term
      (fun k ↦ (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + I * t) m).re) :=
    Complex.reCLM.summable hs
  simpa only [vonMangoldt_LSeries_term_re, zetaPhasePrimeWeight] using hsre.hasSum

/-- The arithmetic amplitudes have their genuine convergent sum on
the half-plane of absolute convergence. -/
theorem hasSum_zetaPhasePrimeWeight {σ : ℝ} (hσ : 1 < σ) :
    HasSum (zetaPhasePrimeWeight σ) (-logDeriv riemannZeta (σ : ℂ)).re := by
  simpa only [Complex.ofReal_zero, mul_zero, add_zero, zero_mul, Real.cos_zero, mul_one]
    using zetaPhase_prime_hasSum hσ 0

/-- The coupled logarithmic derivatives converge for any summable
nonnegative coefficient family, including infinite support. -/
theorem summable_zetaPhase_logDeriv {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    Summable (fun n : ℕ ↦ a n *
      (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  apply (hs.mul_right (-logDeriv riemannZeta (σ : ℂ)).re).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs (a n), abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left
    (norm_neg_logDeriv_riemannZeta_re_le_real_axis hσ _) (ha n)

/-- The signed zeta combination is the actual prime-power work of the
entire phase kernel. Joint absolute convergence is proved before exchanging
the arithmetic and frequency sums. -/
theorem hasSum_zetaPhase_arithmetic {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun m : ℕ ↦ zetaPhasePrimeWeight σ m *
        zetaPhaseKernel a ω (y * Real.log m))
      (∑' n : ℕ, a n *
        (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  let f (m n : ℕ) := a n * zetaPhasePrimeWeight σ m *
    Real.cos ((ω n * y) * Real.log m)
  have hmajor := (hasSum_zetaPhasePrimeWeight hσ).summable.mul_of_nonneg hs
    (zetaPhasePrimeWeight_nonneg σ) ha
  have hdouble : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    dsimp [f, Function.uncurry]
    rw [abs_mul, abs_of_nonneg (mul_nonneg (ha p.2) (zetaPhasePrimeWeight_nonneg σ p.1))]
    calc
      _ ≤ a p.2 * zetaPhasePrimeWeight σ p.1 :=
        mul_le_of_le_one_right (mul_nonneg (ha p.2)
          (zetaPhasePrimeWeight_nonneg σ p.1)) (Real.abs_cos_le_one _)
      _ = _ := mul_comm _ _
  have he : (∑' m, ∑' n, f m n) =
      ∑' n : ℕ, a n *
        (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
    rw [← hdouble.tsum_comm]
    apply tsum_congr
    intro n
    rw [← (zetaPhase_prime_hasSum hσ (ω n * y)).tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp [f]
    ring
  rw [← he]
  apply hdouble.prod.hasSum.congr_fun
  intro m
  unfold zetaPhaseKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [f]
  simp only [mul_assoc]
  ring

/-- A nonnegative phase kernel supplies a signed inequality for zeta
for any finite or infinite summable nonnegative coefficient family. -/
theorem zetaPhase_logDeriv_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    0 ≤ ∑' n : ℕ, a n *
      (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
  rw [← (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).tsum_eq]
  exact tsum_nonneg fun m ↦ mul_nonneg (zetaPhasePrimeWeight_nonneg σ m) (hp _)

private theorem zetaPhase_pole_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    x / (x ^ 2 + t ^ 2) ≤ 1 / x := by
  calc
    x / (x ^ 2 + t ^ 2) ≤ x / x ^ 2 :=
      div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx) (by nlinarith [sq_nonneg t])
    _ = 1 / x := by field_simp

/-- The exact pole contributions converge without replacing nonzero
heights by a common bound in the theorem statement. -/
theorem summable_zetaPhase_exactPole {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Summable (fun n : ℕ ↦ a n * (x / (x ^ 2 + (ω n * y) ^ 2))) := by
  apply (hs.mul_right (1 / x)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ha n) (div_nonneg hx.le (add_nonneg (sq_nonneg _) (sq_nonneg _))))]
  exact mul_le_mul_of_nonneg_left (zetaPhase_pole_le hx _) (ha n)

/-- Summability of the actual height costs suffices to retain all
the local zero sums, with no prescribed linear frequency budget. -/
theorem summable_zetaPhase_localZeros {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) (y : ℝ)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight (ω n * y))) :
    Summable (fun n : ℕ ↦ a n *
      (localZetaPoleSum (ω n * y) ((x - 1 / 2 : ℝ) : ℂ)).re) := by
  let D := (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re
  have hbound (n : ℕ) :
      (localZetaPoleSum (ω n * y) ((x - 1 / 2 : ℝ) : ℂ)).re ≤
        1 / x + D + 448 * localZetaLogHeight (ω n * y) := by
    have h := neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum
      (ω n * y) hx hxsmall
    have hpole := zetaPhase_pole_le hx (ω n * y)
    have hn := norm_neg_logDeriv_riemannZeta_re_le_real_axis
      (by linarith : 1 < 1 + x) (ω n * y)
    have hneg := neg_le_abs (-logDeriv riemannZeta
      (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re
    rw [Real.norm_eq_abs] at hn
    dsimp only [D]
    linarith
  apply ((hs.mul_right (1 / x + D)).add (hL.mul_left 448)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ha n) (localZetaPoleSum_re_nonneg _ hx))]
  have h := mul_le_mul_of_nonneg_left (hbound n) (ha n)
  nlinarith only [h]

/-- The full arithmetic work and the full local zero mass share one
upper budget. Every frequency, exact pole contribution, and actual height
cost is retained. The kernel need not be nonnegative for this signed identity
to be used in the estimate. -/
theorem zetaPhase_primeWork_add_localZeros_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {x : ℝ} (hx : 0 < x)
    (hxsmall : x ≤ 1 / 4) (y : ℝ)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight (ω n * y))) :
    (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * (localZetaPoleSum (ω n * y) ((x - 1 / 2 : ℝ) : ℂ)).re) ≤
        (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * y) ^ 2))) +
          448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * y) := by
  rw [(hasSum_zetaPhase_arithmetic (ω := ω) ha hs (by linarith : 1 < 1 + x) y).tsum_eq]
  have hD := summable_zetaPhase_logDeriv (ω := ω) ha hs (by linarith : 1 < 1 + x) y
  have hZ := summable_zetaPhase_localZeros (ω := ω) ha hs hx hxsmall y hL
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs hx y
  rw [← hD.tsum_add hZ, ← tsum_mul_left, ← hP.tsum_add (hL.mul_left 448)]
  apply (hD.add hZ).tsum_le_tsum _ (hP.add (hL.mul_left 448))
  intro n
  have h := mul_le_mul_of_nonneg_left
    (neg_logDeriv_riemannZeta_re_le_exactPole_sub_poleSum (ω n * y) hx hxsmall) (ha n)
  nlinarith only [h]

/-- Any chosen finite arithmetic window gives an unconditional lower
bound for the complete prime work when the full phase kernel is nonnegative.
No omitted prime term is assigned an unproved sign. -/
theorem zetaPhase_finite_primeWork_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) (S : Finset ℕ) :
    (∑ m ∈ S, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) ≤
      ∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m) := by
  exact Summable.sum_le_tsum S
    (fun m _ ↦ mul_nonneg (zetaPhasePrimeWeight_nonneg σ m) (hp _))
    (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).summable

/-- A literal zero's full multiplicity and any retained finite arithmetic
window constrain each other in the same arbitrary-family inequality. -/
theorem zetaPhase_multiplicity_add_primeWork_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 1)
    (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight (ω n * rho.1.im)))
    (S : Finset ℕ) :
    a r * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re) +
      (∑ m ∈ S, zetaPhasePrimeWeight (1 + x) m *
        zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * rho.1.im) := by
  have h := zetaPhase_primeWork_add_localZeros_le (ω := ω) ha hs hx hxsmall rho.1.im hL
  have hprime := zetaPhase_finite_primeWork_le (ω := ω) ha hs hp
    (by linarith : 1 < 1 + x) rho.1.im S
  have hz := (summable_zetaPhase_localZeros (ω := ω) ha hs hx hxsmall rho.1.im hL).le_tsum r
    (fun n _ ↦ mul_nonneg (ha n) (localZetaPoleSum_re_nonneg _ hx))
  have hsingle := mul_le_mul_of_nonneg_left
    (multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx) (ha r)
  simp only [hr, one_mul] at hz
  rw [mul_div_assoc]
  linarith

end

end RiemannGaussian
