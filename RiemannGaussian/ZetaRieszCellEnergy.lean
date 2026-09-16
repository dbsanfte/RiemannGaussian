/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCellOrders

/-!
# Keep the signed covariance of the two prime moments

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCellEnergy
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeCells
open ZetaRieszCellBoundary
open ZetaRieszCellOrders

/-- The energy of two real-coefficient complex responses retains the
complete signed covariance term. -/
theorem two_moment_energy (a b : ℝ) (z w : ℂ) :
    ‖(a : ℂ) * z + (b : ℂ) * w‖ ^ 2 =
      a ^ 2 * ‖z‖ ^ 2 + b ^ 2 * ‖w‖ ^ 2 +
        2 * a * b * ((starRingEnd ℂ z) * w).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The original cell's full complex energy keeps the correlation
between the two canonical prime moments, including its cofactor sign. -/
theorem prime_cell_energy (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n q₀ : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n) :
    let x := Real.log q₀
    let F := targetProfile L n x
    let s := cellSlope L n x
    let M₀ := primePacketMoment L x P N t (primeCell Q L n q₀) eta n 0
    let M₁ := primePacketMoment L x P N t (primeCell Q L n q₀) eta n 1
    ‖∑ q ∈ primeCell Q L n q₀, eta q * bandWeight L P N t (q * n)‖ ^ 2 =
      F ^ 2 * ‖M₀‖ ^ 2 + s ^ 2 * ‖M₁‖ ^ 2 +
        2 * F * s * ((starRingEnd ℂ M₀) * M₁).re := by
  dsimp only
  rw [prime_cell_exact_moments L P N t Q eta n q₀ hQ]
  exact two_moment_energy _ _ _ _

/-- The exact covariance is a complete prime-pair correlation weighted
by the first prime-logarithm displacement. No diagonal-only relaxation occurs. -/
theorem first_moment_covariance (Q : Finset ℕ) (g : ℕ → ℂ) (h : ℕ → ℝ) :
    ((starRingEnd ℂ (∑ p ∈ Q, g p)) * ∑ q ∈ Q, (h q : ℂ) * g q).re =
      ∑ p ∈ Q, ∑ q ∈ Q, h q * ((starRingEnd ℂ (g p)) * g q).re := by
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have he : starRingEnd ℂ (g p) * ((h q : ℂ) * g q) =
      (h q : ℂ) * (starRingEnd ℂ (g p) * g q) := by ring
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Real prime-pair correlations are symmetric, despite retaining the
full complex phases of both original factors. -/
theorem real_correlation_symm (z w : ℂ) :
    ((starRingEnd ℂ z) * w).re = ((starRingEnd ℂ w) * z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The covariance retains the midpoint logarithm of every prime pair.
This exposes the multiplicative location and phase difference together. -/
theorem covariance_eq_midpoint (Q : Finset ℕ) (g : ℕ → ℂ) (h : ℕ → ℝ) :
    ((starRingEnd ℂ (∑ p ∈ Q, g p)) * ∑ q ∈ Q, (h q : ℂ) * g q).re =
      ∑ p ∈ Q, ∑ q ∈ Q, ((h p + h q) / 2) *
        ((starRingEnd ℂ (g p)) * g q).re := by
  rw [first_moment_covariance]
  have hs : (∑ p ∈ Q, ∑ q ∈ Q, h p * ((starRingEnd ℂ (g p)) * g q).re) =
      ∑ p ∈ Q, ∑ q ∈ Q, h q * ((starRingEnd ℂ (g p)) * g q).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [real_correlation_symm]
  have ht (p q : ℕ) : ((h p + h q) / 2) * ((starRingEnd ℂ (g p)) * g q).re =
      (h p * ((starRingEnd ℂ (g p)) * g q).re +
        h q * ((starRingEnd ℂ (g p)) * g q).re) / 2 := by ring
  simp_rw [ht]
  simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hs]
  ring

end
end RiemannGaussian.ZetaRieszCellEnergy
