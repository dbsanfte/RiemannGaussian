/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiGlobalLogDerivative

/-!
# The complete positive Poisson mass beyond the zeta strip

Functional-equation reindexing separates the two channels of the global
reflected xi expansion without losing a factor of two. Every genuine zero
keeps its analytic multiplicity. The full mass is exactly the real xi
logarithmic derivative on the closed right safe half-plane.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Topology

/-- The signed Poisson contribution of one genuine zero, with its full
analytic multiplicity and the original evaluation point. -/
def zetaGlobalPoissonSummand (s : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    (s.re - rho.1.re) / Complex.normSq (s - rho.1)

/-- The known open zeta strip gives the sign of every complete summand
at every evaluation point with real part at least one. -/
theorem zetaGlobalPoissonSummand_nonneg {s : ℂ} (hs : 1 ≤ s.re)
    (rho : NontrivialZetaZero) : 0 ≤ zetaGlobalPoissonSummand s rho := by
  unfold zetaGlobalPoissonSummand
  apply div_nonneg _ (Complex.normSq_nonneg _)
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith [NontrivialZetaZero.re_lt_one rho])

private theorem reflected_summand (s : ℂ) (rho : NontrivialZetaZero) :
    (zetaLogDerivDifferenceSummand s (1 - s) rho).re =
      zetaGlobalPoissonSummand s rho +
        zetaGlobalPoissonSummand s (NontrivialZetaZero.functionalPartner rho) := by
  rw [zetaLogDerivDifferenceSummand_reflection_re]
  unfold zetaGlobalPoissonSummand
  rw [analyticZetaZeroMultiplicity_functionalPartner,
    NontrivialZetaZero.functionalPartner_coe]
  have he : Complex.normSq (s - (1 - rho.1)) = Complex.normSq (1 - s - rho.1) := by
    rw [show s - (1 - rho.1) = -(1 - s - rho.1) by ring, Complex.normSq_neg]
  rw [he]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Each individual Poisson channel is absolutely summable. This is
deduced from the existing paired expansion before either sum is split. -/
theorem summable_zetaGlobalPoissonSummand {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (zetaGlobalPoissonSummand s) := by
  have h := Complex.reCLM.summable (summable_zetaLogDerivDifferenceSummand s (1 - s))
  apply h.of_nonneg_of_le (zetaGlobalPoissonSummand_nonneg hs)
  intro rho
  change zetaGlobalPoissonSummand s rho ≤ (zetaLogDerivDifferenceSummand s (1 - s) rho).re
  rw [reflected_summand]
  exact le_add_of_nonneg_right (zetaGlobalPoissonSummand_nonneg hs _)

/-- The full positive zero mass is exactly `Re(xi'/xi)`, with every
multiplicity counted once. No local-radius remainder remains. -/
theorem tsum_zetaGlobalPoissonSummand {s : ℂ} (hs : 1 ≤ s.re) :
    (∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho) =
      (logDeriv riemannXi s).re := by
  have hxi : riemannXi s ≠ 0 := by
    intro hz
    let rho : NontrivialZetaZero := ⟨s, (riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp hz⟩
    exact not_lt_of_ge hs (NontrivialZetaZero.re_lt_one rho)
  have h := Complex.hasSum_re (hasSum_zetaLogDeriv_reflection hxi)
  simp only [reflected_summand] at h
  have hsum := summable_zetaGlobalPoissonSummand hs
  have href := (NontrivialZetaZero.functionalPartnerEquiv.summable_iff).mpr hsum
  change Summable (fun rho => zetaGlobalPoissonSummand s
    (NontrivialZetaZero.functionalPartner rho)) at href
  have he : (∑' rho : NontrivialZetaZero,
      zetaGlobalPoissonSummand s (NontrivialZetaZero.functionalPartner rho)) =
        ∑' rho : NontrivialZetaZero, zetaGlobalPoissonSummand s rho := by
    simpa only [NontrivialZetaZero.functionalPartnerEquiv_apply] using
      NontrivialZetaZero.functionalPartnerEquiv.tsum_eq (zetaGlobalPoissonSummand s)
  have ht := h.tsum_eq
  rw [hsum.tsum_add href, he] at ht
  norm_num [Complex.mul_re] at ht
  linarith

/-- Any finite selected zero window consumes its full positive share of
the same global xi mass. Its omitted complement has a proved sign. -/
theorem sum_zetaGlobalPoissonSummand_le {s : ℂ} (hs : 1 ≤ s.re)
    (S : Finset NontrivialZetaZero) :
    (∑ rho ∈ S, zetaGlobalPoissonSummand s rho) ≤ (logDeriv riemannXi s).re := by
  rw [← tsum_zetaGlobalPoissonSummand hs]
  exact (summable_zetaGlobalPoissonSummand hs).sum_le_tsum S
    (fun rho _ => zetaGlobalPoissonSummand_nonneg hs rho)

/-- At an actual zero's ordinate, the full selected contribution is its
multiplicity divided by the horizontal distance from the evaluation line. -/
theorem zetaGlobalPoissonSummand_at_ordinate (rho : NontrivialZetaZero)
    {σ : ℝ} (hσ : 1 ≤ σ) :
    zetaGlobalPoissonSummand ((σ : ℂ) + I * rho.1.im) rho =
      (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) := by
  have hdist : 0 < σ - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  unfold zetaGlobalPoissonSummand
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, add_zero,
    zero_add, sub_self]
  field_simp

end
end RiemannGaussian
