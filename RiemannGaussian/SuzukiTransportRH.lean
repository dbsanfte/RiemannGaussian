/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiPositivityRH
import RiemannGaussian.SuzukiTransportCellCost

/-!
# The exact Suzuki transport criteria imply RH

The literal canonical gaps, endpoint entropy inequality, and signed prime-work
recurrence now connect to Mathlib's `RiemannHypothesis` through the complete
positive-Laplace argument in `SuzukiPositivityRH`.

The finite-head/infinite-tail interface retains the original initial gap,
signed prime work and every nonlinear cell cost. The common cost tail is the
actual summable tail proved in `SuzukiTransportCellCost`; no arbitrary error
function or additional analytic hypothesis is introduced.

These are conditional criteria. Their arithmetic inequalities are not proved
here. Conversely, every hypothetical zero right of the critical line would
force a strict failure of the displayed inequality at some finite prefix.
-/

namespace RiemannGaussian
noncomputable section
open scoped BigOperators

/-- All undisposed canonical gaps nonnegative implies Mathlib's RH. The
initial synthetic cutoff is already discharged by the existing barrier proof. -/
theorem riemannHypothesis_of_suzukiFirstTailCanonicalGap_nonnegative
    (hgap : ∀ count : ℕ, 1 ≤ count → 0 ≤ suzukiFirstTailCanonicalGap count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_psi_nonnegative_tail
  apply riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_transportGap.mpr
  intro cutoff hcutoff
  have h := hgap (cutoff - 1) (by omega)
  simpa only [suzukiFirstTailCanonicalGap, Nat.sub_add_cancel (by omega : 1 ≤ cutoff)] using h

/-- The exact endpoint-entropy inequality has a complete checked path to RH,
with its genuine finite prime sums, canonical centers and smooth correction. -/
theorem riemannHypothesis_of_suzukiFirstTailEntropy_bound
    (hentropy : ∀ count : ℕ, 1 ≤ count →
      4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count) (((count + 2 : ℕ) : ℝ))) ≤
        suzukiChebyshevEndpointCenteredError (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count) (((count + 2 : ℕ) : ℝ)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiFirstTailCanonicalGap_nonnegative
  intro count hcount
  exact (suzukiFirstTailResetTransportGap_succ_nonnegative_iff_entropy_le count).mpr
    (hentropy count hcount)

/-- If cumulative signed prime work plus the actual initial gap pays the
actual nonlinear costs at every prefix, the complete analytic chain proves RH. -/
theorem riemannHypothesis_of_suzukiFirstTail_signed_work_bound
    (hwork : ∀ count : ℕ, 1 ≤ count →
      (∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost n) ≤
        suzukiFirstTailCanonicalGap 0 +
          ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiFirstTailCanonicalGap_nonnegative
  intro count hcount
  have heq := suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost 0 count
  simp only [Nat.zero_add] at heq
  rw [heq]
  exact sub_nonneg.mpr (hwork count hcount)

/-- A finite verified head plus a uniform signed-work margin larger than the
proved common cost tail is sufficient; no band-length-dependent loss is added. -/
theorem riemannHypothesis_of_suzukiFirstTail_head_and_tail_work_bound
    (start : ℕ)
    (hhead : ∀ count : ℕ, 1 ≤ count → count < start →
      0 ≤ suzukiFirstTailCanonicalGap count)
    (htail : ∀ count : ℕ,
      (∑' n : ℕ, suzukiFirstTailTransportCellCost (start + n)) ≤
        suzukiFirstTailCanonicalGap start +
          ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiFirstTailCanonicalGap_nonnegative
  intro count hcount
  by_cases hc : count < start
  · exact hhead count hcount hc
  · have hstart : start ≤ count := le_of_not_gt hc
    have heq := suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost start (count - start)
    rw [Nat.add_sub_of_le hstart] at heq
    rw [heq]
    exact sub_nonneg.mpr
      ((suzukiFirstTailTransportCellCost_block_le_tail start (count - start)).trans
        (htail (count - start)))

/-- A zero right of the critical line would force an actual finite signed-work
failure, with all costs and the initial gap retained. -/
theorem exists_suzukiFirstTail_signed_work_failure_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ count : ℕ, 1 ≤ count ∧
      suzukiFirstTailCanonicalGap 0 +
          (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n) <
        ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost n := by
  by_contra hnot
  push Not at hnot
  have hRH := riemannHypothesis_of_suzukiFirstTail_signed_work_bound hnot
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

end
end RiemannGaussian
