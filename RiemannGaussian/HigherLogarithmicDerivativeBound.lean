/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.HigherDerivativeTest
import RiemannGaussian.LogarithmicDerivativeFamily

/-!
# Every-order bounds for the actual logarithmic phase

At derivative order `k+2`, the positive orientation has lower scale
`t*(k+1)!/(2X)^(k+2)` and dyadic ratio `2^(k+2)`. All derivative hypotheses
are discharged on the original positive interval. Exact phase conjugation
then returns to the original phase `-t*log(x)` with its finite norm unchanged.
The bound holds for every cutoff rule and every prefix below a common cap.
-/

namespace RiemannGaussian.HigherLogarithmicDerivativeBound
noncomputable section
open PhaseIncrementInverse LogarithmicShiftPhase LogarithmicDerivativeFamily
open DerivativeRecursionBudget

/-- The genuine logarithmic phase satisfies the recursive estimate at
every derivative order, with all positive-domain and calculus conditions
discharged and no resonance-avoidance or small-curvature premise. -/
theorem bound (κ : Cutoffs) (k L : ℕ) {t X a : ℝ} (ht : 0 < t) (hX : 0 < X)
    (ha : X ≤ a) (N : ℕ) (hNL : N ≤ L) (hb : a + N ≤ 2 * X) :
    ‖∑ n ∈ Finset.range N, rotation (phase t (a + n))‖ ≤
      budget κ k L (lowerScale t X k) (ratio k) := by
  have hdom {x : ℝ} (hx : x ∈ Set.Icc a (a + N)) :
      0 < x ∧ X ≤ x ∧ x ≤ 2 * X :=
    ⟨hX.trans_le (ha.trans hx.1), ha.trans hx.1, hx.2.trans hb⟩
  have hd : ∀ r < k + 2, ∀ x ∈ Set.Icc a (a + N),
      HasDerivAt (oriented t (k + 2) r) (oriented t (k + 2) (r + 1) x) x :=
    fun r _ _ hx ↦ hasDerivAt_oriented t (k + 2) r (hdom hx).1
  have hr : ∀ x ∈ Set.Icc a (a + N),
      lowerScale t X k ≤ oriented t (k + 2) (k + 2) x ∧
        oriented t (k + 2) (k + 2) x ≤ ratio k * lowerScale t X k :=
    fun _ hx ↦ dyadic_bounds ht.le hX k (hdom hx).2.1 (hdom hx).2.2
  have h := HigherDerivativeTest.bound κ k L (oriented t (k + 2)) a N
    (lowerScale_pos ht hX k) (ratio_pos k).le hNL hd hr
  change ‖∑ n ∈ Finset.range N, rotation ((-1 : ℝ) ^ (k + 2) * phase t (a + n))‖ ≤ _ at h
  rw [PhaseConjugation.norm_sum_neg_one_pow] at h
  exact h

end
end RiemannGaussian.HigherLogarithmicDerivativeBound
