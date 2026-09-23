/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairBoundary

/-!
# Finite least-prime renewal with the original pair weights retained

Extracting the least cofactor prime gives a terminating difference tree
for the truncated Riesz response. The actual pair form admits the exact
first renewal step with all masks, allocation weights, phases and incidence
denominators unchanged. No estimate for the renewal remainder is assumed.
-/

namespace RiemannGaussian.ZetaRieszTypeII
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation

/-- The least-prime child is squarefree, coprime to the extracted prime
and strictly smaller, so repeated extraction is a genuine finite process. -/
theorem minFac_child {a : ℕ} (ha : Squarefree a) (ha1 : a ≠ 1) :
    a.minFac.Prime ∧ Squarefree (a / a.minFac) ∧
      ¬a.minFac ∣ a / a.minFac ∧ a / a.minFac < a := by
  have hp := Nat.minFac_prime ha1
  have he : a.minFac * (a / a.minFac) = a := Nat.mul_div_cancel' (Nat.minFac_dvd a)
  have hs : Squarefree (a.minFac * (a / a.minFac)) := by rw [he]; exact ha
  have hsplit := Nat.squarefree_mul_iff.mp hs
  exact ⟨hp, hsplit.2.2, hp.coprime_iff_not_dvd.mp hsplit.1,
    Nat.div_lt_self (Nat.pos_of_ne_zero ha.ne_zero) hp.one_lt⟩

/-- The exact least-prime recurrence retains both shifted cutoffs. -/
theorem riesz_minFac (z : ℝ) {a : ℕ} (ha : Squarefree a) (ha1 : a ≠ 1) :
    VaughanLogAverage.riesz z a = VaughanLogAverage.riesz z (a / a.minFac) -
      VaughanLogAverage.riesz (z - Real.log a.minFac) (a / a.minFac) := by
  obtain ⟨hp, _, hcop, _⟩ := minFac_child ha ha1
  have h := ZetaSquarefreeRieszWindows.riesz_prime_mul z hp hcop
  rwa [Nat.mul_div_cancel' (Nat.minFac_dvd a)] at h

/-- In the innermost boundary layer the subtracting branch is exactly
zero and the unshifted child still has the entire hinge. Thus iteration
alone creates no within-label cancellation in this layer, at any prime count. -/
theorem inner_layer_renewal {a : ℕ} (ha : Squarefree a) (ha1 : a ≠ 1)
    {z : ℝ} (hz : 0 ≤ z) (hmin : z ≤ Real.log a.minFac) :
    VaughanLogAverage.riesz (z - Real.log a.minFac) (a / a.minFac) = 0 ∧
      VaughanLogAverage.riesz z (a / a.minFac) = z := by
  have hzero := ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hmin)
    (a / a.minFac)
  refine ⟨hzero, ?_⟩
  have h := riesz_minFac z ha ha1
  rw [riesz_eq_cutoff_below_minFac ha.ne_zero hz hmin, hzero, sub_zero] at h
  exact h.symm

/-- A finite renewal tree whose branches keep their distinct Riesz
cutoffs. Its base case includes the unit hinge exactly. -/
def renewalHinge (a : ℕ) (z : ℝ) : ℝ :=
  if a = 0 then 0 else if a = 1 then max 0 z else
    renewalHinge (a / a.minFac) z -
      renewalHinge (a / a.minFac) (z - Real.log a.minFac)
termination_by a
decreasing_by
  all_goals exact Nat.div_lt_self (by omega) (Nat.minFac_prime (by assumption)).one_lt

/-- Iterating least-prime deletion evaluates precisely the original
finite divisor response, rather than a completed Euler product. -/
theorem renewalHinge_eq_riesz {a : ℕ} (ha : Squarefree a) (z : ℝ) :
    renewalHinge a z = VaughanLogAverage.riesz z a := by
  induction a using Nat.strong_induction_on generalizing z with
  | h a ih =>
    by_cases ha1 : a = 1
    · subst a
      simp [renewalHinge, VaughanLogAverage.riesz]
    · obtain ⟨_, hc, _, hlt⟩ := minFac_child ha ha1
      rw [renewalHinge, if_neg ha.ne_zero, if_neg ha1,
        ih _ hlt hc, ih _ hlt hc, ← riesz_minFac z ha ha1]

/-- The first renewal step of the literal discrepancy retains the
unsaturated correction. The child is evaluated at the original full label. -/
theorem pairDiscrepancy_minFac (L : ℝ) (p q : ℕ) {a : ℕ}
    (ha : Squarefree a) (ha1 : a ≠ 1) :
    pairDiscrepancy L p q a = ArithmeticFunction.vonMangoldt a -
      VaughanLogAverage.riesz (L - Real.log p - Real.log q) (a / a.minFac) +
      VaughanLogAverage.riesz (L - Real.log p - Real.log q - Real.log a.minFac)
        (a / a.minFac) + saturationCorrection L p q a := by
  rw [pairDiscrepancy, riesz_minFac _ ha ha1]
  ring

/-- The exact finite renewal step on `pairForm`. Every original mask,
incidence denominator, allocation weight and complex kernel stays in place;
there is no comparison with an unweighted or completed sieve sum. -/
theorem pairForm_eq_minFac_renewal (u : ℝ) (N : ℕ) (S : Finset ℕ) (kernel : ℕ → ℂ)
    (hS : ∀ n ∈ S, 3 ≤ n.primeFactors.card) :
    pairForm u N S kernel =
      ∑ n ∈ S.filter Squarefree, ∑ pq ∈ primePairs n,
        let a := n / (pq.1 * pq.2)
        let z := SquarefreeVaughanLogSource.length u N - Real.log pq.1 - Real.log pq.2
        ((1 - boundedShare (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n : ℝ) : ℂ) *
          ((Real.log n / SquarefreeVaughanLogSource.length u N *
            (ArithmeticFunction.vonMangoldt a - VaughanLogAverage.riesz z (a / a.minFac) +
              VaughanLogAverage.riesz (z - Real.log a.minFac) (a / a.minFac) +
                saturationCorrection (SquarefreeVaughanLogSource.length u N) pq.1 pq.2 a) : ℝ) : ℂ) *
          kernel n / ((primePairs n).card : ℂ) := by
  unfold pairForm
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hnS, hsf⟩ := Finset.mem_filter.mp hn
  apply Finset.sum_congr rfl
  intro pq hpq
  obtain ⟨ha, ha1, _, _⟩ := primePair_cofactor hsf (hS n hnS) hpq
  rw [pairDiscrepancy_minFac _ _ _ ha (by omega)]

end
end RiemannGaussian.ZetaRieszTypeII
