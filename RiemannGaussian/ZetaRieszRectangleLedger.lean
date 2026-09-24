/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleReserve

/-!
# The rectangle's sign in the original carrier ledger

The same literal factorial rectangle belongs to the unique-owner carrier.
Its positive sign in subtraction of the nonowner correction removes a
duplicate incidence; its original owned copy remains negative. The exact
finite complement below is still arithmetic, not an assumed small error.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency

/-- Every selected triple term also lies in the existing largest-prime
owner band, with the complementary cofactor order N+1-j. -/
theorem rectangle_owner_order {N j h : ℕ} (hN : 1000 ≤ N)
    (hh : h ∈ rectangleOrders N j) : N + 1 - j ∈ ownerOrders N := by
  obtain ⟨hr, _, hlo, hhi, _, _⟩ := Finset.mem_filter.mp hh
  have := Finset.mem_range.mp hr
  simp only [ownerOrders, Finset.mem_filter, Finset.mem_range]
  omega

private theorem mass_complement (M j : ℕ) (hj : j ≤ M) (x : ℝ) :
    mass M j (1 - x) = mass M (M - j) x := by
  rw [mass, mass, sub_sub_cancel, Nat.sub_sub_self hj, Nat.choose_symm hj]
  ring

private theorem owner_marginal (N : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (N + 2),
      if N + 1 - j ∈ ownerOrders N then mass (N + 1) j (1 - x) else 0) =
      ∑ k ∈ ownerOrders N, mass (N + 1) k x := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => N + 1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro a ha b hb he
    have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    omega
  · intro k hk
    have hkM := ownerOrders_le hk
    refine ⟨N + 1 - k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
    · simpa only [Nat.sub_sub_self hkM] using hk
    · omega
  · intro j hj
    exact mass_complement _ _ (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega) x

/-- The rectangle is an actual suballocation of the original unique
owner, not merely a new positive correction with no matching owned copy. -/
theorem rectangleMass_le_owner (N : ℕ) (hN : 1000 ≤ N) {x c : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    rectangleMass N x c ≤ ∑ k ∈ ownerOrders N, mass (N + 1) k x := by
  rw [← owner_marginal]
  unfold rectangleMass
  apply Finset.sum_le_sum
  intro j _
  have hm := mass_nonneg (N + 1) j (by linarith : 0 ≤ 1 - x) (by linarith : 1 - x ≤ 1)
  by_cases hj : N + 1 - j ∈ ownerOrders N
  · rw [if_pos hj]
    apply mul_le_of_le_one_right hm
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun h _ _ => mass_nonneg _ _ hc hc1)).trans_eq (mass_total _ _)
  · rw [if_neg hj]
    have he : rectangleOrders N j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hj (rectangle_owner_order hN hh)
    simp [he]

/-- The exact selected integer weight; the second incidence is unique. -/
def ownedRectangleWeight (u : ℝ) (N n : ℕ) : ℝ :=
  ∑ q ∈ rectangleIncidences u N n,
    rectangleMass N (Real.log (n / largestPrime n : ℕ) / Real.log n)
      (Real.log (smallPrime n q) / Real.log (n / largestPrime n : ℕ))

/-- Its finite complement in the uniquely owned carrier has a
nonnegative allocation weight. This gives no sign for the complex sum. -/
theorem ownedRectangleWeight_bounds (u : ℝ) (N : ℕ) (hN : 1000 ≤ N) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 3) :
    0 ≤ ownedRectangleWeight u N n ∧ ownedRectangleWeight u N n ≤ ownerShare N n := by
  have hb := ownerShare_bounds N hn hc
  constructor
  · apply Finset.sum_nonneg
    intro q hq
    obtain ⟨_, _, _, hx, hr⟩ := second_log_data hn hc (Finset.mem_filter.mp hq).1
    exact (rectangleMass_bounds N hx.1 hx.2 hr.1 hr.2).1
  · have hs := Finset.sum_le_sum (s := rectangleIncidences u N n) (fun q hq => by
      obtain ⟨_, _, _, hx, hr⟩ := second_log_data hn hc (Finset.mem_filter.mp hq).1
      exact rectangleMass_le_owner N hN hx.1 hx.2 hr.1 hr.2)
    change ownedRectangleWeight u N n ≤ ∑ _q ∈ rectangleIncidences u N n, ownerShare N n at hs
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    apply hs.trans
    apply mul_le_of_le_one_left hb.1
    have hcard : (rectangleIncidences u N n).card ≤ 1 :=
      (Finset.card_filter_le _ _).trans (secondIncidences_card_le_one hn)
    exact_mod_cast hcard

/-- The rectangle is exactly the corresponding weight of the original
signed residual atom, with no completion in this identity. -/
theorem rectangleResponse_eq_ownedWeight (u y : ℝ) (N K : ℕ) :
    rectangleResponse u y N K = ∑ n ∈ tripleBand u N K,
      (ownedRectangleWeight u N n : ℂ) *
        (residualCoefficient (intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n *
            zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n) := by
  unfold rectangleResponse ownedRectangleWeight
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro q _
  unfold rectangleAtom rawRectangleAtom residualCoefficient
  ring

/-- The literal finite remainder of the uniquely owned carrier after
the selected rectangle, with its original phase and allocation. -/
def ownerRectangleComplement (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ tripleBand u N K,
    ((ownerShare N n - ownedRectangleWeight u N n : ℝ) : ℂ) *
      (residualCoefficient (intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n *
          zetaPrimeLogKernel N (3 / 2 + Complex.I * y) n)

/-- The original owned carrier contains the same rectangle with its
negative sign. The positive nonowner-correction orientation cannot be
counted as an additional positive term in this direct finite partition. -/
theorem ownerCompanion_rectangle_partition (u y : ℝ) (N K : ℕ) :
    ownerCompanion u y N K =
      rectangleResponse u y N K + ownerRectangleComplement u y N K := by
  rw [rectangleResponse_eq_ownedWeight]
  unfold ownerCompanion ownerRectangleComplement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ownerAtom_eq_share _ (SquarefreeVaughanLogSource.length_pos u N) y N
    (Finset.mem_filter.mp hn).2.1 (Finset.mem_filter.mp hn).2.2]
  push_cast
  ring

/-- In the direct literal triple ledger the rectangle reserve is
subtracted, because the original owned incidence survives. -/
theorem tripleResponse_rectangle_ledger (u y : ℝ) (N K : ℕ) :
    tripleResponse u y N K = ownerRectangleComplement u y N K +
      unallocatedTriples u y N K - rectangleReserve u y N K := by
  rw [triple_decomposition, ownerCompanion_rectangle_partition, rectangleReserve]
  ring

/-- The matching owned rectangle cannot be discarded as an o(1)
error when the positive correction reserve is harvested. -/
theorem not_tendsto_owned_rectangle_zero (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ¬Tendsto (fun t => (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder t + 1)) *
      (ownerCompanion (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder t) (dyadicPrimeCount t) -
        ownerRectangleComplement (3 / 2 - rho.1.re) rho.1.im
          (dyadicMomentOrder t) (dyadicPrimeCount t))) atTop (𝓝 0) := by
  intro hz
  have hz' := (Complex.continuous_re.tendsto _).comp hz.neg
  simp only [neg_zero, Complex.zero_re] at hz'
  have hpos := eventually_rectangleReserve_ge rho hrho hexposed huU hsimple
  have hpos' : ∀ᶠ t : ℕ in atTop, (1 / 160 : ℝ) ≤
      (-( (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder t + 1)) *
        (ownerCompanion (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder t) (dyadicPrimeCount t) -
          ownerRectangleComplement (3 / 2 - rho.1.re) rho.1.im
            (dyadicMomentOrder t) (dyadicPrimeCount t)))).re := by
    simpa only [ownerCompanion_rectangle_partition, add_sub_cancel_right,
      rectangleReserve, mul_neg] using hpos
  have h := ge_of_tendsto hz' hpos'
  norm_num at h

end
end RiemannGaussian.ZetaRieszSkewAllocation
