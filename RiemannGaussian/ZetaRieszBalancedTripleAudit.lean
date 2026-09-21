/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSymmetricOperators
import RiemannGaussian.ZetaRieszAllowancePrimeBoxes
import RiemannGaussian.ZetaRieszLowerDegreeBounds
import RiemannGaussian.ZetaRieszAllowanceGrowth
import RiemannGaussian.ZetaRieszCompleteOperators

/-!
# The obstruction's actual balanced triples have a different cutoff polynomial

This audit uses the original floor-defined length and the same prime boxes
as the positive-allowance obstruction. They lie outside LinearClass and
have the pair-saturated coefficient, eventually throughout that radius range.
-/

namespace RiemannGaussian.ZetaRieszBalancedTripleAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszReflectedLinear ZetaRieszSymmetricOperators
open ZetaRieszPrimeCountFrequency

/-- Every prime in an actual triple box retains its lower logarithmic endpoint. -/
theorem tripleProducts_prime_log_gt {a h : ℝ} (_hh : 0 ≤ h) {n : ℕ}
    (hn : n ∈ tripleProducts a h) : ∀ p ∈ n.primeFactors, a < Real.log p := by
  obtain ⟨⟨⟨p,q⟩,r⟩, hv, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hpq,hr⟩ := Finset.mem_product.mp hv
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  have pB := logPrimes_bounds hp
  have qB := logPrimes_bounds hq
  have rB := logPrimes_bounds hr
  intro v hv
  simp only [Nat.primeFactors_mul pB.1.ne_zero (Nat.mul_ne_zero qB.1.ne_zero rB.1.ne_zero),
    Nat.primeFactors_mul qB.1.ne_zero rB.1.ne_zero, pB.1.primeFactors,
    qB.1.primeFactors,rB.1.primeFactors,Finset.mem_union,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> linarith [pB.2.1,qB.2.1,rB.2.1]

/-- The same bounded translates used in the divergence proof eventually
have all three pair products strictly below the original physical cutoff. -/
theorem eventually_boxes_pair_saturated {u h C : ℝ} (hu : 1/2 ≤ u)
    (huh : u ≤ Real.exp (-(11/16 : ℝ))) (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, (2/3 : ℝ)*N ≤ a → a ≤ (2/3 : ℝ)*N+C →
      ∀ n ∈ tripleProducts a h,
        SquarefreeVaughanLogSource.length u N < Real.log n ∧
        (∀ p ∈ n.primeFactors,
          Real.log n-SquarefreeVaughanLogSource.length u N < Real.log p) ∧
        ¬LinearClass (SquarefreeVaughanLogSource.length u N) n := by
  have hu0 : 0 < u := by linarith
  have hl := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 27/40)
    (huh.trans_lt (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(27/40 : ℝ))))
  have hlarge : ∀ᶠ N : ℕ in atTop, 3*C+6*h < (1/60 : ℝ)*N :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ)<1/60)).eventually_gt_atTop _
  filter_upwards [hl,hlarge,eventually_ge_atTop 2] with N hLN hbig hN
  intro a ha hau n hn
  obtain ⟨hs,hk,htlo,hthi,hpmax⟩ := tripleProducts_bounds hh hn
  have hupper := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hlog2 : 2*Real.log 2 < (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlen : SquarefreeVaughanLogSource.length u N < Real.log n := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    nlinarith
  have hmin (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log n-SquarefreeVaughanLogSource.length u N < Real.log p := by
    have hpmin := tripleProducts_prime_log_gt hh hn p hp
    nlinarith
  refine ⟨hlen,hmin,?_⟩
  intro hc
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < n.primeFactors.card)
  exact (hmin p hp).not_ge (hc.2.2.2 p hp).2

/-- The obstruction's boxes are actual surviving labels with the
pair-saturated coefficient; their discrepancy is not a paid off-mask term. -/
theorem eventually_surviving_boxes_coefficient {u h C : ℝ} (hu : 1/2<u)
    (huh : u ≤ Real.exp (-(11/16 : ℝ))) (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3 : ℝ)*dyadicMomentOrder j+C →
      ∀ n ∈ tripleProducts a h,
        n ∈ ZetaRieszDominantAllocation.nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧
        ¬LinearClass (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n ∧
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n =
          (((Real.log n/SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))*
            (Real.log n-SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) : ℝ) : ℂ) := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually
    (eventually_boxes_pair_saturated hu.le huh hh hC),
    ZetaRieszAllowanceGrowth.eventually_tripleBoxes_survive hu huh hh hC] with j hj hsurvive
  intro a ha hau n hn
  obtain ⟨ht,hmin,hnot⟩ := hj a ha hau n hn
  obtain ⟨hs,hk,_⟩ := tripleProducts_bounds hh hn
  exact ⟨(hsurvive a ha hau).2 hn,hnot,
    coefficient_three_reflected_unit hs hk ht.le (fun p hp => (hmin p hp).le)⟩

/-- The explicit allocation-transfer band contains the same surviving
prime boxes that force the positive-allowance obstruction. -/
theorem eventually_boxes_subset_balancedTripleBand {u h C : ℝ} (hu : 1/2<u)
    (huh : u ≤ Real.exp (-(11/16 : ℝ))) (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3 : ℝ)*dyadicMomentOrder j+C →
      tripleProducts a h ⊆ ZetaRieszCompleteOperators.balancedTripleBand u
        (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually
    (eventually_boxes_pair_saturated hu.le huh hh hC),
    ZetaRieszAllowanceGrowth.eventually_tripleBoxes_survive hu huh hh hC] with j hj hsurvive
  intro a ha hau n hn
  obtain ⟨ht,hmin,_⟩ := hj a ha hau n hn
  obtain ⟨hbal,hsub⟩ := hsurvive a ha hau
  obtain ⟨hs,hk,htlo,_hthi,hpmax⟩ := tripleProducts_bounds hh hn
  apply Finset.mem_filter.mpr
  refine ⟨hsub hn,hs,hk,ht.le,?_⟩
  intro p hp
  exact ⟨(hmin p hp).le, by linarith [hpmax p hp]⟩

end
end RiemannGaussian.ZetaRieszBalancedTripleAudit
