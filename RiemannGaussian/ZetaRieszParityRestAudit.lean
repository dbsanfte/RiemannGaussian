/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFullParityPacket
import RiemannGaussian.ZetaRieszBalancedTripleAudit

/-!
# The existing independent allowance after selecting the parity packet

The old balanced triple witnesses lie in the smaller core window, entirely
outside the selected largest-prime share box. Thus the existing one-sided
allowance for the literal rest still diverges. This is not a divergence
theorem for the signed rest, nor a no-go theorem for joint cancellation.
-/

namespace RiemannGaussian.ZetaRieszParityRestAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszParityPacket ZetaRieszPrimeEndpoint ZetaRieszPrimeCountFrequency
open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation ZetaRieszSperner
open ZetaRieszAllowancePrimeBoxes ZetaRieszAllowanceGrowth

/-- The selected largest-prime share excludes every balanced label. -/
theorem balanced_selection_zero (u : ℝ) (N K : ℕ) {n : ℕ}
    (hbal : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2) :
    fullParitySelection u N K n = 0 := by
  apply if_neg
  intro hn
  have hb := (Finset.mem_filter.mp hn).2.1
  have hp := hbal (largestPrime n) hb.largest_mem
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast hb.nontrivial)
  linarith [hb.largest_lower]

/-- The actual old phase-cost estimate applied to the literal remaining
suballocation, with no zero or packet-decay premise. -/
def restAllowance (u y : ℝ) (j : ℕ) : ℝ :=
  u^(dyadicMomentOrder j+1)*∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
    (1-fullParitySelection u (dyadicMomentOrder j) (dyadicPrimeCount j) n)*
      (weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n*
          phaseCost (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) y n)

/-- This allowance really bounds the unchanged signed rest from below. -/
theorem fullParityRest_lower {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ) :
    -restAllowance u y j ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        fullParityRest u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, restAllowance, ← mul_neg]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  rw [fullParityRest, Complex.re_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro n _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left
    (residual_atom_lower (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length_pos u (dyadicMomentOrder j)) y (dyadicMomentOrder j) n)
    (sub_nonneg.mpr (fullParitySelection_bounds u (dyadicMomentOrder j) (dyadicPrimeCount j) n).2)

/-- Every old balanced triple witness survives unaltered in the literal
rest, including the narrower core window and the phase-cost fallback. -/
theorem eventually_boxes_in_rest {u h C : ℝ} (hu : 1/2<u)
    (huh : u ≤ Real.exp (-(11/16 : ℝ))) (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3 : ℝ)*dyadicMomentOrder j+C →
      3*h ≤ a ∧ ∀ n ∈ tripleProducts a h,
        n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧
        fullParitySelection u (dyadicMomentOrder j) (dyadicPrimeCount j) n = 0 ∧
        ¬ZetaRieszReflectedLinear.LinearClass
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n := by
  have ht : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [eventually_tripleBoxes_survive hu huh hh hC,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszBalancedTripleAudit.eventually_boxes_pair_saturated hu.le huh hh hC),
    ht.eventually_gt_atTop (100*(3*C+6*h+1))] with j hsurvive hsaturated hlarge
  intro a ha hau
  obtain ⟨hbal, hsub⟩ := hsurvive a ha hau
  refine ⟨hbal, ?_⟩
  intro n hn
  obtain ⟨_, _, htlo, hthi, hp⟩ := tripleProducts_bounds hh hn
  have hb : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2 := by
    intro p hpn
    linarith [hp p hpn]
  refine ⟨?_, balanced_selection_zero u _ _ hb, (hsaturated a ha hau n hn).2.2⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨hsub hn, by constructor <;> nlinarith⟩
  · constructor <;> nlinarith

private theorem subfamily_le_restAllowance {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (j : ℕ)
    (T : Finset ℕ)
    (hT : ∀ n ∈ T,
      n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧
      fullParitySelection u (dyadicMomentOrder j) (dyadicPrimeCount j) n = 0 ∧
      ¬ZetaRieszReflectedLinear.LinearClass
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n) :
    u^(dyadicMomentOrder j+1)*∑ n ∈ T,
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (dyadicMomentOrder j) n*
          (middleLayerAllowance (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
            |Real.cos (y*Real.log n)|) ≤ restAllowance u y j := by
  unfold restAllowance
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  apply le_trans (le_of_eq ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (hT n hn).1) ?_)
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(hT n hn).2.1, sub_zero, one_mul, phaseCost, if_neg (hT n hn).2.2]
  · intro n _ _
    exact mul_nonneg (sub_nonneg.mpr (fullParitySelection_bounds u _ _ n).2)
      (mul_nonneg (weight_nonneg _ _ _) (phaseCost_nonneg
        (SquarefreeVaughanLogSource.length_pos _ _) _ _))

/-- The existing one-sided allowance for the literal rest still has a superunit geometric lower bound at every fixed height. -/
theorem eventually_restAllowance_growth {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (y : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop,
      c * (2*u)^dyadicMomentOrder j / ((dyadicMomentOrder j:ℝ)+1)^4 ≤
        restAllowance u y j := by
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_positive_phase_boxes y
  obtain ⟨c,hc,hcount⟩ := eventually_logPrimes_card_lower hh
    (show 0 ≤ C+2*h by linarith)
  let D := 3*C+6*h
  let k := u*c^3*Real.exp (-(3/2:ℝ)*D)/24
  have hu0 : 0<u := by linarith
  have hk : 0<k := by dsimp [k]; positivity
  refine ⟨k,hk,?_⟩
  filter_upwards [eventually_boxes_in_rest hu huh hh.le hC,
    tendsto_dyadicMomentOrder.eventually hcount,
    tendsto_dyadicMomentOrder.eventually eventually_triple_unassigned,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 2)] with j hsurvive hcountj hshare hN
  let N := dyadicMomentOrder j
  obtain ⟨a,ha,hau,hcos⟩ := hphase ((2/3:ℝ)*N)
  obtain ⟨hbal,hsub⟩ := hsurvive a ha hau
  let T := tripleProducts a h
  let M := c*Real.exp ((2/3:ℝ)*N)/((N:ℝ)+1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp : M ≤ ((logPrimes a h).card : ℝ) :=
    hcountj a ha (by linarith)
  have hq : M ≤ ((logPrimes (a+h) h).card : ℝ) :=
    hcountj (a+h) (by linarith) (by linarith)
  have hr : M ≤ ((logPrimes (a+2*h) h).card : ℝ) :=
    hcountj (a+2*h) (by linarith) (by linarith)
  have hcard : c^3*Real.exp (2*(N:ℝ))/((N:ℝ)+1)^3 ≤ (T.card:ℝ) := by
    have hm : M^3 ≤ ((logPrimes a h).card : ℝ)*((logPrimes (a+h) h).card : ℝ)*
        ((logPrimes (a+2*h) h).card : ℝ) := by
      rw [pow_succ, pow_two]
      exact mul_le_mul (mul_le_mul hp hq hM (Nat.cast_nonneg _)) hr hM (by positivity)
    have hex : Real.exp ((2/3:ℝ)*N)^3 = Real.exp (2*(N:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp only [M] at hm
    rw [div_pow,mul_pow,hex] at hm
    simpa only [T,tripleProducts_card hh.le,Nat.cast_mul] using hm
  let Q := Real.exp (-(3/2:ℝ)*(2*N+D)) * (2*N)^N / N.factorial / 4
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs : (T.card:ℝ)*Q ≤ ∑ n ∈ T,
      weight (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n *
        (middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n *
          |Real.cos (y*Real.log n)|) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    have hb := tripleProducts_bounds hh.le hn
    simpa only [Q,D,add_assoc] using triple_atom_lower
      (ZetaRieszAnnulusJoint.intermediatePrimes u N) hu.le hN hC hh.le ha hau hbal hshare hn
        (hcos _ hb.2.2.1.le hb.2.2.2.1)
  have hcomp := subfamily_le_restAllowance hu0.le y j T hsub
  calc
    _ ≤ u^(N+1)*((c^3*Real.exp (2*(N:ℝ))/((N:ℝ)+1)^3)*Q) :=
      triple_box_scalar_lower hu0.le hc.le (by omega)
    _ ≤ u^(N+1)*((T.card:ℝ)*Q) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcard hQ) (pow_nonneg hu0.le _)
    _ ≤ u^(N+1)*(∑ n ∈ T,
        weight (ZetaRieszAnnulusJoint.intermediatePrimes u N) N n *
          (middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n *
            |Real.cos (y*Real.log n)|)) := mul_le_mul_of_nonneg_left hs (pow_nonneg hu0.le _)
    _ ≤ _ := hcomp

/-- Removing the selected parity packet does not make the already proved
phase-cost allowance finite. No conclusion about the signed rest follows. -/
theorem restAllowance_tendsto_atTop {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16 : ℝ))) (y : ℝ) :
    Tendsto (restAllowance u y) atTop atTop := by
  obtain ⟨c,hc,hbound⟩ := eventually_restAllowance_growth hu huh y
  have ht := ((geometric_over_successor_four_tendsto (by linarith : 1<2*u)).comp
    tendsto_dyadicMomentOrder).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop hbound
  simpa only [Function.comp_def,mul_div_assoc] using ht

/-- In particular, this independent allowance cannot supply the required
three-fortieths floor, even along a cofinal subsequence. -/
theorem not_frequently_restAllowance_le {u : ℝ}
    (hu : 1/2<u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y B : ℝ) :
    ¬ ∃ᶠ j in atTop, restAllowance u y j ≤ B := by
  have ht := restAllowance_tendsto_atTop hu
    (huU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) y
  intro h
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually (ht.eventually_gt_atTop B)).exists
  exact hgt.not_ge hle

end
end RiemannGaussian.ZetaRieszParityRestAudit
