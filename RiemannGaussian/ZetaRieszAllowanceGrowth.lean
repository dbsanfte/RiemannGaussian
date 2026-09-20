/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllowancePrimeBoxes

/-!
# Quantitative audit of the proposed positive allowance

Balanced three-prime products near `log n = 2N` survive every existing
mask. The prime number theorem supplies their number in positive phase
boxes. Their contribution tests the exact complement `B - B₄`.
-/

namespace RiemannGaussian.ZetaRieszAllowanceGrowth
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszAllowanceComplement
open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation ZetaRieszSperner
open ZetaRieszDominantAllocation ZetaRieszPrimeCountFrequency ZetaRieszMaskSupport

/-- Three-prime allowance on the central product window exceeds one already at order two. -/
theorem triple_allowance_ge_one {u : ℝ} (hu : 1/2 ≤ u) {N n : ℕ}
    (hN : 2 ≤ N) (hs : Squarefree n) (hk : n.primeFactors.card = 3)
    (ht : 2*(N:ℝ) ≤ Real.log n) :
    1 ≤ middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hLu : SquarefreeVaughanLogSource.length u N ≤ (3/2:ℝ)*N := by
    have := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    nlinarith [Real.log_two_lt_d9, Nat.cast_nonneg (α := ℝ) N]
  rw [middleLayerAllowance, if_pos ⟨hs,by omega⟩, hk]
  norm_num
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  rw [show Real.log n / SquarefreeVaughanLogSource.length u N * (Real.log n / 3) =
    (Real.log n)^2 / (3*SquarefreeVaughanLogSource.length u N) by ring]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [mul_self_le_mul_self (by positivity : (0:ℝ)≤2*N) ht,
    mul_nonneg (sub_nonneg.mpr hNR) (Nat.cast_nonneg (α := ℝ) N)]

/-- The full, unassigned three-prime fraction is eventually at least one half. -/
theorem eventually_triple_unassigned :
    ∀ᶠ N : ℕ in atTop, (1/2:ℝ) ≤ 1-3*Real.exp (-(N:ℝ)/64) := by
  have ht : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ)/64)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0:ℝ)<64)
    simpa only [neg_div, Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1/6)] with N hN
  linarith

/-- The actual atoms of a balanced positive-phase triple box have an explicit positive charge. -/
theorem triple_atom_lower (A : Finset ℕ) {u : ℝ} (hu : 1/2 ≤ u)
    {N n : ℕ} (hN : 2 ≤ N) {C h a y : ℝ}
    (_hC : 0 ≤ C) (hh : 0 ≤ h) (ha : (2/3:ℝ)*N ≤ a)
    (hau : a ≤ (2/3:ℝ)*N+C) (hbal : 3*h ≤ a)
    (hshare : (1/2:ℝ) ≤ 1-3*Real.exp (-(N:ℝ)/64))
    (hn : n ∈ tripleProducts a h) (hcos : (1/2:ℝ) ≤ Real.cos (y*Real.log n)) :
    Real.exp (-(3/2:ℝ)*(2*N+3*C+6*h)) * (2*N)^N / N.factorial / 4 ≤
      weight A N n *
        (middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n *
          |Real.cos (y*Real.log n)|) := by
  obtain ⟨hs,hk,htlo,hthi,hp⟩ := tripleProducts_bounds hh hn
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have ht : 2*(N:ℝ) ≤ Real.log n := by linarith
  have hn1 : 1 < n := by
    have ht0 : 0 < Real.log n := by linarith
    exact_mod_cast (Real.log_pos_iff (Nat.cast_nonneg n)).mp ht0
  have hb : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2 := by
    intro p hpn
    linarith [hp p hpn]
  have hw := balanced_weight_lower A N hs hn1 hb
  rw [hk] at hw
  norm_num only [Nat.cast_ofNat] at hw
  have hamp : 0 ≤ amplitude N n := ZetaRieszCosineCarrier.factorial_envelope_nonneg N n
  have hw' : amplitude N n/2 ≤ weight A N n := by nlinarith
  have hml := triple_allowance_ge_one hu hN hs hk ht
  have hm : (1/2:ℝ) ≤ middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n *
      |Real.cos (y*Real.log n)| := by
    have haC : (1/2:ℝ) ≤ |Real.cos (y*Real.log n)| := hcos.trans (le_abs_self _)
    nlinarith
  have hwlow : amplitude N n/4 ≤ weight A N n *
      (middleLayerAllowance (SquarefreeVaughanLogSource.length u N) n *
        |Real.cos (y*Real.log n)|) := by
    have := mul_le_mul hw' hm (by norm_num : (0:ℝ)≤1/2) (weight_nonneg A N n)
    nlinarith
  apply le_trans _ hwlow
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤4)
  unfold amplitude
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (by linarith)
  · exact pow_le_pow_left₀ (by positivity) ht N
  · positivity
  · positivity

/-- Uniformly in the bounded phase shift, every triple-box integer belongs to the actual complement. -/
theorem eventually_tripleBoxes_survive {u h C : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3:ℝ)*dyadicMomentOrder j ≤ a → a ≤ (2/3:ℝ)*dyadicMomentOrder j+C →
      3*h ≤ a ∧ tripleProducts a h ⊆
        nondominantBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have hn : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [eventually_ge_atTop 32,
    tendsto_dyadicMomentOrder.eventually (eventually_length_lower (by linarith) huh),
    hn.eventually (eventually_ge_atTop (12*C+24*h+2))] with j hj hL hN a ha hau
  have hbal : 3*h ≤ a := by nlinarith
  refine ⟨hbal,?_⟩
  intro n hnT
  obtain ⟨hs,hk,htlo,hthi,hp⟩ := tripleProducts_bounds hh hnT
  apply balanced_mem_nondominant j hj hu huh hL hs
  · apply (mem_literalWindow _ _).mpr
    constructor <;> nlinarith
  · omega
  · rw [hk]
    exact lt_of_lt_of_le (by decide : 3<4) (four_le_dyadicPrimeCount j)
  · intro p hpn
    linarith [hp p hpn]

/-- The exact factorial normalization of a full-density triple box has rate `2u`. -/
theorem triple_box_scalar_lower {u c D : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) :
    (u*c^3*Real.exp (-(3/2:ℝ)*D)/24) * (2*u)^N / ((N:ℝ)+1)^4 ≤
      u^(N+1) * ((c^3*Real.exp (2*(N:ℝ))/((N:ℝ)+1)^3) *
        (Real.exp (-(3/2:ℝ)*(2*N+D)) * (2*N)^N / N.factorial / 4)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hs := PrimeWindow.local_monomial_lower hN (by norm_num : (0:ℝ)≤2)
  norm_num [PrimeWindow.localGrowth] at hs
  rw [show -(2*(N:ℝ))/2 = -(N:ℝ) by ring] at hs
  have hs' : (2:ℝ)^N/(6*((N:ℝ)+1)) ≤
      Real.exp (-(N:ℝ)) * (2*N)^N / N.factorial := by
    apply le_trans _ hs
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have he : Real.exp (2*(N:ℝ)) * Real.exp (-(3/2:ℝ)*(2*N+D)) =
      Real.exp (-(3/2:ℝ)*D) * Real.exp (-(N:ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  let k := u^(N+1)*c^3*Real.exp (-(3/2:ℝ)*D)/(4*((N:ℝ)+1)^3)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ = k * ((2:ℝ)^N/(6*((N:ℝ)+1))) := by
      dsimp [k]
      rw [mul_pow, pow_succ]
      field_simp
      ring
    _ ≤ k * (Real.exp (-(N:ℝ)) * (2*N)^N / N.factorial) :=
      mul_le_mul_of_nonneg_left hs' hk
    _ = _ := by
      dsimp [k]
      calc
        _ = (u^(N+1)*c^3/(4*((N:ℝ)+1)^3)) *
          (Real.exp (-(3/2:ℝ)*D)*Real.exp (-(N:ℝ))) * ((2*N)^N/N.factorial) := by ring
        _ = _ := by rw [← he]; field_simp

/-- The actual complement has an exponential lower bound at every fixed height throughout the requested radius interval. -/
theorem eventually_complement_growth {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (y : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop,
      c * (2*u)^dyadicMomentOrder j / ((dyadicMomentOrder j:ℝ)+1)^4 ≤
        antichainBudget u y j - fourCharge u y j := by
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_positive_phase_boxes y
  obtain ⟨c,hc,hcount⟩ := eventually_logPrimes_card_lower hh
    (show 0 ≤ C+2*h by linarith)
  let D := 3*C+6*h
  let k := u*c^3*Real.exp (-(3/2:ℝ)*D)/24
  have hu0 : 0<u := by linarith
  have hk : 0<k := by dsimp [k]; positivity
  refine ⟨k,hk,?_⟩
  filter_upwards [eventually_tripleBoxes_survive hu huh hh.le hC,
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
  have hcomp := subfamily_le_complement hu0.le y j T hsub (by
    intro n hn hFour
    have ht := (tripleProducts_bounds hh.le hn).2.1
    have hf := hFour.2.1
    omega)
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

/-- The fixed polynomial denominator cannot suppress the strictly superunit rate. -/
theorem geometric_over_successor_four_tendsto {r : ℝ} (hr : 1<r) :
    Tendsto (fun N : ℕ => r^N / ((N:ℝ)+1)^4) atTop atTop := by
  have hr0 : 0<r := by linarith
  have ht := ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
    (inv_pos.mpr hr0) (inv_lt_one_of_one_lt₀ hr)
  have ht' : Tendsto (fun N : ℕ => ((N:ℝ)+1)^4 * r⁻¹^N) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun N => by
      change 0 < ((N:ℝ)+1)^4*r⁻¹^N
      positivity)⟩
  have hi := ht'.inv_tendsto_nhdsGT_zero
  change Tendsto (fun N : ℕ => (((N:ℝ)+1)^4*r⁻¹^N)⁻¹) atTop atTop at hi
  simpa only [mul_inv_rev,inv_pow,inv_inv,div_eq_mul_inv] using hi

/-- The exact complement `B-B₄` diverges, with every existing support restriction in force. -/
theorem complement_tendsto_atTop {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (y : ℝ) :
    Tendsto (fun j => antichainBudget u y j-fourCharge u y j) atTop atTop := by
  obtain ⟨c,hc,hbound⟩ := eventually_complement_growth hu huh y
  have ht := ((geometric_over_successor_four_tendsto (by linarith : 1<2*u)).comp
    tendsto_dyadicMomentOrder).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop hbound
  simpa only [Function.comp_def,mul_div_assoc] using ht

/-- The proposed improved allowance also diverges at every fixed height: it cannot close the source contradiction. -/
theorem improved_allowance_tendsto_atTop {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (y : ℝ) :
    Tendsto (fun j => antichainBudget u y j-(3/4:ℝ)*fourCharge u y j) atTop atTop := by
  apply tendsto_atTop_mono (fun j => ?_) (complement_tendsto_atTop hu huh y)
  linarith [fourCharge_nonneg (show 0≤u by linarith) y j]

/-- No cofinal subsequence can meet the requested three-fortieths ceiling for this exact allowance. -/
theorem not_frequently_improved_allowance_le_three_fortieths {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ))) (y : ℝ) :
    ¬ ∃ᶠ j in atTop,
      antichainBudget u y j-(3/4:ℝ)*fourCharge u y j ≤ (3/40:ℝ) := by
  intro h
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually
    ((improved_allowance_tendsto_atTop hu huh y).eventually_gt_atTop (3/40))).exists
  exact hgt.not_ge hle

end
end RiemannGaussian.ZetaRieszAllowanceGrowth
