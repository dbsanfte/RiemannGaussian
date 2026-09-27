/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointDominantFloor
import RiemannGaussian.ZetaRieszAllowanceGrowth
import RiemannGaussian.ZetaRieszSymmetricOperators

/-!
# Positive phase credit that a joint lower bound must retain

Balanced actual three-prime boxes supply positive real credit at rate
`(2*u)^N/(N+1)^4`, with the original residual allocation, phase and core
masks. This is a bound for a literal subfamily, not a free reserve: the
whole signed complement remains. In particular positive-phase deletion
cannot be an asymptotically negligible step toward the joint floor.
-/

namespace RiemannGaussian.ZetaRieszJointPhaseCredit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszAllowanceGrowth
open ZetaRieszAllowanceComplement ZetaRieszOneSidedArithmetic
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszParityPacket ZetaRieszSperner

/-- With the newly paid large-prime region removed, seven or more
prime factors force the least logarithm strictly below the reflected
cutoff. Thus the unit tent's rising-edge defect is confined to counts
at most six; no estimate of the other signed divisor terms is implied. -/
theorem least_log_reflected_margin {n P N : ℕ} (hs : Squarefree n)
    (hcount : 7 ≤ n.primeFactors.card) (hP : P ∈ n.primeFactors)
    (hshare : Real.log P ≤ (121/200 : ℝ)*Real.log n)
    {L : ℝ} (hL : (137/100 : ℝ)*N ≤ L)
    (hwindow : Real.log n ≤ (203/100 : ℝ)*N) :
    Real.log n.minFac+(1/300 : ℝ)*Real.log n ≤ L-Real.log P := by
  have hc : (6 : ℝ) ≤ (n.primeFactors.erase P).card := by
    have h := Finset.card_erase_add_one hP
    exact_mod_cast (show 6 ≤ (n.primeFactors.erase P).card by omega)
  have hl (q : ℕ) (hq : q ∈ n.primeFactors.erase P) : Real.log n.minFac ≤ Real.log q := by
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
    have hd := Nat.minFac_le_of_dvd hqp.two_le
      (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hq))
    exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos n)
      (by exact_mod_cast hd)
  have hsum := Finset.sum_le_sum (fun q hq => hl q hq)
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have he := Finset.sum_erase_add n.primeFactors (fun q : ℕ => Real.log q) hP
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at he
  have hleast := Real.log_natCast_nonneg n.minFac
  have htotal := Real.log_natCast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right hc hleast]

/-- The only new debit in the comparison retaining positive unit credit
vanishes exactly at counts at least seven on this literal geometry. -/
theorem rising_edge_zero_of_seven {n P N : ℕ} (hs : Squarefree n)
    (hcount : 7 ≤ n.primeFactors.card) (hP : P ∈ n.primeFactors)
    (hshare : Real.log P ≤ (121/200 : ℝ)*Real.log n)
    {L : ℝ} (hL : (137/100 : ℝ)*N ≤ L)
    (hwindow : Real.log n ≤ (203/100 : ℝ)*N) :
    max 0 (Real.log n.minFac-max 0 (L-Real.log P)) = 0 := by
  have h := least_log_reflected_margin hs hcount hP hshare hL hwindow
  apply max_eq_left
  have hm := le_max_right 0 (L-Real.log P)
  nlinarith [Real.log_natCast_nonneg n]

/-- The actual balanced box has a positive coefficient comparable to
its earlier allowance. The pair cutoffs are checked, not dropped. -/
theorem box_coefficient_lower {a h L : ℝ} (hh : 0 ≤ h) (hL : 0 < L)
    (hpairs : 2*a+6*h ≤ L) {n : ℕ} (hn : n ∈ tripleProducts a h)
    (hLhi : L ≤ (3/4 : ℝ)*Real.log n) :
    (3/4 : ℝ)*middleLayerAllowance L n ≤
      (SquarefreeVaughanLogSource.coefficient L n).re := by
  obtain ⟨hs,hk,_,_,_⟩ := tripleProducts_bounds hh hn
  have he : SquarefreeVaughanLogSource.coefficient L n =
      (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ) := by
    obtain ⟨⟨⟨p,q⟩,r⟩,hv,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hpq,hr⟩ := Finset.mem_product.mp hv
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
    have bp := logPrimes_bounds hp
    have bq := logPrimes_bounds hq
    have br := logPrimes_bounds hr
    exact ZetaRieszSymmetricOperators.coefficient_three_pair_saturated
      bp.1 bq.1 br.1
      (logPrimes_order (by linarith) hp hq).ne
      (logPrimes_order (by linarith) hp hr).ne
      (logPrimes_order (by linarith) hq hr).ne
      (by linarith) (by linarith) (by linarith)
      (by nlinarith [Real.log_natCast_nonneg (p*(q*r))])
  rw [he,Complex.ofReal_re,middleLayerAllowance,if_pos ⟨hs,by omega⟩,hk]
  norm_num
  have ht : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg _) hL.le
  nlinarith [mul_le_mul_of_nonneg_left hLhi ht]

/-- The full signed original atom keeps a fixed fraction of the
positive-phase box charge. This does not replace its observation by an
absolute value: the explicit positive cosine assumption is used. -/
theorem box_atom_lower (A : Finset ℕ) {u : ℝ} (hu : 1/2 ≤ u)
    {N n : ℕ} (hN : 2 ≤ N) {C h a y : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (ha : (2/3 : ℝ)*N ≤ a)
    (hau : a ≤ (2/3 : ℝ)*N+C) (hbal : 3*h ≤ a)
    (hpairs : 2*a+6*h ≤ SquarefreeVaughanLogSource.length u N)
    (hshare : (1/2 : ℝ) ≤ 1-3*Real.exp (-(N : ℝ)/64))
    (hn : n ∈ tripleProducts a h) (hcos : (1/2 : ℝ) ≤ Real.cos (y*Real.log n)) :
    (3/4 : ℝ)*(Real.exp (-(3/2 : ℝ)*(2*N+3*C+6*h))*(2*N)^N/N.factorial/4) ≤
      (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := tripleProducts_bounds hh hn
  have hLu : SquarefreeVaughanLogSource.length u N ≤ (3/2 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  have hc := box_coefficient_lower hh (SquarefreeVaughanLogSource.length_pos u N)
    hpairs hn (by linarith [hb.2.2.1])
  have he := triple_atom_lower A hu hN hC hh ha hau hbal hshare hn hcos
  rw [re_residual_atom]
  rw [abs_of_nonneg (by linarith : 0 ≤ Real.cos (y*Real.log n))] at he
  have hx := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ Real.cos (y*Real.log n)))
    (weight_nonneg A N n)
  linarith

/-- The positive boxes lie in the literal smaller core and below every
dominant-prime threshold. The original count and physical masks are
discharged by the earlier prime-box theorem. -/
theorem eventually_boxes_in_core {u h C : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hh : 0 ≤ h) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (2/3 : ℝ)*dyadicMomentOrder j ≤ a →
      a ≤ (2/3 : ℝ)*dyadicMomentOrder j+C →
      3*h ≤ a ∧ 2*a+6*h ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) ∧
        tripleProducts a h ⊆ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have huh := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (huh.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  have hn : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [eventually_tripleBoxes_survive hu huh.le hh hC,
    tendsto_dyadicMomentOrder.eventually hL,
    hn.eventually_ge_atTop (1000*(C+h+1))]
    with j hsurvive hL hsize a ha hau
  obtain ⟨hbal,hsub⟩ := hsurvive a ha hau
  refine ⟨hbal,by nlinarith,?_⟩
  intro n hnT
  have hb := tripleProducts_bounds hh hnT
  have hw : (39/20 : ℝ)*dyadicMomentOrder j < Real.log n ∧
      Real.log n ≤ (203/100 : ℝ)*dyadicMomentOrder j := by
    constructor <;> nlinarith [hb.2.2.1,hb.2.2.2.1]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hsub hnT,by constructor <;> nlinarith [hw.1,hw.2]⟩,hw⟩

/-- At every fixed height, the actual core contains exponentially growing
positive credit. These are ordinary primes with the original residual
coefficient; this is not the old antichain allowance. -/
theorem eventually_positive_credit_growth {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ j : ℕ in atTop,
      k*(2*u)^dyadicMomentOrder j/((dyadicMomentOrder j : ℝ)+1)^4 ≤
        u^(dyadicMomentOrder j+1)*∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
          max (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re 0 := by
  obtain ⟨h,C,hh,hC,hphase⟩ := exists_positive_phase_boxes y
  obtain ⟨c,hc,hcount⟩ := eventually_logPrimes_card_lower hh
    (show 0 ≤ C+2*h by linarith)
  let D := 3*C+6*h
  let k := (3/4 : ℝ)*(u*c^3*Real.exp (-(3/2 : ℝ)*D)/24)
  have hu0 : 0 < u := by linarith
  refine ⟨k,by dsimp [k]; positivity,?_⟩
  filter_upwards [eventually_boxes_in_core hu hU hh.le hC,
    tendsto_dyadicMomentOrder.eventually hcount,
    tendsto_dyadicMomentOrder.eventually eventually_triple_unassigned,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 2)]
    with j hsurvive hcountj hshare hN
  let N := dyadicMomentOrder j
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let f := fun n => (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  obtain ⟨a,ha,hau,hcos⟩ := hphase ((2/3 : ℝ)*N)
  obtain ⟨hbal,hpairs,hsub⟩ := hsurvive a ha hau
  let T := tripleProducts a h
  let M := c*Real.exp ((2/3 : ℝ)*N)/((N : ℝ)+1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp : M ≤ ((logPrimes a h).card : ℝ) := hcountj a ha (by linarith)
  have hq : M ≤ ((logPrimes (a+h) h).card : ℝ) :=
    hcountj (a+h) (by linarith) (by linarith)
  have hr : M ≤ ((logPrimes (a+2*h) h).card : ℝ) :=
    hcountj (a+2*h) (by linarith) (by linarith)
  have hcard : c^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3 ≤ (T.card : ℝ) := by
    have hm : M^3 ≤ ((logPrimes a h).card : ℝ)*((logPrimes (a+h) h).card : ℝ)*
        ((logPrimes (a+2*h) h).card : ℝ) := by
      rw [pow_succ,pow_two]
      exact mul_le_mul (mul_le_mul hp hq hM (Nat.cast_nonneg _)) hr hM (by positivity)
    have hex : Real.exp ((2/3 : ℝ)*N)^3 = Real.exp (2*(N : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp only [M] at hm
    rw [div_pow,mul_pow,hex] at hm
    simpa only [T,tripleProducts_card hh.le,Nat.cast_mul] using hm
  let Q := Real.exp (-(3/2 : ℝ)*(2*N+D))*(2*N)^N/N.factorial/4
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hs : (T.card : ℝ)*((3/4 : ℝ)*Q) ≤ ∑ n ∈ T, f n := by
    rw [← nsmul_eq_mul,← Finset.sum_const]
    apply Finset.sum_le_sum
    intro n hn
    have hb := tripleProducts_bounds hh.le hn
    simpa only [Q,D,f,add_assoc] using box_atom_lower A hu.le hN hC hh.le ha hau hbal hpairs
      hshare hn (hcos _ hb.2.2.1.le hb.2.2.2.1)
  have hwhole : (∑ n ∈ T, f n) ≤
      ∑ n ∈ coreBand u N (dyadicPrimeCount j), max (f n) 0 := by
    apply (Finset.sum_le_sum (fun n _ => le_max_left (f n) 0)).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => le_max_right (f n) 0)
  have hscalar := mul_le_mul_of_nonneg_left
    (triple_box_scalar_lower hu0.le hc.le (D := D) (show 1 ≤ N by omega))
    (by norm_num : (0 : ℝ) ≤ 3/4)
  change k*(2*u)^N/((N : ℝ)+1)^4 ≤ u^(N+1)*
    ∑ n ∈ coreBand u N (dyadicPrimeCount j), max (f n) 0
  calc
    _ ≤ u^(N+1)*((c^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3)*((3/4 : ℝ)*Q)) := by
      calc
        _ = (3/4 : ℝ)*(u*c^3*Real.exp (-(3/2 : ℝ)*D)/24*
            (2*u)^N/((N : ℝ)+1)^4) := by dsimp only [k]; ring
        _ ≤ (3/4 : ℝ)*(u^(N+1)*
            ((c^3*Real.exp (2*(N : ℝ))/((N : ℝ)+1)^3)*Q)) := hscalar
        _ = _ := by ring
    _ ≤ u^(N+1)*((T.card : ℝ)*((3/4 : ℝ)*Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard (by positivity)) (pow_nonneg hu0.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.trans hwhole) (pow_nonneg hu0.le _)

/-- Dropping all positive observations has an UNBOUNDED source-scale
loss on the actual core, at every fixed real height. There is no cofinal
bounded allowance for this information loss. -/
theorem positive_credit_tendsto_atTop {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
        max (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re 0) atTop atTop := by
  obtain ⟨k,hk,hbound⟩ := eventually_positive_credit_growth hu hU y
  have ht := ((geometric_over_successor_four_tendsto (by linarith : 1 < 2*u)).comp
    tendsto_dyadicMomentOrder).const_mul_atTop hk
  apply tendsto_atTop_mono' atTop hbound
  simpa only [Function.comp_def,mul_div_assoc] using ht

/-- The loss from replacing signed observations by their nonpositive
parts is exactly their positive credit, with every original term retained. -/
theorem clipping_loss_eq (A S : Finset ℕ) (u L y : ℝ) (N : ℕ) :
    ((u : ℂ)^(N+1)*∑ n ∈ S,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-
      u^(N+1)*(∑ n ∈ S,
        min (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0) =
    u^(N+1)*∑ n ∈ S,
      max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0 := by
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,← mul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simp only [min_def,max_def]
  split_ifs <;> linarith

/-- This specific loss diverges even on the original cofinal schedule.
It cannot be paid as a fixed or vanishing allowance in the joint floor. -/
theorem clipping_loss_tendsto_atTop {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
      u^(dyadicMomentOrder j+1)*∑ n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j),
        min (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re 0) atTop atTop := by
  apply (positive_credit_tendsto_atTop hu hU y).congr'
  filter_upwards [] with j
  exact (clipping_loss_eq _ _ _ _ _ _).symm

end
end RiemannGaussian.ZetaRieszJointPhaseCredit
