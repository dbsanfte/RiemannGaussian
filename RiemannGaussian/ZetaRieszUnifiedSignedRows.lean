/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerSafeRows

/-!
# One signed ledger for the three independently paid literal populations

The full large-owner population is paid with its actual singleton owner
allocation, rather than charging another nonowner error per label. It is
disjoint from both closed signed divisor-row payments. The remaining real
carrier keeps all smaller-owner unit and unselected divisor incidences
joined. The numerical -79/1000 floor remains open.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszUnifiedSignedRows
open ZetaRieszJointOwnerEnvelope ZetaRieszOwnerSafeRows ZetaRieszFineDivisorRows
open ZetaRieszSaturatedRowFloor ZetaRieszPrimeCountFrequency ZetaRieszSignedConvolution
open ZetaRieszParityPacket ZetaRieszJointAllocation ZetaRieszPrimeEndpoint
open ZetaRieszUnsignedDivisorError

/-- The previously proved actual large-owner label set; all original
core, physical, squarefree, count and nondominant masks remain. -/
def largeOwnerLabels (u : ℝ) (N K : ℕ) : Finset ℕ :=
  literalPopulation (coreBand u N K) (ZetaRieszAnnulusJoint.intermediatePrimes u N) N

/-- The canonical-owner atoms of this original label population, with
the same owner allocation as the retained divisor convolution. -/
def largeOwnerIncidences (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ largeOwnerLabels u N K,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N n *
        zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The large-owner payment is a literal restriction of the SAME
canonical-owner carrier. No cofactor or phase has been completed. -/
theorem coreConvolution_eq_largeOwner_unpaid (u y : ℝ) (N K : ℕ) :
    coreConvolution u y N K = largeOwnerIncidences u y N K+
      ∑ n ∈ coreBand u N K\largeOwnerLabels u N K,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N n *
            zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  have hs : largeOwnerLabels u N K ⊆ coreBand u N K := Finset.filter_subset _ _
  rw [coreConvolution_eq_owner,← Finset.sum_sdiff hs]
  unfold largeOwnerIncidences
  ring

/-- An all-count independent geometric payment of the ORIGINAL singleton
owner sum. The constant is pooled over all labels, not charged per owner. -/
theorem source_scaled_largeOwnerIncidences_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 320 ≤ N)
    (y : ℝ) (K : ℕ) :
    ‖(u : ℂ)^(N+1)*largeOwnerIncidences u y N K‖ ≤ literalErrorBudget N := by
  apply source_scaled_variable_population_bound hu hU hN
    (largeOwnerLabels u N K)
    (fun n => ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
    (SquarefreeVaughanLogSource.length_pos u N) y
  · intro n hn
    obtain ⟨_,hs,hc,hp,hP,hshare⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn,hs,hc,Finset.mem_inter.mpr ⟨hp,by simp⟩,hP,hshare⟩
  · intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2

/-- Actual large-owner atoms decay for any cofinal order schedule, with
no zero assumption or extra nonowner-allocation credit. -/
theorem tendsto_largeOwnerIncidences {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(dyadicMomentOrder j+1)*
      largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => literalErrorBudget (dyadicMomentOrder j)) ?_
    (tendsto_literalErrorBudget.comp tendsto_dyadicMomentOrder)
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (320 : ℕ))]
    with j hj
  exact source_scaled_largeOwnerIncidences_bound hu hU hj y (dyadicPrimeCount j)

private theorem fine_lower_gt_one {u : ℝ} {N : ℕ} (hN : 0 < N) {pb : ℕ×ℕ}
    (hpb : pb ∈ fineRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2)) : 1 < d := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hle : (lower N pb.1 pb.2 : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have h : (1 : ℝ)<d := (one_lt_exp_iff.mpr (by linarith : (0 : ℝ)<N/1000)).trans_le
    ((fine_row_large hpb).trans hle)
  exact_mod_cast h

/-- Even at rounded endpoints, none of the old fine-row credits belongs
to a label whose whole canonical-owner population is paid separately. -/
theorem fine_closed_label_not_largeOwner {u : ℝ} {N K : ℕ} (hN : 0 < N)
    {pb : ℕ×ℕ} (hpb : pb ∈ fineRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors d ≠ 0) :
    pb.1*(pb.2*d) ∉ largeOwnerLabels u N K := by
  intro hn
  have hg := fine_row_geometry hpb
  have hc := closed_row_cofactor_geometry hg hd (fine_lower_gt_one hN hpb hd) hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) hg.1 hc.1.ne_zero hc.2.2
  have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
  have hhigh := (Finset.mem_filter.mp hn).2.2.2.2.1
  rw [ho] at hhigh
  linarith

/-- The new unsaturated closed-row payment is also disjoint from the
whole large-owner population at the original label/incidence level. -/
theorem ownerSafe_closed_label_not_largeOwner {u : ℝ} {N K : ℕ} (hN : 0 < N)
    {pb : ℕ×ℕ} (hpb : pb ∈ ownerSafeRows u N) {d : ℕ}
    (hd : d ∈ Finset.Icc (lower N pb.1 pb.2) (upper N pb.1 pb.2))
    (hs : sieve (pb.1*pb.2).primeFactors d ≠ 0) :
    pb.1*(pb.2*d) ∉ largeOwnerLabels u N K := by
  intro hn
  have hg := ownerSafe_row_geometry hpb
  have hc := closed_row_cofactor_geometry hg hd (ownerSafe_unsigned_gt_one hN hpb hd) hs
  have ho := ZetaRieszPrimeIntervals.largestPrime_mul pb.1 (pb.2*d) hg.1 hc.1.ne_zero hc.2.2
  have hP := (Finset.mem_filter.mp hpb).2.2.2.2.2.2.1
  have hhigh := (Finset.mem_filter.mp hn).2.2.2.2.1
  rw [ho] at hhigh
  linarith

/-- Three disjoint paid populations are removed from the SAME signed
incidence ledger. Unit/small-divisor incidences of the other owners remain. -/
def unifiedRemaining (u y : ℝ) (j : ℕ) : ℝ :=
  ownerSafeRemaining u y j-
    (largeOwnerIncidences u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re

/-- Shared carrier errors occur once, plus each independent population
payment once. No countwise positive allowance has been introduced. -/
def unifiedErrorBudget (y : ℝ) (N : ℕ) : ℝ :=
  ownerSafeErrorBudget y N+literalErrorBudget N

/-- The pooled real-carrier comparison cost is source-o(1). -/
theorem tendsto_unifiedErrorBudget (y : ℝ) :
    Tendsto (unifiedErrorBudget y) atTop (𝓝 0) := by
  change Tendsto (fun N => ownerSafeErrorBudget y N+literalErrorBudget N) atTop (𝓝 0)
  simpa only [zero_add] using (tendsto_ownerSafeErrorBudget y).add tendsto_literalErrorBudget

/-- Whole-carrier signed estimate after all three independent geometric
payments. The remaining scalar is the actual unestimated joint target. -/
theorem eventually_abs_joined_sub_unifiedRemaining_bound {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      |u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          unifiedRemaining u y j)| ≤ unifiedErrorBudget y (dyadicMomentOrder j) := by
  filter_upwards [eventually_abs_joined_sub_ownerSafeRemaining_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (320 : ℕ))] with j hj hN
  have hp := (Complex.abs_re_le_norm
    ((u : ℂ)^(dyadicMomentOrder j+1)*largeOwnerIncidences u y
      (dyadicMomentOrder j) (dyadicPrimeCount j))).trans
        (source_scaled_largeOwnerIncidences_bound (by linarith : 0 ≤ u) hU hN y (dyadicPrimeCount j))
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hp
  rw [unifiedRemaining,show u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        (ownerSafeRemaining u y j-(largeOwnerIncidences u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re)) =
      u^(dyadicMomentOrder j+1)*
        ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
          ownerSafeRemaining u y j)+
      u^(dyadicMomentOrder j+1)*(largeOwnerIncidences u y
        (dyadicMomentOrder j) (dyadicPrimeCount j)).re by ring]
  exact (abs_add_le _ _).trans (add_le_add hj hp)

/-- The current carrier loses no source in joining these three literal
payments. This does not assume an independent floor for the signed rest. -/
theorem tendsto_joined_re_sub_unifiedRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    Tendsto (fun j => u^(dyadicMomentOrder j+1)*
      ((ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re-
        unifiedRemaining u y j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun j => unifiedErrorBudget y (dyadicMomentOrder j)) ?_
    ((tendsto_unifiedErrorBudget y).comp tendsto_dyadicMomentOrder)
  simpa only [Real.norm_eq_abs] using eventually_abs_joined_sub_unifiedRemaining_bound hu hU hy

/-- An unconditional one-sided comparison for the WHOLE joined carrier.
The open numerical floor concerns the joined signed scalar on the left. -/
theorem eventually_joined_floor_with_unifiedRemaining {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 ≤ |y|) :
    ∀ᶠ j in atTop,
      u^(dyadicMomentOrder j+1)*unifiedRemaining u y j-
        unifiedErrorBudget y (dyadicMomentOrder j) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_abs_joined_sub_unifiedRemaining_bound hu hU hy] with j hj
  have h := (abs_le.mp hj).1
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  nlinarith


/-- Every nonzero atom outside the pooled large-owner payment has the
strict remaining owner cut on the ACTUAL dyadic core, even when its
singleton allocation differs from the original full prime allocation. -/
theorem unpaid_owner_cut (j : ℕ) (hj : 32 ≤ j) (u : ℝ) {n : ℕ}
    (hn : n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j)\
      largeOwnerLabels u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hcoeff : residualCoefficient
      (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    log (largestPrime n) < (243/200 : ℝ)*dyadicMomentOrder j := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  obtain ⟨hncore,hnnot⟩ := Finset.mem_sdiff.mp hn
  have hnnarrow := (Finset.mem_filter.mp hncore).1
  have hnnd := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnd).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,hw⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hs : Squarefree n := by
    by_contra hh
    apply hcoeff
    simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hh]
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  by_contra hncut
  have hP : (243/200 : ℝ)*N ≤ log (largestPrime n) := le_of_not_gt hncut
  have hpN : N^2 < largestPrime n := by
    by_contra hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs
      (Nat.dvd_of_mem_primeFactors hp) hcK (by
        intro q hq
        have he : q=largestPrime n := by
          simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
        simpa only [he] using le_of_not_gt hh)
    have hN0 : (0 : ℝ)<N := by
      dsimp [N,dyadicMomentOrder,dyadicPrimeCount]
      positivity
    change log (largestPrime n) ≤ (N : ℝ)/4 at hsmall
    linarith
  have hpX : largestPrime n <
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2 _ hp
  have hpA := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N _).mpr ⟨hpp,hpN,hpX⟩
  have hphi : log (largestPrime n) < (13/20 : ℝ)*log n := by
    by_contra hnphi
    have hn1 : 1 < n := hpp.one_lt.trans_le
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hp))
    have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc3; omega
    exact (Finset.mem_sdiff.mp hnnd).2
      (Finset.mem_filter.mpr ⟨hnret,hs,hn1,hnp,largestPrime n,hp,hpA,
        ZetaRieszDominantAllocation.eligible_of_three_prime_factors hs hc3 hp,le_of_not_gt hnphi⟩)
  exact hnnot (Finset.mem_filter.mpr ⟨hncore,hs,hc3,hpA,hP,hphi.le⟩)

end RiemannGaussian.ZetaRieszUnifiedSignedRows
