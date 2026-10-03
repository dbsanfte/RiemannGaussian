/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllTagNativeFloor
import RiemannGaussian.ZetaRieszJointOwnerEnvelope

/-!
# Spend all large-owner labels before pricing the balanced remainder

The complete owner-window payment and the independently geometric large-owner
payment are disjoint. Together with the SAME signed prime correction, they
pay every native label with owner logarithm at least `51N/50`. Any additional
labels with zero residual coefficient are removed by their exact zero total,
not by a bound on their cutoff variation. The remaining signed main has only
owners below that threshold. Its whole-floor numerical price is still open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszBalancedOwnerFloor
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint ZetaRieszOwnedCells
open ZetaRieszJointAllocation ZetaRieszOwnerLatticePhase ZetaRieszCutoffPeriodFloor

/-- The unchanged squarefree native core and its count crop. -/
def nativeSF (u : ℝ) (j : ℕ) : Finset ℕ :=
  (ZetaRieszPaidIncidenceFloor.nativeLabels u j).filter Squarefree

/-- Only the geometric owner population NOT already paid by the complete
owner-window theorem. Every other native mask remains in the input set. -/
def upperLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  ZetaRieszJointOwnerEnvelope.literalPopulation
    (nativeSF u j\ZetaRieszAllTagNativeFloor.fullLabels u j)
    (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (dyadicMomentOrder j)

/-- Every owner above the exact lower edge, including zero-response labels. -/
def highLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (nativeSF u j).filter (fun n => (51/50 : ℝ)*dyadicMomentOrder j≤log (largestPrime n))

/-- The precise remaining owner geometry. Counts and phases are unchanged. -/
def restLabels (u : ℝ) (j : ℕ) : Finset ℕ := nativeSF u j\highLabels u j

theorem mem_restLabels {u : ℝ} {j n : ℕ} :
    n∈restLabels u j ↔ n∈nativeSF u j ∧
      log (largestPrime n)<(51/50 : ℝ)*dyadicMomentOrder j := by
  simp only [restLabels,highLabels,Finset.mem_sdiff,Finset.mem_filter]
  by_cases h : n∈nativeSF u j <;> simp [h]

private theorem native_data {u : ℝ} {j n : ℕ}
    (hn : n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j) :
    n∈ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) ∧
      n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j := by
  unfold ZetaRieszPaidIncidenceFloor.nativeLabels at hn
  rw [ZetaRieszJointCountFloor.coreBand_count_filter _ _ _ _
    (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2] at hn
  exact Finset.mem_filter.mp hn

private theorem owner_mem {u : ℝ} {j n : ℕ} (hj : 32≤j)
    (hn : n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j) (hs : Squarefree n)
    (hlo : (51/50 : ℝ)*dyadicMomentOrder j≤log (largestPrime n)) :
    largestPrime n∈ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j) := by
  have hd := native_data hn
  have hnnarrow := (Finset.mem_filter.mp hd.1).1
  have hnnd := (Finset.mem_filter.mp hnnarrow).1
  have hnret := (Finset.mem_sdiff.mp hnnd).1
  have hnS := (Finset.mem_sdiff.mp hnret).1
  obtain ⟨hnfew,_⟩ := Finset.mem_filter.mp hnS
  obtain ⟨hncentral,hc3,hcK⟩ := Finset.mem_filter.mp hnfew
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpN : (dyadicMomentOrder j)^2<largestPrime n := by
    by_contra hh
    have hsmall := ZetaRieszMaskSupport.few_smooth_divisor_log_le j hj hs
      (Nat.dvd_of_mem_primeFactors hp) hcK (by
        intro q hq
        have he : q=largestPrime n := by
          simpa only [hpp.primeFactors,Finset.mem_singleton] using hq
        simpa only [he] using le_of_not_gt hh)
    have hN0 : (0 : ℝ)<dyadicMomentOrder j := by
      unfold dyadicMomentOrder dyadicPrimeCount
      positivity
    change log (largestPrime n)≤(dyadicMomentOrder j : ℝ)/4 at hsmall
    linarith only [hsmall,hlo,hN0]
  have hpX : largestPrime n<
      (ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hncentral).1).1).2 _ hp
  exact (ZetaRieszAnnulusJoint.mem_intermediatePrimes _ _ _).mpr ⟨hpp,hpN,hpX⟩

/-- No cofactor geometry is missing between the proved owner-window edges. -/
private theorem mem_fullLabels_of_owner {u : ℝ} {j n : ℕ}
    (hn : n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j) (hs : Squarefree n)
    (hp : largestPrime n∈ZetaRieszSmallTagNativeFloor.owners u (dyadicMomentOrder j)) :
    n∈ZetaRieszAllTagNativeFloor.fullLabels u j := by
  have hd := native_data hn
  have hc := ZetaRieszJointPrimeEnergy.core_count hd.1
  obtain ⟨hpp,he,has,hac,_⟩ := ZetaRieszJointPrimeEnergy.owner_data hs hc
  have hap : ¬(ownerCofactor n).Prime := by
    intro ha
    simp only [ha.primeFactors,Finset.card_singleton] at hac
    omega
  have hl : log n=log (largestPrime n)+log (ownerCofactor n) := by
    conv_lhs => rw [← he]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast has.ne_zero)]
  have hi : ownerCofactor n∈Finset.Ioc
      (coreFloor (dyadicMomentOrder j) (log (largestPrime n)) (39/20))
      (coreFloor (dyadicMomentOrder j) (log (largestPrime n)) (203/100)) := by
    apply (coreFloor_membership _ _ (Nat.pos_of_ne_zero has.ne_zero)).mpr
    simpa only [← hl] using (Finset.mem_filter.mp hd.1).2
  have hr : (largestPrime n,ownerCofactor n)∈ZetaRieszAllTagNativeFloor.rows u j∪
      ZetaRieszRoughPrimePairCancellation.rows u j :=
    ZetaRieszAllTagNativeFloor.owner_rows_complete.mpr
      ⟨hp,hi,has,hap,by simpa only [he] using hd.2⟩
  rcases Finset.mem_union.mp hr with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,h,he⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,h,he⟩)

/-- The previously unpaid large-owner part has the existing explicit
geometric bound, independently of zeros and of any signed floor premise. -/
theorem eventually_upper_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,
      ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈upperLabels u j,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖≤
        ZetaRieszJointOwnerEnvelope.literalErrorBudget (dyadicMomentOrder j) := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (320 : ℕ))]
    with j hj
  apply ZetaRieszJointOwnerEnvelope.source_scaled_literal_population_bound hu hU hj
    _ _ (SquarefreeVaughanLogSource.length_pos u _) y
  intro n hn
  exact (Finset.mem_filter.mp
    (native_data (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1).1).2.2

/-- Any omitted high-owner label has EXACTLY zero original residual atom.
It may still have large cutoff variation; that variation is not norm-paid. -/
theorem remaining_high_coefficient_eq_zero {u : ℝ} {j n : ℕ} (hj : 32≤j)
    (hn : n∈highLabels u j) (hfull : n∉ZetaRieszAllTagNativeFloor.fullLabels u j)
    (hupp : n∉upperLabels u j) :
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n=0 := by
  obtain ⟨hns,hlo⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnative,hs⟩ := Finset.mem_filter.mp hns
  have hd := native_data hnative
  by_contra hcoeff
  have hnotpop : n∉ZetaRieszJointOwnerEnvelope.literalPopulation
      (ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
      (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j)) (dyadicMomentOrder j) := by
    intro hh
    exact hupp (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hns,hfull⟩,(Finset.mem_filter.mp hh).2⟩)
  have hcut := ZetaRieszJointOwnerEnvelope.literal_rest_owner_cut j hj u
    (Finset.mem_sdiff.mpr ⟨hd.1,hnotpop⟩) hcoeff
  have hpA := owner_mem hj hnative hs hlo
  have hN0 : (0 : ℝ)≤dyadicMomentOrder j := Nat.cast_nonneg _
  have hhi : log (largestPrime n)≤(5/4 : ℝ)*dyadicMomentOrder j := by
    linarith only [hcut,hN0]
  exact hfull (mem_fullLabels_of_owner hnative hs (Finset.mem_filter.mpr ⟨hpA,hlo,hhi⟩))

private theorem fullLabels_owner_lower {u : ℝ} {j n : ℕ}
    (hN : 64≤dyadicMomentOrder j) (hn : n∈ZetaRieszAllTagNativeFloor.fullLabels u j) :
    (51/50 : ℝ)*dyadicMomentOrder j≤log (largestPrime n) := by
  have hrow : ∃ pa : ℕ×ℕ,
      pa∈ZetaRieszAllTagNativeFloor.rows u j∪ZetaRieszRoughPrimePairCancellation.rows u j ∧
        pa.1*pa.2=n := by
    rcases Finset.mem_union.mp hn with h | h
    · obtain ⟨pa,hpa,he⟩ := Finset.mem_image.mp h
      exact ⟨pa,Finset.mem_union_left _ hpa,he⟩
    · obtain ⟨pa,hpa,he⟩ := Finset.mem_image.mp h
      exact ⟨pa,Finset.mem_union_right _ hpa,he⟩
  obtain ⟨pa,hpa,rfl⟩ := hrow
  have hd : pa.1.Prime ∧ Squarefree pa.2 ∧ pa.2<pa.1 ∧
      pa.1∈ZetaRieszSmallTagNativeFloor.owners u (dyadicMomentOrder j) := by
    rcases Finset.mem_union.mp hpa with h | h
    · have hr := ZetaRieszAllTagNativeFloor.rows_data hN h
      exact ⟨hr.1,hr.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1⟩
    · have hr := ZetaRieszRoughPrimePairCancellation.rows_data hN h
      exact ⟨hr.1,hr.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2.1⟩
  have he : largestPrime (pa.1*pa.2)=pa.1 :=
    ZetaRieszPrimeIntervals.largestPrime_mul _ _ hd.1 hd.2.1.ne_zero (fun q hq =>
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.1.ne_zero)
        (Nat.dvd_of_mem_primeFactors hq)).trans_lt hd.2.2.1)
  rw [he]
  exact (ZetaRieszSmallTagNativeFloor.owners_data hd.2.2.2).2.2.1

private theorem upperLabels_subset_highLabels (u : ℝ) (j : ℕ) :
    upperLabels u j⊆highLabels u j := by
  intro n hn
  obtain ⟨hnrest,_,_,_,hlo,_⟩ := Finset.mem_filter.mp hn
  have hN : (0 : ℝ)≤dyadicMomentOrder j := Nat.cast_nonneg _
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hnrest).1,
    by linarith only [hlo,hN]⟩

private theorem full_disjoint_upper (u : ℝ) (j : ℕ) :
    Disjoint (ZetaRieszAllTagNativeFloor.fullLabels u j) (upperLabels u j) := by
  apply Finset.disjoint_left.mpr
  intro n hn hu
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2 hn

/-- The original complex geometric payment, with its literal masks. -/
def upperPacket (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈upperLabels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n

/-- The entire high-owner REAL total. It is paid only jointly with the
old signed head, never as a separate complex norm or absolute head allowance. -/
def highPacket (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈highLabels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

/-- The payments are disjoint; every extra high label has zero total. -/
theorem eventually_highPacket_eq {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ j in atTop,highPacket u y j=
      ZetaRieszAllTagNativeFloor.fullPacket u y j+(upperPacket u y j).re := by
  filter_upwards [ZetaRieszAllTagNativeFloor.eventually_fullLabels_subset_native hu hU,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ)),
    eventually_ge_atTop (32 : ℕ)] with j hj hN h32
  have hs : ZetaRieszAllTagNativeFloor.fullLabels u j∪upperLabels u j⊆highLabels u j := by
    apply Finset.union_subset _ (upperLabels_subset_highLabels u j)
    intro n hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hj.1 hn,hj.2 n hn⟩,fullLabels_owner_lower hN hn⟩
  let f n := residualCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
      zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n
  have he : (∑ n∈ZetaRieszAllTagNativeFloor.fullLabels u j∪upperLabels u j,f n)=
      ∑ n∈highLabels u j,f n := by
    apply Finset.sum_subset hs
    intro n hn hnot
    have hfull : n∉ZetaRieszAllTagNativeFloor.fullLabels u j := fun h =>
      hnot (Finset.mem_union_left _ h)
    have hupp : n∉upperLabels u j := fun h => hnot (Finset.mem_union_right _ h)
    dsimp only [f]
    rw [remaining_high_coefficient_eq_zero h32 hn hfull hupp,zero_mul]
  change (((u : ℂ)^(dyadicMomentOrder j+1)*(∑ n∈highLabels u j,f n)).re)=
    (((u : ℂ)^(dyadicMomentOrder j+1)*
      (∑ n∈ZetaRieszAllTagNativeFloor.fullLabels u j,f n)).re)+
        (((u : ℂ)^(dyadicMomentOrder j+1)*(∑ n∈upperLabels u j,f n)).re)
  rw [← he,Finset.sum_union (full_disjoint_upper u j),mul_add,Complex.add_re]

/-- Both independent errors are explicit and source-small. -/
def budget (u y : ℝ) (j : ℕ) : ℝ :=
  ZetaRieszRoughPrimePairCancellation.combinedBudget u y j+
    ZetaRieszJointOwnerEnvelope.literalErrorBudget (dyadicMomentOrder j)

theorem budget_tendsto (u y : ℝ) : Tendsto (budget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => budget u y j) atTop (𝓝 0)
  simpa only [budget,Function.comp_apply,add_zero] using
    (ZetaRieszRoughPrimePairCancellation.combinedBudget_tendsto u y).add
      (ZetaRieszJointOwnerEnvelope.tendsto_literalErrorBudget.comp tendsto_dyadicMomentOrder)

/-- A new INDEPENDENT signed bound for the whole high-owner population
and the same prime head, including all native cofactor counts/geometries. -/
theorem eventually_high_packet_joint_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |highPacket u y j+ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)|≤
        budget u y j := by
  filter_upwards [eventually_highPacket_eq hu hU y,
    ZetaRieszAllTagNativeFloor.eventually_full_packet_joint_bound hu hU hy,
    eventually_upper_bound (by linarith : 0≤u) hU y] with j he hf hg
  rw [he,add_right_comm]
  have hr : |(upperPacket u y j).re|≤
      ZetaRieszJointOwnerEnvelope.literalErrorBudget (dyadicMomentOrder j) :=
    (Complex.abs_re_le_norm _).trans hg
  exact (abs_add_le _ _).trans (add_le_add hf hr)

theorem tendsto_high_packet_add_head {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => highPacket u y j+
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (budget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_high_packet_joint_bound hu hU hy

/-- All remaining prime shares are below `34/65`, rather than the old
nondominant `13/20` threshold. This is geometry, not a floor estimate. -/
theorem rest_owner_share_lt {u : ℝ} {j n : ℕ} (hn : n∈restLabels u j) :
    log (largestPrime n)/log n<(34/65 : ℝ) := by
  obtain ⟨hns,hp⟩ := mem_restLabels.mp hn
  have hd := native_data (Finset.mem_filter.mp hns).1
  have ht := (Finset.mem_filter.mp hd.1).2.1
  have hN0 : (0 : ℝ)<dyadicMomentOrder j := by
    unfold dyadicMomentOrder dyadicPrimeCount
    positivity
  have hn0 : 0<log n := by linarith only [ht,hN0]
  apply (div_lt_iff₀ hn0).mpr
  linarith only [ht,hp]

/-- The literal balanced part of the real native carrier. The head is
retained separately only so their SIGNED difference can be priced jointly. -/
def restPacket (u y : ℝ) (j : ℕ) : ℝ :=
  ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈restLabels u j,
    residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re

theorem native_real_eq_rest_high (u y : ℝ) (j : ℕ) :
    ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
      (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re=
        restPacket u y j+highPacket u y j := by
  let f n := residualCoefficient
    (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
    (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
      zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n
  have he : (∑ n∈nativeSF u j,f n)=∑ n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j,f n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    have hs : ¬Squarefree n := fun hs => hnot (Finset.mem_filter.mpr ⟨hn,hs⟩)
    simp only [f,residualCoefficient,SquarefreeVaughanLogSource.coefficient,
      hs,false_and,if_false,mul_zero,zero_mul]
  have hh : highLabels u j⊆nativeSF u j := Finset.filter_subset _ _
  change (((u : ℂ)^(dyadicMomentOrder j+1)*
    (∑ n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j,f n)).re)=
      (((u : ℂ)^(dyadicMomentOrder j+1)*(∑ n∈restLabels u j,f n)).re)+
        (((u : ℂ)^(dyadicMomentOrder j+1)*(∑ n∈highLabels u j,f n)).re)
  rw [← he,← Finset.sum_sdiff hh,mul_add,Complex.add_re]
  rfl

/-- The WHOLE remaining signed main minus the head is source-equivalent
to the native carrier, without any zero or exposure hypothesis. Neither
remaining summand has been paid independently. -/
theorem tendsto_rest_sub_head_sub_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => restPacket u y j-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)-
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re)
      atTop (𝓝 0) := by
  have ht := (tendsto_high_packet_add_head hu hU hy).neg
  simp only [neg_zero] at ht
  apply ht.congr'
  filter_upwards [] with j
  rw [native_real_eq_rest_high]
  ring

/-- The whole high-owner population is deleted on the same cutoff axis.
Its total is paid jointly with the signed head; no period is relocated. -/
def highPaidIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  ZetaRieszComplexNullFloor.increment (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)
    N (highLabels u j)
    (ZetaRieszComplexProjection.sourceWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      L u y N) L (ZetaRieszSmallTagNativeFloor.realParameters p) k

theorem sum_highPaidIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) :
    (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),
      highPaidIncrement u y j p k)=highPacket u y j := by
  have hs : ∀ n∈highLabels u j,Squarefree n := fun _ hn =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  have hn : highLabels u j⊆ZetaRieszPaidIncidenceFloor.nativeLabels u j := fun _ hn =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
  have hc : ∀ n∈highLabels u j,3≤n.primeFactors.card := fun _ h =>
    ZetaRieszJointPrimeEnergy.core_count (hn h)
  have hX : ∀ n∈highLabels u j,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ h =>
    (Finset.le_sup (f:=id) (hn h)).trans (le_max_right _ _)
  unfold highPaidIncrement
  dsimp only
  rw [ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _ hs hc hX]
  simp only [ZetaRieszSmallTagNativeFloor.realParameters,Function.update_self,zero_mul,sub_zero]
  unfold ZetaRieszComplexProjection.complexPrefix highPacket
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n h
  rw [corrected_prefix_eq (hs n h) (hc n h) (hX n h)]
  have hnp : ¬n.Prime := by
    intro hp
    have hh := hc n h
    simp only [hp.primeFactors,Finset.card_singleton] at hh
    omega
  simp only [ZetaRieszComplexProjection.sourceWeight,residualCoefficient,
    SquarefreeVaughanLogSource.coefficient,if_pos (And.intro (hs n h) hnp)]
  push_cast
  ring

private theorem increment_sdiff (X N : ℕ) (S D : Finset ℕ) (hD : D⊆S)
    (W : ℕ→ℂ) (L : ℝ) (p : Fin 5→ℝ) (k : ℕ) :
    ZetaRieszComplexNullFloor.increment X N S W L p k-
      ZetaRieszComplexNullFloor.increment X N D W L p k=
        ZetaRieszComplexNullFloor.increment X N (S\D) W L p k := by
  have he w : ZetaRieszCofactorPhaseEnergy.correlation (S\D) w k=
      ZetaRieszCofactorPhaseEnergy.correlation S w k-
        ZetaRieszCofactorPhaseEnergy.correlation D w k := Finset.sum_sdiff_eq_sub hD
  simp only [ZetaRieszComplexNullFloor.increment,he]
  ring

/-- The actual native main now contains ONLY the balanced owner labels.
The whole free null/tangent column stays joined, with no extra credit. -/
theorem step_sub_highPaid (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (k : ℕ) :
    let N := dyadicMomentOrder j
    let L := SquarefreeVaughanLogSource.length u N
    let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j
    let W := ZetaRieszComplexProjection.sourceWeight
      (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
    ZetaRieszSmallTagNativeFloor.step u y j p q a k-highPaidIncrement u y j p k=
      ZetaRieszComplexNullFloor.increment X N (restLabels u j) W L
        (ZetaRieszSmallTagNativeFloor.realParameters p) k+
          ZetaRieszTangentCubicCredit.extendedIncrement X N (nativeSF u j) W L q a k := by
  dsimp only
  have hs : highLabels u j⊆nativeSF u j := Finset.filter_subset _ _
  unfold ZetaRieszSmallTagNativeFloor.step highPaidIncrement
  dsimp only
  simp only [nativeSF,restLabels] at hs ⊢
  rw [add_sub_right_comm,increment_sdiff _ _ _ _ hs]

/-- Price the signed balanced remainder AND the exact prime correction
together over complete periods. Their cancellation remains the open target. -/
def cost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (ZetaRieszPrimeHeadPeriods.endpoint u j)) (cutoffPeriod y) (fun k =>
    (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
      ZetaRieszSmallTagNativeFloor.step u y j p q a k-highPaidIncrement u y j p k else 0)-
        ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k)

private theorem sum_extend (X Y : ℕ) (hXY : X≤Y) (t : ℕ→ℝ) :
    (∑ k∈Finset.Icc 1 Y,if k≤X then t k else 0)=∑ k∈Finset.Icc 1 X,t k := by
  have hsub : Finset.Icc 1 X⊆Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  rw [← Finset.sum_subset (f:=fun k => if k≤X then t k else 0) hsub (by
    intro k hk hnot
    have hlo := (Finset.mem_Icc.mp hk).1
    have hx : ¬k≤X := fun hx => hnot (Finset.mem_Icc.mpr ⟨hlo,hx⟩)
    simp only [if_neg hx])]
  exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_Icc.mp hk).2)

/-- Spend the entire high-owner/head payment ONCE in the actual whole
floor. The only main labels left have owner share below `34/65`. -/
theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -cost u y j (p j) (q j) (a j)-budget u y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_high_packet_joint_bound hu hU hy] with j hb
  have hphysical : ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)≤
      ZetaRieszPrimeHeadPeriods.endpoint u j := le_max_right _ _
  have hnative : ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤
      ZetaRieszPrimeHeadPeriods.endpoint u j := le_max_left _ _
  have hf := block_floor (Finset.Icc 1 (ZetaRieszPrimeHeadPeriods.endpoint u j))
    (cutoffPeriod y) (fun k =>
      (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
        ZetaRieszSmallTagNativeFloor.step u y j (p j) (q j) (a j) k-
          highPaidIncrement u y j (p j) k else 0)-
            ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k)
  rw [Finset.sum_sub_distrib,ZetaRieszPrimeHeadPeriods.sum_headIncrement hphysical,
    sum_extend _ _ hnative,Finset.sum_sub_distrib,
    ZetaRieszSmallTagNativeFloor.sum_step,sum_highPaidIncrement] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  change -cost u y j (p j) (q j) (a j)≤Q.re-highPacket u y j-
    ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) at hf
  change -cost u y j (p j) (q j) (a j)-budget u y j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hr,(abs_le.mp hb).1,abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Alternative entire prices are never stacked as overlapping credits. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszAllTagNativeFloor.price u y j p q a) (cost u y j p q a+budget u y j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszAllTagNativeFloor.price u y j p q a := min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy p q a,
    ZetaRieszAllTagNativeFloor.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszAllTagNativeFloor.price u y j (p j) (q j) (a j))
    (cost u y j (p j) (q j) (a j)+budget u y j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- The remaining whole balanced/head price premise is OPEN. This
conditional endpoint does not prove a zero exclusion by itself. -/
theorem false_of_cofinal_price (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho→
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (hy : 54≤|rho.1.im|) (hsimple : analyticZetaZeroMultiplicity rho=1)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ)
    (hcost : ∃ᶠ j in atTop,
      price (3/2-rho.1.re) rho.1.im j (p j) (q j) (a j)≤399/5000) : False := by
  have hu : 1/2<3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  apply ZetaRieszEndgameSlack.false_of_relaxed_floor rho hrho hexposed hU hsimple
    (ZetaRieszComplexProjection.nativeError (3/2-rho.1.re) rho.1.im)
      (ZetaRieszComplexProjection.tendsto_nativeError rho hrho hexposed hU)
  have hf := eventually_joined_floor hu hU hy p q a
  exact (hcost.and_eventually hf).mono (fun j hj => by
    obtain ⟨hc,hf⟩ := hj
    linarith only [hc,hf])

end RiemannGaussian.ZetaRieszBalancedOwnerFloor
