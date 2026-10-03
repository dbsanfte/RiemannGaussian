/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedAllocationPayment
import RiemannGaussian.ZetaRieszLargeOrderCore

/-!
# Spend the paid radial strips on the allocation-free balanced sum

The existing uniform radial estimate applies to the ORIGINAL coefficient
on every remaining balanced label. Spend it before clipping periods,
keeping the same signed prime head and the old whole native free columns.
The main now has neither allocation nor the two outer radial strips.
No estimate of the surviving central signed price is inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszBalancedRadialPayment
open ZetaRieszBalancedOwnerFloor ZetaRieszPrimeCountFrequency
open ZetaRieszPrimeEndpoint ZetaRieszCutoffPeriodFloor
open LogarithmicDeviation

/-- The same native balanced labels, with only the independently paid
radial strips removed. Count, physical and owner masks are unchanged. -/
def centralLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  deviationBand (restLabels u j) (1971/1000) (2029/1000) (dyadicMomentOrder j)

theorem mem_centralLabels {u : ℝ} {j n : ℕ} :
    n∈centralLabels u j ↔ n∈restLabels u j ∧
      (1971/1000 : ℝ)*dyadicMomentOrder j<log n ∧
        log n≤(2029/1000 : ℝ)*dyadicMomentOrder j := by
  simp only [centralLabels,deviationBand,Finset.mem_filter]

theorem centralLabels_subset_rest (u : ℝ) (j : ℕ) :
    centralLabels u j⊆restLabels u j := fun _ hn => (mem_centralLabels.mp hn).1

/-- The stronger lower radial endpoint tightens the largest-prime share
for EVERY surviving count, without a completion or limiting share mask. -/
theorem central_owner_share_lt {u : ℝ} {j n : ℕ} (hn : n∈centralLabels u j) :
    log (largestPrime n)/log n<(340/657 : ℝ) := by
  have hN : (0 : ℝ)<dyadicMomentOrder j := by
    unfold dyadicMomentOrder dyadicPrimeCount
    positivity
  have hd := mem_centralLabels.mp hn
  have hp := (mem_restLabels.mp hd.1).2
  have ht := hd.2.1
  have hlog : 0<log n := by linarith only [ht,hN]
  apply (div_lt_iff₀ hlog).mpr
  nlinarith only [ht,hp]

theorem central_prime_log_lt {u : ℝ} {j n p : ℕ} (hn : n∈centralLabels u j)
    (hp : p∈n.primeFactors) : log p<(340/657 : ℝ)*log n := by
  have ht := (mem_centralLabels.mp hn).2.1
  have hN : (0 : ℝ)<dyadicMomentOrder j := by
    unfold dyadicMomentOrder dyadicPrimeCount
    positivity
  have hlog : 0<log n := by linarith only [ht,hN]
  have hmax : p≤largestPrime n := by
    rw [largestPrime,dif_pos
      (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  have hl := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos : (0 : ℝ)<p)
    (by exact_mod_cast hmax : (p : ℝ)≤largestPrime n)
  exact hl.trans_lt ((div_lt_iff₀ hlog).mp (central_owner_share_lt hn))

/-- Reuse the finite constant from the proved all-mask radial estimate.
This is not a small numerical evaluation of that Dirichlet constant. -/
def radialConstant : ℝ := Classical.choose ZetaRieszLargeOrderCore.exists_edge_bound

theorem radialConstant_nonneg : 0≤radialConstant :=
  (Classical.choose_spec ZetaRieszLargeOrderCore.exists_edge_bound).1

/-- The funded radial difference at the actual native dyadic order. -/
def radialBudget (j : ℕ) : ℝ :=
  ZetaRieszLargeOrderCore.rate^(dyadicMomentOrder j)*radialConstant

theorem radialBudget_nonneg (j : ℕ) : 0≤radialBudget j :=
  mul_nonneg (pow_nonneg ZetaRieszLargeOrderCore.rate_bounds.1.le _)
    radialConstant_nonneg

theorem radialBudget_tendsto : Tendsto radialBudget atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    ZetaRieszLargeOrderCore.rate_bounds.1.le
      ZetaRieszLargeOrderCore.rate_bounds.2).comp tendsto_dyadicMomentOrder).mul_const
        radialConstant
  simp only [zero_mul] at h
  convert h using 1
  ext j
  rfl

/-- Full original coefficient on the literal central labels. -/
def centralRest (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈centralLabels u j,
    SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n

/-- Pay ONLY the two outer strips, at all counts and arbitrary height.
No zero, exposure, completion or signed-cancellation premise occurs. -/
theorem central_sub_unallocated_norm_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ) :
    ‖centralRest u y j-ZetaRieszBalancedAllocationPayment.unallocatedRest u y j‖≤
      radialBudget j := by
  have h := (Classical.choose_spec ZetaRieszLargeOrderCore.exists_edge_bound).2
    (dyadicMomentOrder j) (restLabels u j)
    (SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)))
    (fun n _ => SquarefreeVaughanLogSource.norm_coefficient_le
      (SquarefreeVaughanLogSource.length_pos u _) n) y u hu hU
  simpa only [centralRest,ZetaRieszBalancedAllocationPayment.unallocatedRest,
    centralLabels,radialBudget,radialConstant,mul_sub,norm_sub_rev] using h

theorem central_sub_unallocated_real_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ) :
    |(centralRest u y j).re-
      (ZetaRieszBalancedAllocationPayment.unallocatedRest u y j).re|≤radialBudget j := by
  have h := Complex.abs_re_le_norm
    (centralRest u y j-ZetaRieszBalancedAllocationPayment.unallocatedRest u y j)
  have hh : |(centralRest u y j).re-
      (ZetaRieszBalancedAllocationPayment.unallocatedRest u y j).re|≤
        ‖centralRest u y j-ZetaRieszBalancedAllocationPayment.unallocatedRest u y j‖ := by
    simpa only [Complex.sub_re] using h
  exact hh.trans (central_sub_unallocated_norm_bound hu hU j y)

/-- The SAME head remains signed. The surviving central main-minus-head
is source-equivalent to the whole native real carrier. -/
theorem tendsto_central_sub_head_sub_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => (centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)-
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re)
      atTop (𝓝 0) := by
  have hrad : Tendsto (fun j => (centralRest u y j).re-
      (ZetaRieszBalancedAllocationPayment.unallocatedRest u y j).re) atTop (𝓝 0) :=
    squeeze_zero_norm (fun j => by
      simpa only [Real.norm_eq_abs] using
        central_sub_unallocated_real_bound (by linarith : 0≤u) hU j y) radialBudget_tendsto
  have h := hrad.add
    (ZetaRieszBalancedAllocationPayment.tendsto_unallocated_sub_head_sub_native hu hU hy)
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- Keep the original whole native tangent columns, which are free
exactly. Only the main population is pruned by the radial payment. -/
def step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j
  let W := ZetaRieszComplexProjection.sourceWeight
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
  ZetaRieszComplexNullFloor.increment X N (centralLabels u j)
    (ZetaRieszBalancedAllocationPayment.unallocatedWeight L u y N) L
      (ZetaRieszSmallTagNativeFloor.realParameters p) k+
    ZetaRieszTangentCubicCredit.extendedIncrement X N (nativeSF u j) W L q a k

theorem sum_step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),step u y j p q a k)=
      (centralRest u y j).re := by
  have hs : ∀ n∈nativeSF u j,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n∈nativeSF u j,3≤n.primeFactors.card := fun _ hn =>
    ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n∈nativeSF u j,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ hn =>
    (Finset.le_sup (f:=id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hd : centralLabels u j⊆nativeSF u j :=
    (centralLabels_subset_rest u j).trans Finset.sdiff_subset
  unfold step
  dsimp only
  rw [Finset.sum_add_distrib,ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _
    (fun n hn => hs n (hd hn)) (fun n hn => hc n (hd hn)) (fun n hn => hX n (hd hn)),
      ZetaRieszTangentCubicCredit.sum_extendedIncrement_zero _ _ _ _ _ q a hs hc hX,add_zero]
  simp only [ZetaRieszSmallTagNativeFloor.realParameters,Function.update_self,zero_mul,sub_zero]
  unfold ZetaRieszComplexProjection.complexPrefix centralRest
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [corrected_prefix_eq
    (hs n (hd hn)) (hc n (hd hn)) (hX n (hd hn))]
  have hnp : ¬n.Prime := by
    intro hp
    have hh := hc n (hd hn)
    simp only [hp.primeFactors,Finset.card_singleton] at hh
    omega
  simp only [ZetaRieszBalancedAllocationPayment.unallocatedWeight,
    SquarefreeVaughanLogSource.coefficient,if_pos (And.intro (hs n (hd hn)) hnp)]
  push_cast
  ring

/-- Every retained count and crossing and the SAME full head are joined
BEFORE clipping. No small central cost is assumed. -/
def cost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (ZetaRieszPrimeHeadPeriods.endpoint u j)) (cutoffPeriod y) (fun k =>
    (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then step u y j p q a k else 0)-
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

/-- The radial payment is spent ONCE in the current full carrier floor.
The only new error is geometrically vanishing and independent of zeros. -/
theorem eventually_joined_floor_paid {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -cost u y j (p j) (q j) (a j)-budget u y j-
        ZetaRieszBalancedAllocationPayment.allocationBudget j-radialBudget j-
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
      (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then step u y j (p j) (q j) (a j) k
        else 0)-ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k)
  rw [Finset.sum_sub_distrib,ZetaRieszPrimeHeadPeriods.sum_headIncrement hphysical,
    sum_extend _ _ hnative,sum_step] at hf
  have ha := ZetaRieszBalancedAllocationPayment.unallocated_sub_rest_bound
    (by linarith : 0≤u) hU j y
  have hrad := central_sub_unallocated_real_bound (by linarith : 0≤u) hU j y
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have he := native_real_eq_rest_high u y j
  change Q.re=restPacket u y j+highPacket u y j at he
  change -cost u y j (p j) (q j) (a j)≤(centralRest u y j).re-
    ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) at hf
  change -cost u y j (p j) (q j) (a j)-budget u y j-
    ZetaRieszBalancedAllocationPayment.allocationBudget j-radialBudget j-
      (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,he,hr,(abs_le.mp hb).1,(abs_le.mp ha).2,(abs_le.mp hrad).2,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Deleting a signed population is not assumed to reduce clipped cost.
Keep the two funded whole prices as alternatives, never stacked credits. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszBalancedAllocationPayment.price u y j p q a)
    (cost u y j p q a+budget u y j+
      ZetaRieszBalancedAllocationPayment.allocationBudget j+radialBudget j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszBalancedAllocationPayment.price u y j p q a :=
  min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_paid hu hU hy p q a,
    ZetaRieszBalancedAllocationPayment.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszBalancedAllocationPayment.price u y j (p j) (q j) (a j))
    (cost u y j (p j) (q j) (a j)+budget u y j+
      ZetaRieszBalancedAllocationPayment.allocationBudget j+radialBudget j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

end RiemannGaussian.ZetaRieszBalancedRadialPayment
