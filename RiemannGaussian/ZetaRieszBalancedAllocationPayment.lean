/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedOwnerFloor
import RiemannGaussian.ZetaRieszJointAllocationFloor

/-!
# Pay the allocation correction on the entire balanced remainder

The new owner geometry makes the existing allocation payment applicable to
EVERY remaining label, at every retained prime count. The signed main and
the SAME prime head remain joined. Only their allocation correction is
norm-paid; no norm bound for the main is asserted. The payment is spent in
the actual whole-floor cutoff price, without assuming deletion improves a
clipped cost. The cofinal numerical price bound remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszBalancedAllocationPayment
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint ZetaRieszOwnedCells
open ZetaRieszJointAllocation ZetaRieszOwnerLatticePhase ZetaRieszCutoffPeriodFloor
open ZetaRieszBalancedOwnerFloor

private theorem rest_core {u : ℝ} {j n : ℕ} (hn : n∈restLabels u j) :
    n∈ZetaRieszParityPacket.coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  have h := (Finset.mem_filter.mp (mem_restLabels.mp hn).1).1
  unfold ZetaRieszPaidIncidenceFloor.nativeLabels at h
  rw [ZetaRieszJointCountFloor.coreBand_count_filter _ _ _ _
    (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2] at h
  exact (Finset.mem_filter.mp h).1

/-- The unchanged core window, with no added least-prime or count mask. -/
theorem rest_subset_window (u : ℝ) (j : ℕ) :
    restLabels u j⊆literalWindow (dyadicMomentOrder j) := by
  intro n hn
  have ht := (Finset.mem_filter.mp (rest_core hn)).2
  apply (mem_literalWindow _ _).mpr
  constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (dyadicMomentOrder j)]

/-- All prime legs, not just the owner or a fixed-count subpopulation,
lie strictly inside the already proved allocation-tail geometry. -/
theorem rest_prime_log_le {u : ℝ} {j n p : ℕ} (hn : n∈restLabels u j)
    (hp : p∈n.primeFactors) : log p≤(9/16 : ℝ)*log n := by
  have hN : (0 : ℝ)<dyadicMomentOrder j := by
    unfold dyadicMomentOrder dyadicPrimeCount
    positivity
  have ht := (Finset.mem_filter.mp (rest_core hn)).2.1
  have hln : 0<log n := by linarith only [ht,hN]
  have howner := (div_lt_iff₀ hln).mp (rest_owner_share_lt hn)
  have hmax : p≤largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  have hl : log p≤log (largestPrime n) := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) (by exact_mod_cast hmax)
  linarith only [hl,howner,hln]

/-- The existing independent geometric payment, now for the WHOLE
unpaid population. It is uniform in height and needs no zero hypothesis. -/
def allocationBudget (j : ℕ) : ℝ :=
  (4*ZetaRieszWideOwnerAudit.radiusCeiling)*((dyadicMomentOrder j : ℝ)+1)*
    ZetaRieszParityOrderTail.allocationBoxRate^(dyadicMomentOrder j)*
      zetaMoebiusLogMajorantMass (1+1/262144)

theorem allocationBudget_nonneg (j : ℕ) : 0≤allocationBudget j := by
  unfold allocationBudget
  exact mul_nonneg (mul_nonneg (by unfold ZetaRieszWideOwnerAudit.radiusCeiling; positivity)
    (pow_nonneg ZetaRieszParityOrderTail.allocationBoxRate_bounds.1 _))
      (zetaMoebiusLogMajorantMass_nonneg _)

/-- A certified rational geometric rate, not a floating approximation.
The fixed Dirichlet-mass constant is not asserted numerically small. -/
theorem allocationBudget_le_rational (j : ℕ) :
    allocationBudget j≤
      (4*ZetaRieszWideOwnerAudit.radiusCeiling)*((dyadicMomentOrder j : ℝ)+1)*
        (9991081/10000000 : ℝ)^(dyadicMomentOrder j)*
          zetaMoebiusLogMajorantMass (1+1/262144) := by
  unfold allocationBudget
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ZetaRieszParityOrderTail.allocationBoxRate_bounds.1
        ZetaRieszJointAllocationFloor.allocation_rate_lt.le _)
      (by unfold ZetaRieszWideOwnerAudit.radiusCeiling; positivity))
    (zetaMoebiusLogMajorantMass_nonneg _)

theorem allocationBudget_tendsto : Tendsto allocationBudget atTop (𝓝 0) := by
  exact ZetaRieszJointAllocationFloor.tendsto_allowance.comp tendsto_dyadicMomentOrder

/-- No rectangular selection or count ceiling 39: this estimate pays
all old allocated atoms on ANY subpopulation of the actual remainder. -/
theorem assigned_subset_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ)
    (D : Finset ℕ) (hD : D⊆restLabels u j) :
    ‖(u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈D,
      assignedCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n‖≤allocationBudget j := by
  exact ZetaRieszJointAllocationFloor.norm_scaled_assigned_sum_le _ _
    (SquarefreeVaughanLogSource.length_pos u _) _
    (hD.trans (rest_subset_window u j))
    (fun _ hn _ hp _ _ => rest_prime_log_le (hD hn) hp) y hu hU

/-- The same literal balanced label sum with its allocation correction
paid. The original Riesz coefficient, factorial kernel and phase remain. -/
def unallocatedRest (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈restLabels u j,
    SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
        zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n

private theorem unallocated_sub_residual (u y : ℝ) (j : ℕ) :
    unallocatedRest u y j-
      ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈restLabels u j,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)=
      (u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈restLabels u j,
        assignedCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n := by
  unfold unallocatedRest
  rw [← mul_sub,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simp only [residualCoefficient,assignedCoefficient]
  push_cast
  ring

/-- The payment is a genuine complex norm estimate for the allocation
DIFFERENCE, never for either source-carrying balanced main separately. -/
theorem unallocated_sub_rest_norm_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ) :
    ‖unallocatedRest u y j-
      ((u : ℂ)^(dyadicMomentOrder j+1)*∑ n∈restLabels u j,
        residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u (dyadicMomentOrder j))
          (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
            zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)‖≤allocationBudget j := by
  rw [unallocated_sub_residual]
  exact assigned_subset_bound hu hU j y _ (Finset.Subset.refl _)

theorem unallocated_sub_rest_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ) :
    |(unallocatedRest u y j).re-restPacket u y j|≤allocationBudget j := by
  have hb := unallocated_sub_rest_norm_bound hu hU j y
  exact (Complex.abs_re_le_norm _).trans hb

/-- The balanced ORIGINAL coefficient sum minus the SAME head is
source-equivalent to the whole native carrier. Both payments are arithmetic. -/
theorem tendsto_unallocated_sub_head_sub_native {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j => (unallocatedRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)-
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re)
      atTop (𝓝 0) := by
  have ha : Tendsto (fun j => (unallocatedRest u y j).re-restPacket u y j)
      atTop (𝓝 0) := squeeze_zero_norm (fun j => by
    simpa only [Real.norm_eq_abs] using unallocated_sub_rest_bound (by linarith) hU j y)
      allocationBudget_tendsto
  have ht := ha.add (tendsto_rest_sub_head_sub_native hu hU hy)
  simp only [add_zero] at ht
  exact ht.congr' (Eventually.of_forall fun _ => by ring)

/-- Full signed original weight on the balanced labels. No completion or
absolute majorant replaces the original two-hinge Riesz coefficient. -/
def unallocatedWeight (L u y : ℝ) (N n : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*(-1/L : ℝ)*(log n : ℂ)*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The new whole main increment uses no boundedShare at all. The old
WHOLE tangent/null correction is retained on its unchanged native labels. -/
def step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let X := ZetaRieszPaidIncidenceFloor.nativeEndpoint u j
  let W := ZetaRieszComplexProjection.sourceWeight
    (ZetaRieszAnnulusJoint.intermediatePrimes u N) L u y N
  ZetaRieszComplexNullFloor.increment X N (restLabels u j)
    (unallocatedWeight L u y N) L (ZetaRieszSmallTagNativeFloor.realParameters p) k+
      ZetaRieszTangentCubicCredit.extendedIncrement X N (nativeSF u j) W L q a k

theorem sum_step (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    (∑ k∈Finset.Icc 1 (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j),step u y j p q a k)=
      (unallocatedRest u y j).re := by
  have hs : ∀ n∈nativeSF u j,Squarefree n := fun _ hn => (Finset.mem_filter.mp hn).2
  have hc : ∀ n∈nativeSF u j,3≤n.primeFactors.card := fun _ hn =>
    ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hn).1
  have hX : ∀ n∈nativeSF u j,n≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := fun _ hn =>
    (Finset.le_sup (f:=id) (Finset.mem_filter.mp hn).1).trans (le_max_right _ _)
  have hd : restLabels u j⊆nativeSF u j := Finset.sdiff_subset
  unfold step
  dsimp only
  rw [Finset.sum_add_distrib,ZetaRieszComplexNullFloor.sum_increment_eq _ _ _ _ _
    (fun n hn => hs n (hd hn)) (fun n hn => hc n (hd hn)) (fun n hn => hX n (hd hn)),
      ZetaRieszTangentCubicCredit.sum_extendedIncrement_zero _ _ _ _ _ q a hs hc hX,add_zero]
  simp only [ZetaRieszSmallTagNativeFloor.realParameters,Function.update_self,zero_mul,sub_zero]
  unfold ZetaRieszComplexProjection.complexPrefix unallocatedRest
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [corrected_prefix_eq (hs n (hd hn)) (hc n (hd hn)) (hX n (hd hn))]
  have hnp : ¬n.Prime := by
    intro hp
    have hh := hc n (hd hn)
    simp only [hp.primeFactors,Finset.card_singleton] at hh
    omega
  simp only [unallocatedWeight,SquarefreeVaughanLogSource.coefficient,
    if_pos (And.intro (hs n (hd hn)) hnp)]
  push_cast
  ring

/-- Keep all counts, crossings and the exact signed head joined before
complete-period clipping. Only the allocation correction is paid separately. -/
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

/-- The allocation payment is actually spent in the full floor. No
allocation price, countwise allowance or head norm remains in its main. -/
theorem eventually_joined_floor_paid {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -cost u y j (p j) (q j) (a j)-budget u y j-allocationBudget j-
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
  have ha := unallocated_sub_rest_bound (by linarith : 0≤u) hU j y
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have he := native_real_eq_rest_high u y j
  change Q.re=restPacket u y j+highPacket u y j at he
  change -cost u y j (p j) (q j) (a j)≤(unallocatedRest u y j).re-
    ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j) at hf
  change -cost u y j (p j) (q j) (a j)-budget u y j-allocationBudget j-
    (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,he,hr,(abs_le.mp hb).1,(abs_le.mp ha).2,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Prior whole prices remain alternatives, not overlapping credits.
No monotonicity of signed clipping under allocation removal is assumed. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszBalancedOwnerFloor.price u y j p q a)
    (cost u y j p q a+budget u y j+allocationBudget j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszBalancedOwnerFloor.price u y j p q a := min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_paid hu hU hy p q a,
    ZetaRieszBalancedOwnerFloor.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszBalancedOwnerFloor.price u y j (p j) (q j) (a j))
    (cost u y j (p j) (q j) (a j)+budget u y j+allocationBudget j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

/-- This cofinal numerical bound is still OPEN; the independent
allocation estimate above is not a proof of the main signed price. -/
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

end RiemannGaussian.ZetaRieszBalancedAllocationPayment
