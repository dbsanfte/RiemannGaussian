/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalBulkPayment
import RiemannGaussian.ZetaRieszBalancedRadialPayment

/-!
# Spend the completed bulk payment in the literal central ledger

The completed all-count real sum is paid independently. Complete the
actual central population exactly, retaining its ordinary-prime,
semiprime and rejected-composite boundaries together with the SAME head.
No bound on those remaining signed boundaries is assumed or inferred.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalCentralPayment
open ZetaRieszGlobalBulkPayment ZetaRieszPrimeCountFrequency
open ZetaRieszBalancedRadialPayment
open ZetaRieszBalancedOwnerFloor

/-- Restoring primes preserves the original divisor-log majorant. -/
theorem completedCoefficient_norm_le {L : ℝ} (hL : 0<L) (n : ℕ) :
    ‖completedCoefficient L n‖≤zetaMoebiusLogMajorant n := by
  by_cases hp : n.Prime
  · have he := SquarefreeVaughanLogSource.coefficient_eq_completed_with_prime hL n
    have hz : SquarefreeVaughanLogSource.coefficient L n=0 := by
      simp only [SquarefreeVaughanLogSource.coefficient,hp,not_true_eq_false,and_false,if_false]
    change SquarefreeVaughanLogSource.coefficient L n=completedCoefficient L n+_ at he
    rw [hz,if_pos hp] at he
    have hc : completedCoefficient L n=-((log n*min L (log n)/L : ℝ) : ℂ) := by
      linear_combination -he
    have hm : 0 ≤ min L (log n) := le_min hL.le (log_natCast_nonneg n)
    have hn : 0≤log n*min L (log n)/L := by positivity
    rw [hc,norm_neg,Complex.norm_real,Real.norm_of_nonneg hn]
    apply le_trans ?_ (ZetaRieszCentralWindow.log_le_divisor_majorant n)
    apply (div_le_iff₀ hL).mpr
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (log_natCast_nonneg n)
  · have he : completedCoefficient L n=SquarefreeVaughanLogSource.coefficient L n := by
      simp only [completedCoefficient,SquarefreeVaughanLogSource.coefficient,hp,
        not_false_eq_true,and_true]
    rw [he]
    exact SquarefreeVaughanLogSource.norm_coefficient_le hL n

/-- Contract only the two radial strips already paid uniformly for all
divisor-majorized populations. There are no count or physical masks here. -/
def centralFullLabels (N : ℕ) : Finset ℕ :=
  LogarithmicDeviation.deviationBand (fullLabels N) (1971/1000) (2029/1000) N

/-- Completed all-count sum on the contracted physical total-log window. -/
def completedCentral (u y : ℝ) (N : ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈centralFullLabels N,
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n

theorem central_sub_full_norm_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖completedCentral u y N-completedCore u y N‖≤
      ZetaRieszLargeOrderCore.rate^N*radialConstant := by
  have h := (Classical.choose_spec ZetaRieszLargeOrderCore.exists_edge_bound).2
    N (fullLabels N) (completedCoefficient (SquarefreeVaughanLogSource.length u N))
      (fun n _ => completedCoefficient_norm_le (SquarefreeVaughanLogSource.length_pos u N) n)
      y u hu hU
  simpa only [completedCentral,completedCore,centralFullLabels,radialConstant,
    mul_sub,norm_sub_rev] using h

/-- A signed central completed-bulk bound, with both genuine geometric
payments. This is not a norm bound on either prime boundary. -/
theorem completedCentral_real_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {N : ℕ} (hN : 64≤N) :
    |(completedCentral u y N).re|≤bulkBudget u y N+
      ZetaRieszLargeOrderCore.rate^N*radialConstant := by
  have he := Complex.abs_re_le_norm (completedCentral u y N-completedCore u y N)
  have he' : |(completedCentral u y N).re-(completedCore u y N).re|≤
      ‖completedCentral u y N-completedCore u y N‖ := by
    simpa only [Complex.sub_re] using he
  have hh : |(completedCentral u y N).re-(completedCore u y N).re|≤
      ZetaRieszLargeOrderCore.rate^N*radialConstant := by
    exact he'.trans
      (central_sub_full_norm_bound (by linarith : 0≤u) hU y N)
  have hb := completedCore_real_bound hu hU hy hN
  have ht := abs_add_le ((completedCentral u y N).re-(completedCore u y N).re)
    (completedCore u y N).re
  simp only [sub_add_cancel] at ht
  linarith only [ht,hh,hb]

theorem centralLabels_subset_full {u : ℝ} {j : ℕ} :
    centralLabels u j⊆centralFullLabels (dyadicMomentOrder j) := by
  intro n hn
  have hd := mem_centralLabels.mp hn
  have hs : Squarefree n := (Finset.mem_filter.mp (mem_restLabels.mp hd.1).1).2
  have hN : (0 : ℝ)≤dyadicMomentOrder j := Nat.cast_nonneg _
  have hf : n∈fullLabels (dyadicMomentOrder j) := by
    apply (ZetaRieszOwnerLatticePhase.coreFloor_membership _ 0
      (Nat.pos_of_ne_zero hs.ne_zero)).mpr
    simp only [zero_add]
    constructor <;> nlinarith only [hd.2.1,hd.2.2,hN]
  exact Finset.mem_filter.mpr ⟨hf,hd.2⟩

private theorem central_squarefree {u : ℝ} {j n : ℕ} (hn : n∈centralLabels u j) :
    Squarefree n := (Finset.mem_filter.mp (mem_restLabels.mp (mem_centralLabels.mp hn).1).1).2

private theorem central_count {u : ℝ} {j n : ℕ} (hn : n∈centralLabels u j) :
    3≤n.primeFactors.card := by
  exact ZetaRieszJointPrimeEnergy.core_count
    (Finset.mem_filter.mp (mem_restLabels.mp (mem_centralLabels.mp hn).1).1).1

private theorem central_not_prime {u : ℝ} {j n : ℕ} (hn : n∈centralLabels u j) :
    ¬n.Prime := by
  intro hp
  have hc := central_count hn
  simp only [hp.primeFactors,Finset.card_singleton] at hc
  omega

private theorem full_one_lt {N n : ℕ} (hn : n∈centralFullLabels N) : 1<n := by
  have hl := (Finset.mem_filter.mp hn).2.1
  have hN : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hp : 0<log n := by nlinarith only [hl,hN]
  by_contra h
  have hn : n≤1 := by omega
  interval_cases n <;> norm_num at hp

private theorem squarefree_count_one_prime {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card=1) : n.Prime := by
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hc
  have hm : p∈n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hm
  have he := Nat.prod_primeFactors_of_squarefree hs
  rw [hp,Finset.prod_singleton] at he
  simpa only [← he] using hpp

/-- All labels restored by the completion, with original coefficients
and full phases. The low-count sectors are NOT independently paid. -/
def primeLabels (N : ℕ) : Finset ℕ := (centralFullLabels N).filter Nat.Prime

/-- Distinct two-prime labels restored by the global completion. -/
def semiprimeLabels (N : ℕ) : Finset ℕ :=
  (centralFullLabels N).filter (fun n => Squarefree n ∧ n.primeFactors.card=2)

/-- Includes every rejected physical/count/owner mask at counts >=3;
raw high owners retain their original allocation-free coefficient. -/
def rejectedLabels (u : ℝ) (j : ℕ) : Finset ℕ :=
  (centralFullLabels (dyadicMomentOrder j)).filter
    (fun n => Squarefree n ∧ 3≤n.primeFactors.card ∧ n∉centralLabels u j)

/-- Source-scaled completed coefficient on an explicit finite population. -/
def completionTerm (u y : ℝ) (N : ℕ) (S : Finset ℕ) : ℂ :=
  (u : ℂ)^(N+1)*∑ n∈S,completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n

/-- The remaining boundaries stay joined, including the SAME entire
signed head on its original wider radial support. -/
def joinedBoundary (u y : ℝ) (j : ℕ) : ℂ :=
  let N := dyadicMomentOrder j
  completionTerm u y N (primeLabels N)+completionTerm u y N (semiprimeLabels N)+
    completionTerm u y N (rejectedLabels u j)+
      (ZetaRieszRoughPrimePairCancellation.nativeHead u y N : ℂ)

/-- Exact completion of the literal masked central population. Every
discarded count/owner/physical label is charged once, with its sign. -/
theorem completedCentral_eq_native_and_boundaries (u y : ℝ) (j : ℕ) :
    completedCentral u y (dyadicMomentOrder j)=centralRest u y j+
      completionTerm u y (dyadicMomentOrder j) (primeLabels (dyadicMomentOrder j))+
      completionTerm u y (dyadicMomentOrder j) (semiprimeLabels (dyadicMomentOrder j))+
      completionTerm u y (dyadicMomentOrder j) (rejectedLabels u j) := by
  have hsub := centralLabels_subset_full (u:=u) (j:=j)
  have hm : ∀ n∈centralLabels u j,
      SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=
      completedCoefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n := by
    intro n hn
    simp only [SquarefreeVaughanLogSource.coefficient,completedCoefficient,
      central_squarefree hn,central_not_prime hn,not_false_eq_true,and_self,if_true]
  let N := dyadicMomentOrder j
  let f := fun n => completedCoefficient (SquarefreeVaughanLogSource.length u N) n*
    zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hv : (∑ n∈centralLabels u j,SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)=
      ∑ n∈centralFullLabels N,if n∈centralLabels u j then f n else 0 := by
    rw [← Finset.sum_subset (f:=fun n => if n∈centralLabels u j then f n else 0)
      hsub (by intro n _ hn; simp only [if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn,hm n hn]
  have ha : (∑ n∈centralFullLabels N,f n)=
      (∑ n∈centralLabels u j,SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u N) n*zetaPrimeLogKernel N (3/2+Complex.I*y) n)+
      (∑ n∈primeLabels N,f n)+(∑ n∈semiprimeLabels N,f n)+
        ∑ n∈rejectedLabels u j,f n := by
    rw [hv]
    simp only [primeLabels,semiprimeLabels,rejectedLabels,N,Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · have hpos : 0<n.primeFactors.card := Finset.card_pos.mpr
        (Nat.nonempty_primeFactors.mpr (full_one_lt hn))
      by_cases hp : n.Prime
      · have hno : n∉centralLabels u j := fun hm => central_not_prime hm hp
        simp only [hno,hp,hp.primeFactors,Finset.card_singleton,hs,
          show ¬(1 : ℕ)=2 by omega,show ¬(3 : ℕ)≤1 by omega,
          and_false,false_and,if_true,if_false,zero_add,add_zero]
      · by_cases hc : n.primeFactors.card=2
        · have hno : n∉centralLabels u j := by
            intro hm
            have := central_count hm
            omega
          simp [hno,hp,hs,hc]
        · have ht : 3≤n.primeFactors.card := by
            have h1 : n.primeFactors.card≠1 := fun he => hp (squarefree_count_one_prime hs he)
            omega
          by_cases hm : n∈centralLabels u j <;>
            simp only [hm,hp,hs,hc,ht,not_true_eq_false,not_false_eq_true,
              and_true,and_false,if_true,if_false,zero_add,add_zero]
    · have hp : ¬n.Prime := fun hp => hs hp.squarefree
      have hm : n∉centralLabels u j := fun hm => hs (central_squarefree hm)
      simp only [hm,hp,hs,false_and,if_false,add_zero]
      simp only [f,completedCoefficient,if_neg hs,zero_mul]
  unfold completedCentral centralRest completionTerm
  change (u : ℂ)^(N+1)*(∑ n∈centralFullLabels N,f n)=_
  rw [ha]
  simp only [mul_add]
  rfl

/-- The completed bulk is the ONLY term paid here. The entire remaining
completion boundary is still signed and includes the unchanged head. -/
theorem native_joint_eq_completed_sub_boundary (u y : ℝ) (j : ℕ) :
    (centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)=
    (completedCentral u y (dyadicMomentOrder j)).re-(joinedBoundary u y j).re := by
  rw [completedCentral_eq_native_and_boundaries]
  simp only [joinedBoundary,Complex.add_re,Complex.ofReal_re]
  ring

/-- Completed full-window payment and its own paid central-strip error. -/
def centralBulkBudget (u y : ℝ) (j : ℕ) : ℝ :=
  bulkBudget u y (dyadicMomentOrder j)+radialBudget j

theorem centralBulkBudget_tendsto (u y : ℝ) :
    Tendsto (centralBulkBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => bulkBudget u y (dyadicMomentOrder j)+radialBudget j) atTop (𝓝 0)
  have h := ((bulkBudget_tendsto u y).comp tendsto_dyadicMomentOrder).add radialBudget_tendsto
  simpa only [Function.comp_apply,add_zero] using h

/-- Quantitatively pay the global completed bulk INSIDE the exact current
central-main-minus-head ledger. No independent price is assigned to any
restored or rejected population. -/
theorem eventually_native_joint_boundary_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |(centralRest u y j).re-
        ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)+
          (joinedBoundary u y j).re|≤centralBulkBudget u y j := by
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (64 : ℕ))]
    with j hN
  rw [native_joint_eq_completed_sub_boundary,sub_add_cancel]
  exact completedCentral_real_bound hu hU hy hN

theorem tendsto_native_joint_plus_boundary {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|) :
    Tendsto (fun j => (centralRest u y j).re-
      ZetaRieszRoughPrimePairCancellation.nativeHead u y (dyadicMomentOrder j)+
        (joinedBoundary u y j).re) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (centralBulkBudget_tendsto u y)
  filter_upwards [eventually_native_joint_boundary_bound hu hU hy] with j hj
  simpa only [Real.norm_eq_abs] using hj

/-- Spend all existing owner/allocation/radial payments ONCE. The literal
native real carrier is minus the joined completion boundary plus o(1).
The floor still requires an independent upper bound for that boundary. -/
theorem tendsto_native_plus_boundary {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
          (joinedBoundary u y j).re) atTop (𝓝 0) := by
  have h := (tendsto_native_joint_plus_boundary hu.le hU hy).sub
    (tendsto_central_sub_head_sub_native hu hU hy)
  simp only [sub_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- All payments spent once: completed central bulk, the original balanced
radial strip, balanced allocation difference, and allocated high-owner row.
No raw high-owner boundary is paid by the last of these. -/
def nativeBoundaryBudget (u y : ℝ) (j : ℕ) : ℝ :=
  centralBulkBudget u y j+radialBudget j+
    ZetaRieszBalancedAllocationPayment.allocationBudget j+budget u y j

theorem nativeBoundaryBudget_tendsto (u y : ℝ) :
    Tendsto (nativeBoundaryBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => centralBulkBudget u y j+radialBudget j+
    ZetaRieszBalancedAllocationPayment.allocationBudget j+budget u y j) atTop (𝓝 0)
  have h := (((centralBulkBudget_tendsto u y).add radialBudget_tendsto).add
    ZetaRieszBalancedAllocationPayment.allocationBudget_tendsto).add (budget_tendsto u y)
  simpa only [add_zero] using h

/-- A global quantitative signed bound on the literal native carrier
plus its entire completion boundary. Every unestimated boundary remains
in this inequality; there is no zero or phase-approximation premise. -/
theorem eventually_native_boundary_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        (joinedBoundary u y j).re|≤nativeBoundaryBudget u y j := by
  filter_upwards [eventually_native_joint_boundary_bound hu.le hU hy,
    eventually_high_packet_joint_bound hu hU hy] with j hb hh
  have ha := ZetaRieszBalancedAllocationPayment.unallocated_sub_rest_bound
    (by linarith : 0≤u) hU j y
  have hr := central_sub_unallocated_real_bound (by linarith : 0≤u) hU j y
  rw [native_real_eq_rest_high]
  apply abs_le.mpr
  unfold nativeBoundaryBudget
  constructor <;> linarith only [(abs_le.mp hb).1,(abs_le.mp hb).2,
    (abs_le.mp hh).1,(abs_le.mp hh).2,(abs_le.mp ha).1,(abs_le.mp ha).2,
      (abs_le.mp hr).1,(abs_le.mp hr).2]

/-- The precise remaining arithmetic floor target is an UPPER bound on
the JOINED signed boundary, never separate positive prime/mask prices. -/
theorem eventually_native_floor_from_joined_boundary {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -(joinedBoundary u y j).re-nativeBoundaryBudget u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_boundary_bound hu hU hy] with j hj
  linarith only [(abs_le.mp hj).1]

end RiemannGaussian.ZetaRieszGlobalCentralPayment
