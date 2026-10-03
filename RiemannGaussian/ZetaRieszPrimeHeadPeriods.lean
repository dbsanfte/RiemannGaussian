/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughPrimePairCancellation

/-!
# Spend the signed prime head inside the whole cutoff periods

The literal prime-pair head is placed on its exact physical cutoff axis.
Both rough rows and this head are paid jointly before clipping complete
periods. The exact gain is same-sign period overlap minus the negative
head mass. No sign, positive saving or cofinal numerical bound is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPrimeHeadPeriods
open ZetaRieszCutoffPeriodFloor ZetaRieszPrimeCountFrequency
open ZetaRieszRoughPrimePairCancellation (nativeHead)
open ZetaRieszSmallTagNativeFloor (owners)

/-- The actual integer physical cutoff, with no extra rounding. -/
def physicalEndpoint (u : ℝ) (N : ℕ) : ℕ :=
  (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2

/-- Add only zero native increments beyond the original endpoint.
The physical head needs its own complete cutoff endpoint. -/
def endpoint (u : ℝ) (j : ℕ) : ℕ :=
  max (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)
    (physicalEndpoint u (dyadicMomentOrder j))

/-- One prime-owner coefficient with its ENTIRE prime cofactor sum.
The smooth allocation, sieve and full phase remain literal. -/
def headCoefficient (u y : ℝ) (N p : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)/(L*p)*∑ q∈Finset.Ioc
    (ZetaRieszOwnerLatticePhase.coreFloor N (log p) (39/20))
    (ZetaRieszOwnerLatticePhase.coreFloor N (log p) (203/100)),
      if q.Prime then ZetaRieszOwnerLatticePhase.ownerTest N (log p) y q*
        ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) q
      else 0

/-- The original Riesz hinge increment, including its integer edge. -/
def hingeDelta (L : ℝ) (k : ℕ) : ℝ :=
  max 0 (L-log k)-max 0 (L-log (k+1 : ℕ))

/-- The exact prime-head cutoff increment. No cofactor/count is normed. -/
def headIncrement (u y : ℝ) (N k : ℕ) : ℝ :=
  ∑ p∈owners u N,headCoefficient u y N p*
    ((if p≤k then (1 : ℝ) else 0)*hingeDelta (SquarefreeVaughanLogSource.length u N) k)

private theorem prefix_delta {X d : ℕ} (hd : d∈Finset.Icc 1 X)
    (f : ℕ→ℝ) (hend : f (X+1)=0) :
    (∑ k∈Finset.Icc 1 X,(if d≤k then (1 : ℝ) else 0)*(f k-f (k+1)))=f d := by
  have he := ZetaRieszSignedCutoffEnergy.abel_profile X f
    (fun i => if i=d then (1 : ℝ) else 0) hend
  have hs k : (∑ i∈Finset.Icc 1 k,if i=d then (1 : ℝ) else 0)=
      if d≤k then 1 else 0 := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    by_cases h : d≤k
    · simp [h,Finset.mem_Icc,hd0]
    · simp [h,Finset.mem_Icc]
  simp only [hs] at he
  simpa only [mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq',if_pos hd] using he.symm

private theorem length_eq_log (u : ℝ) (N : ℕ) :
    SquarefreeVaughanLogSource.length u N=log (physicalEndpoint u N) := by
  simp only [SquarefreeVaughanLogSource.length,physicalEndpoint,Nat.cast_pow,
    Nat.cast_add,Nat.cast_ofNat]

private theorem owner_bounds {u : ℝ} {N p : ℕ} (hp : p∈owners u N) :
    1≤p ∧ p≤physicalEndpoint u N ∧ log p≤SquarefreeVaughanLogSource.length u N := by
  have hd := ZetaRieszSmallTagNativeFloor.owners_data hp
  have hphys := ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hd.2.1).2.2
  have hlog : log p≤log (physicalEndpoint u N) :=
    log_le_log (by exact_mod_cast hd.1.pos) (by exact_mod_cast hphys.le)
  rw [← length_eq_log] at hlog
  exact ⟨hd.1.one_lt.le,hphys.le,hlog⟩

/-- The cutoff total is exactly the retained signed prime-pair head,
not a positive prime allowance or a vanishing marked two-prime weight. -/
theorem sum_headIncrement {u y : ℝ} {N X : ℕ} (hX : physicalEndpoint u N≤X) :
    (∑ k∈Finset.Icc 1 X,headIncrement u y N k)=nativeHead u y N := by
  let L := SquarefreeVaughanLogSource.length u N
  have hphysical : 0<physicalEndpoint u N := by unfold physicalEndpoint; positivity
  have hlog : L≤log (X+1 : ℕ) := by
    rw [show L=log (physicalEndpoint u N) from length_eq_log u N]
    exact log_le_log (by exact_mod_cast hphysical)
      (by exact_mod_cast (hX.trans (Nat.le_succ X)))
  have hend : max 0 (L-log (X+1 : ℕ))=0 := max_eq_left (by linarith)
  simp only [headIncrement]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he p (hp : p∈owners u N) :
      (∑ k∈Finset.Icc 1 X,(if p≤k then (1 : ℝ) else 0)*hingeDelta L k)=L-log p := by
    have hb := owner_bounds hp
    have hs := prefix_delta (Finset.mem_Icc.mpr ⟨hb.1,hb.2.1.trans hX⟩)
      (fun k => max 0 (L-log k)) hend
    change (∑ k∈Finset.Icc 1 X,(if p≤k then (1 : ℝ) else 0)*hingeDelta L k)=
      max 0 (L-log p) at hs
    rw [max_eq_right (show 0≤L-log p from sub_nonneg.mpr hb.2.2)] at hs
    exact hs
  unfold nativeHead ZetaRieszRoughPrimePairCancellation.head
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [he p hp]
  dsimp [headCoefficient,L]
  ring

/-- The prime correction keeps precisely its one-sided physical hinge
support. This also explains why a base-profile bound alone can miss it. -/
theorem headIncrement_eq_zero {u y : ℝ} {N k : ℕ}
    (hk : 0<k) (hL : SquarefreeVaughanLogSource.length u N≤log k) :
    headIncrement u y N k=0 := by
  have hnext : log k≤log (k+1 : ℕ) := log_le_log
    (by exact_mod_cast hk) (by exact_mod_cast Nat.le_succ k)
  simp only [headIncrement,hingeDelta,max_eq_left (by linarith :
    SquarefreeVaughanLogSource.length u N-log k≤0),max_eq_left (by linarith :
    SquarefreeVaughanLogSource.length u N-log (k+1 : ℕ)≤0),sub_self,mul_zero,
    Finset.sum_const_zero]

/-- The previous remaining main, extended by EXACT zeros only. All
original counts, null directions and free tangent corrections stay joined. -/
def restIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (k : ℕ) : ℝ :=
  if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
    ZetaRieszSmallTagNativeFloor.step u y j p q a k-
      ZetaRieszSmallTagNativeFloor.paidIncrement u y j p k-
        ZetaRieszRoughPrimePairCancellation.paidIncrement u y j p k
  else 0

private theorem sum_extend (X Y : ℕ) (hXY : X≤Y) (t : ℕ→ℝ) :
    (∑ k∈Finset.Icc 1 Y,if k≤X then t k else 0)=∑ k∈Finset.Icc 1 X,t k := by
  have hsub : Finset.Icc 1 X⊆Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  rw [← Finset.sum_subset (f:=fun k => if k≤X then t k else 0) hsub (by
    intro k hk hnot
    have hlo := (Finset.mem_Icc.mp hk).1
    have hx : ¬k≤X := fun hx => hnot (Finset.mem_Icc.mpr ⟨hlo,hx⟩)
    simp only [if_neg hx])]
  exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_Icc.mp hk).2)

private theorem blockCost_extend (X Y : ℕ) (hXY : X≤Y) (g : ℕ→ℕ) (t : ℕ→ℝ) :
    blockCost (Finset.Icc 1 Y) g (fun k => if k≤X then t k else 0)=
      blockCost (Finset.Icc 1 X) g t := by
  have hK : Finset.Icc 1 X⊆Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  have hb b : blockTotal (Finset.Icc 1 Y) g (fun k => if k≤X then t k else 0) b=
      blockTotal (Finset.Icc 1 X) g t b := by
    unfold blockTotal
    have hsub : (Finset.Icc 1 X).filter (fun k => g k=b)⊆
        (Finset.Icc 1 Y).filter (fun k => g k=b) := Finset.filter_subset_filter _ hK
    rw [← Finset.sum_subset (f:=fun k => if k≤X then t k else 0) hsub (by
      intro k hk hn
      obtain ⟨hk,hg⟩ := Finset.mem_filter.mp hk
      have hx : ¬k≤X := fun hx => hn
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,hx⟩,hg⟩)
      simp only [if_neg hx])]
    exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2)
  simp only [blockCost,hb]
  symm
  apply Finset.sum_subset (Finset.image_subset_image hK)
  intro b _ hb
  have hz : blockTotal (Finset.Icc 1 X) g t b=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    obtain ⟨hk,hg⟩ := Finset.mem_filter.mp hk
    exact (hb (Finset.mem_image.mpr ⟨k,hk,hg⟩)).elim
  simp only [hz,neg_zero,max_self]

/-- Join the prime correction with ALL remaining counts and periods
before taking the one-sided cost. No separate sign allowance is used. -/
def cost (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  blockCost (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (fun k =>
    restIncrement u y j p q a k-headIncrement u y (dyadicMomentOrder j) k)

theorem eventually_joined_floor_pruned {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -cost u y j (p j) (q j) (a j)-ZetaRieszRoughPrimePairCancellation.combinedBudget u y j-
        ZetaRieszComplexProjection.nativeError u y j≤
          ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
            (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszRoughPrimePairCancellation.eventually_packet_joint_bound hu hU hy,
    ZetaRieszRoughPrimePairCancellation.eventually_sum_paidIncrement hu hU y,
    ZetaRieszSmallTagNativeFloor.eventually_packet_bound hu hU hy,
    ZetaRieszSmallTagNativeFloor.eventually_sum_paidIncrement hu hU y]
    with j hrough he hsmall hes
  have hf := block_floor (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (fun k =>
    restIncrement u y j (p j) (q j) (a j) k-headIncrement u y (dyadicMomentOrder j) k)
  have hphysical : physicalEndpoint u (dyadicMomentOrder j)≤endpoint u j := le_max_right _ _
  have hnative : ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤endpoint u j := le_max_left _ _
  rw [Finset.sum_sub_distrib,sum_headIncrement hphysical] at hf
  simp only [restIncrement] at hf
  rw [sum_extend _ _ hnative,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ZetaRieszSmallTagNativeFloor.sum_step,he (p j),hes (p j)] at hf
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  change -cost u y j (p j) (q j) (a j)≤Q.re-ZetaRieszSmallTagNativeFloor.packet u y j-
    ZetaRieszRoughPrimePairCancellation.packet u y j-nativeHead u y (dyadicMomentOrder j) at hf
  change -cost u y j (p j) (q j) (a j)-
    (ZetaRieszSmallTagNativeFloor.budget u y j+ZetaRieszRoughPrimePairCancellation.budget u y j)-
      (4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hf,hr,(abs_le.mp hrough).1,(abs_le.mp hsmall).1,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Signed overlap of the two complete period totals. -/
def overlap (K : Finset ℕ) (g : ℕ→ℕ) (t h : ℕ→ℝ) : ℝ :=
  ∑ b∈K.image g,
    (min (max (blockTotal K g t b) 0) (max (blockTotal K g h b) 0)+
      min (max (-blockTotal K g t b) 0) (max (-blockTotal K g h b) 0))

private theorem clipped_difference (x h : ℝ) :
    max (-x) 0+h-max (h-x) 0=
      min (max x 0) (max h 0)+min (max (-x) 0) (max (-h) 0)-max (-h) 0 := by
  simp only [max_def,min_def]
  split_ifs <;> linarith

/-- EXACT global gain, with every adverse crossing retained. Positive
overlap alone is insufficient when some head periods are negative. -/
theorem blockCost_sub_eq (K : Finset ℕ) (g : ℕ→ℕ) (t h : ℕ→ℝ) :
    blockCost K g (fun k => t k-h k)=
      blockCost K g t+(∑ k∈K,h k)-overlap K g t h+blockCost K g h := by
  have hb b : blockTotal K g (fun k => t k-h k) b=
      blockTotal K g t b-blockTotal K g h b := by
    simpa only [blockTotal] using Finset.sum_sub_distrib
      (s:=K.filter (fun k => g k=b)) t h
  have he := Finset.sum_congr (s₁:=K.image g) rfl (fun b _ =>
    clipped_difference (blockTotal K g t b) (blockTotal K g h b))
  simp only [blockCost,hb,overlap,neg_sub,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,sum_blockTotal] at *
  linarith only [he]

/-- The literal prime-head overlap, joined with the entire unpaid main. -/
def nativeOverlap (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  overlap (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
    (restIncrement u y j p q a) (headIncrement u y (dyadicMomentOrder j))

/-- Exact adverse period mass of the signed head. It is subtracted from
the overlap credit, not ignored or placed in a source-small error. -/
def headCost (u y : ℝ) (j : ℕ) : ℝ :=
  blockCost (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
    (headIncrement u y (dyadicMomentOrder j))

theorem cost_eq (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    cost u y j p q a=ZetaRieszRoughPrimePairCancellation.restCost u y j p q a+
      nativeHead u y (dyadicMomentOrder j)-nativeOverlap u y j p q a+headCost u y j := by
  unfold cost nativeOverlap headCost
  have hphysical : physicalEndpoint u (dyadicMomentOrder j)≤endpoint u j := le_max_right _ _
  have hnative : ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤endpoint u j := le_max_left _ _
  rw [blockCost_sub_eq,sum_headIncrement hphysical]
  change blockCost (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
    (fun k => if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
      ZetaRieszSmallTagNativeFloor.step u y j p q a k-
        ZetaRieszSmallTagNativeFloor.paidIncrement u y j p k-
          ZetaRieszRoughPrimePairCancellation.paidIncrement u y j p k else 0)+
      nativeHead u y (dyadicMomentOrder j)-nativeOverlap u y j p q a+headCost u y j=_
  rw [blockCost_extend _ _ hnative]
  rfl

/-- Retain every previously valid floor. The alternative spends the
literal signed prime correction BEFORE period clipping. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszRoughPrimePairCancellation.price u y j p q a)
    (cost u y j p q a+ZetaRieszRoughPrimePairCancellation.combinedBudget u y j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszRoughPrimePairCancellation.price u y j p q a := min_le_left _ _

/-- Quantitative whole-floor improvement over the outside-head price:
exactly the positive part of NET signed overlap, not a guessed credit. -/
theorem price_le_signed_overlap (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszRoughPrimePairCancellation.restCost u y j p q a+
      nativeHead u y (dyadicMomentOrder j)+
        ZetaRieszRoughPrimePairCancellation.combinedBudget u y j-
          max (nativeOverlap u y j p q a-headCost u y j) 0 := by
  have ho : price u y j p q a≤ZetaRieszRoughPrimePairCancellation.restCost u y j p q a+
      nativeHead u y (dyadicMomentOrder j)+
        ZetaRieszRoughPrimePairCancellation.combinedBudget u y j :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hn : price u y j p q a≤cost u y j p q a+
      ZetaRieszRoughPrimePairCancellation.combinedBudget u y j := min_le_right _ _
  rw [cost_eq] at hn
  rcases le_total (nativeOverlap u y j p q a-headCost u y j) 0 with h | h
  · simpa only [max_eq_right h,sub_zero] using ho
  · rw [max_eq_left h]
    linarith only [hn]

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_pruned hu hU hy p q a,
    ZetaRieszRoughPrimePairCancellation.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszRoughPrimePairCancellation.price u y j (p j) (q j) (a j))
    (cost u y j (p j) (q j) (a j)+ZetaRieszRoughPrimePairCancellation.combinedBudget u y j)
    with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

end RiemannGaussian.ZetaRieszPrimeHeadPeriods
