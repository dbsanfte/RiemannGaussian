/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBalancedRadialPayment
import RiemannGaussian.ZetaRieszQuantitativeNullStep

/-!
# Joint prime-head transport through the exact quadratic divisor orbit

The ordinary-prime correction is NOT zero. Its full signed total is moved
onto the quadratic divisor orbit of the same literal prime pair. The
difference is an exact null direction. Apply its signed crossing credit
only AFTER joining every retained count and complete cutoff period.
No asymptotic estimate of the resulting native price is assumed or proved.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszPrimeHeadTransport
open ZetaRieszPrimeCountFrequency ZetaRieszCutoffPeriodFloor
open ZetaRieszSmallTagNativeFloor (owners owners_data)
open ZetaRieszOwnerLatticePhase (coreFloor)
open ZetaRieszRoughPrimePairCancellation (nativeHead)

/-- The original prime cofactor interval; no radial contraction of the
prime correction accompanies the independently paid main radial strips. -/
def pairInterval (N p : ℕ) : Finset ℕ :=
  Finset.Ioc (coreFloor N (log p) (39/20)) (coreFloor N (log p) (203/100))

/-- A literal signed head pair, including its phase, allocation and sieve. -/
def pairAmount (u y : ℝ) (N p q : ℕ) : ℝ :=
  let L := SquarefreeVaughanLogSource.length u N
  u^(N+1)*(L-log p)/(L*p)*
    (if q.Prime then ZetaRieszOwnerLatticePhase.ownerTest N (log p) y q*
      ZetaRieszUnsignedDivisorError.sieve (ZetaRieszSmallTagNativeFloor.smallPrimes N) q
     else 0)

/-- The exact four divisor incidences of a distinct prime pair. -/
def pairOrbit (p q k : ℕ) : ℝ :=
  (if 1≤k then 1 else 0)-(if p≤k then 1 else 0)-
    (if q≤k then 1 else 0)+(if p*q≤k then 1 else 0)

/-- These four incidences are the literal signed divisor prefix, not
an artificial two-prime completion or a deleted marked-weight surrogate. -/
theorem pairOrbit_eq_divisors {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (k : ℕ) :
    pairOrbit p q k=∑ d∈(p*q).divisors,(μ d : ℝ)*(if d≤k then 1 else 0) := by
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hmu : μ (p*q)=1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp,ArithmeticFunction.moebius_apply_prime hq]
    norm_num
  rw [Nat.divisors_mul,Finset.mul_def,Finset.sum_image hcop.mul_injOn_divisors,
    Finset.sum_product,hp.sum_divisors]
  simp only [hq.sum_divisors,Nat.mul_one,ArithmeticFunction.moebius_apply_one,
    Int.cast_one,ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq,Int.cast_neg,neg_mul,one_mul,hmu]
  unfold pairOrbit
  ring

/-- No truncated or fitted polynomial replaces this exact log-square step. -/
def quadraticDelta (N k : ℕ) : ℝ :=
  (log k^2-log (k+1 : ℕ)^2)/((N : ℝ)+1)

/-- Transport one signed amount, rather than delete its ordinary-prime source. -/
def pairIncrement (N p q : ℕ) (amount : ℝ) (k : ℕ) : ℝ :=
  amount*(((N : ℝ)+1)/(2*log p*log q))*pairOrbit p q k*quadraticDelta N k

private theorem prefix_delta {X d : ℕ} (hd : d∈Finset.Icc 1 X) (f : ℕ→ℝ) :
    (∑ k∈Finset.Icc 1 X,(if d≤k then (1 : ℝ) else 0)*(f k-f (k+1)))=
      f d-f (X+1) := by
  let F := fun k => f k-f (X+1)
  have he := ZetaRieszSignedCutoffEnergy.abel_profile X F
    (fun i => if i=d then (1 : ℝ) else 0) (sub_self _)
  have hs k : (∑ i∈Finset.Icc 1 k,if i=d then (1 : ℝ) else 0)=
      if d≤k then 1 else 0 := by
    have hd0 := (Finset.mem_Icc.mp hd).1
    by_cases h : d≤k
    · simp [h,Finset.mem_Icc,hd0]
    · simp [h,Finset.mem_Icc]
  simp only [hs] at he
  have hdiff k : F k-F (k+1)=f k-f (k+1) := by dsimp [F]; ring
  simp only [hdiff,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',if_pos hd] at he
  simpa only [ite_mul,one_mul,zero_mul,F] using he.symm

/-- The signed quadratic orbit has exactly its semiprime divisor moment.
The terminal boundary cancels; it is not silently set to zero. -/
theorem sum_pairOrbit_quadratic {p q X : ℕ} (hp : 1<p) (hq : 1<q)
    (hX : p*q≤X) (N : ℕ) :
    (∑ k∈Finset.Icc 1 X,pairOrbit p q k*quadraticDelta N k)=
      2*log p*log q/((N : ℝ)+1) := by
  have hpq : 1≤p*q := by nlinarith
  have hpX : p≤X := (Nat.le_mul_of_pos_right p (by omega)).trans hX
  have hqX : q≤X := (Nat.le_mul_of_pos_left q (by omega)).trans hX
  have h1 := prefix_delta (Finset.mem_Icc.mpr ⟨le_refl 1,hpq.trans hX⟩)
    (fun k => log k^2/((N : ℝ)+1))
  have h2 := prefix_delta (Finset.mem_Icc.mpr ⟨(by omega : 1≤p),hpX⟩)
    (fun k => log k^2/((N : ℝ)+1))
  have h3 := prefix_delta (Finset.mem_Icc.mpr ⟨(by omega : 1≤q),hqX⟩)
    (fun k => log k^2/((N : ℝ)+1))
  have h4 := prefix_delta (Finset.mem_Icc.mpr ⟨hpq,hX⟩)
    (fun k => log k^2/((N : ℝ)+1))
  have hd k : quadraticDelta N k=
      log k^2/((N : ℝ)+1)-log (k+1 : ℕ)^2/((N : ℝ)+1) := by
    unfold quadraticDelta
    ring
  simp only [pairOrbit,hd,add_mul,sub_mul,Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [h1,h2,h3,h4]
  have hp0 : (p : ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hq0 : (q : ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
  simp only [Nat.cast_one,log_one,zero_pow (by decide : 2≠0),zero_div,
    Nat.cast_mul,log_mul hp0 hq0]
  ring

/-- Every transported pair keeps its exact signed correction amount. -/
theorem sum_pairIncrement {p q X : ℕ} (hp : 1<p) (hq : 1<q)
    (hX : p*q≤X) (N : ℕ) (amount : ℝ) :
    (∑ k∈Finset.Icc 1 X,pairIncrement N p q amount k)=amount := by
  have hpL : 0<log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hqL : 0<log (q : ℝ) := log_pos (by exact_mod_cast hq)
  simp only [pairIncrement,mul_assoc,← Finset.mul_sum]
  rw [sum_pairOrbit_quadratic hp hq hX N]
  have hN : (N : ℝ)+1≠0 := by positivity
  field_simp

/-- Join all head pairs before changing any cutoff profile. -/
theorem nativeHead_eq_sum_pairAmount (u y : ℝ) (N : ℕ) :
    nativeHead u y N=∑ p∈owners u N,∑ q∈pairInterval N p,pairAmount u y N p q := by
  unfold nativeHead ZetaRieszRoughPrimePairCancellation.head
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [pairInterval,pairAmount,← Finset.mul_sum]
  ring

/-- The pair labels can extend beyond the old cutoff endpoint. Pay that
bookkeeping exactly by enlarging the endpoint, never dropping its edge. -/
def pairEndpoint (u : ℝ) (N : ℕ) : ℕ :=
  (owners u N).sup (fun p => p*coreFloor N (log p) (203/100))

/-- A common complete cutoff axis containing the old carrier and every
literal head-pair product. The old increments on its extension are zero. -/
def endpoint (u : ℝ) (j : ℕ) : ℕ :=
  max (ZetaRieszPrimeHeadPeriods.endpoint u j) (pairEndpoint u (dyadicMomentOrder j))

/-- The full signed correction on its quadratic divisor axis, with all
ordinary prime pairs and all original masks retained. -/
def quadraticHead (u y : ℝ) (N k : ℕ) : ℝ :=
  ∑ p∈owners u N,∑ q∈pairInterval N p,
    pairIncrement N p q (pairAmount u y N p q) k

/-- This is the SAME head. Its nonzero source is never norm-paid away. -/
theorem sum_quadraticHead {u y : ℝ} {N X : ℕ} (hX : pairEndpoint u N≤X) :
    (∑ k∈Finset.Icc 1 X,quadraticHead u y N k)=nativeHead u y N := by
  simp only [quadraticHead]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=Finset.Icc 1 X)]
  rw [nativeHead_eq_sum_pairAmount]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqp : q.Prime
  · have hpX : p*coreFloor N (log p) (203/100)≤pairEndpoint u N :=
      Finset.le_sup (f:=fun p : ℕ => p*coreFloor N (log p) (203/100)) hp
    have hqX : q≤coreFloor N (log p) (203/100) := (Finset.mem_Ioc.mp hq).2
    have hprod : p*q≤X := (Nat.mul_le_mul_left p hqX).trans (hpX.trans hX)
    exact sum_pairIncrement (owners_data hp).1.one_lt hqp.one_lt hprod N _
  · simp only [pairAmount,if_neg hqp,mul_zero,pairIncrement,zero_mul,Finset.sum_const_zero]

/-- The prime-head profile move is an exact zero-total direction. -/
def direction (u y : ℝ) (j k : ℕ) : ℝ :=
  ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k-
    quadraticHead u y (dyadicMomentOrder j) k

theorem sum_direction (u y : ℝ) (j : ℕ) :
    (∑ k∈Finset.Icc 1 (endpoint u j),direction u y j k)=0 := by
  have hp : ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)≤endpoint u j :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hpair : pairEndpoint u (dyadicMomentOrder j)≤endpoint u j := le_max_right _ _
  simp only [direction,Finset.sum_sub_distrib]
  rw [ZetaRieszPrimeHeadPeriods.sum_headIncrement hp,sum_quadraticHead hpair,sub_self]

/-- Literal head pairs have a unique larger owner. No pair-incidence
average or additional owner mask is used by the transport. -/
theorem pair_cofactor_lt_owner {u : ℝ} {N p q : ℕ} (hN : 64≤N)
    (hp : p∈owners u N) (hq : q∈pairInterval N p) : q<p := by
  have hd := owners_data hp
  exact (Finset.mem_Ioc.mp hq).2.trans_lt
    (ZetaRieszTaggedCoreWindow.full_core_owner_geometry hN hd.1 hd.2.2.1 hd.2.2.2).1

theorem native_pairOrbit_eq_divisors {u : ℝ} {N p q : ℕ} (hN : 64≤N)
    (hp : p∈owners u N) (hq : q∈pairInterval N p) (hqp : q.Prime) (k : ℕ) :
    pairOrbit p q k=∑ d∈(p*q).divisors,(μ d : ℝ)*(if d≤k then 1 else 0) :=
  pairOrbit_eq_divisors (owners_data hp).1 hqp
    (ne_of_gt (pair_cofactor_lt_owner hN hp hq)) k

/-- The literal central main and the SAME head, including all prior
whole native free directions. Only exact zeros extend the main endpoint. -/
def joinedIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (k : ℕ) : ℝ :=
  (if k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j then
    ZetaRieszBalancedRadialPayment.step u y j p q a k else 0)-
      ZetaRieszPrimeHeadPeriods.headIncrement u y (dyadicMomentOrder j) k

private theorem sum_extend (X Y : ℕ) (hXY : X≤Y) (t : ℕ→ℝ) :
    (∑ k∈Finset.Icc 1 Y,if k≤X then t k else 0)=∑ k∈Finset.Icc 1 X,t k := by
  have hsub : Finset.Icc 1 X⊆Finset.Icc 1 Y := Finset.Icc_subset_Icc_right hXY
  rw [← Finset.sum_subset (f:=fun k => if k≤X then t k else 0) hsub (by
    intro k hk hn
    have hlo := (Finset.mem_Icc.mp hk).1
    have hx : ¬k≤X := fun hx => hn (Finset.mem_Icc.mpr ⟨hlo,hx⟩)
    simp only [if_neg hx])]
  exact Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_Icc.mp hk).2)

theorem sum_joinedIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    (∑ k∈Finset.Icc 1 (endpoint u j),joinedIncrement u y j p q a k)=
      (ZetaRieszBalancedRadialPayment.centralRest u y j).re-
        nativeHead u y (dyadicMomentOrder j) := by
  have hn : ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤endpoint u j :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hp : ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)≤endpoint u j :=
    (le_max_right _ _).trans (le_max_left _ _)
  simp only [joinedIncrement,Finset.sum_sub_distrib]
  rw [sum_extend _ _ hn,ZetaRieszBalancedRadialPayment.sum_step,
    ZetaRieszPrimeHeadPeriods.sum_headIncrement hp]

/-- The enlarged endpoint introduces no new original cost. All added
head increments are literally zero, not charged by a positive allowance. -/
theorem joinedIncrement_eq_zero {u y : ℝ} {j k : ℕ}
    (hk : ZetaRieszPrimeHeadPeriods.endpoint u j<k) :
    ∀ (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ),joinedIncrement u y j p q a k=0 := by
  intro p q a
  have hn : ¬k≤ZetaRieszPaidIncidenceFloor.nativeEndpoint u j := by
    have h := le_max_left (ZetaRieszPaidIncidenceFloor.nativeEndpoint u j)
      (ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j))
    change ZetaRieszPaidIncidenceFloor.nativeEndpoint u j≤
      ZetaRieszPrimeHeadPeriods.endpoint u j at h
    omega
  have hphys : ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)≤k :=
    (le_max_right _ _).trans hk.le
  have hphysical : 0<ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j) := by
    unfold ZetaRieszPrimeHeadPeriods.physicalEndpoint
    positivity
  have hk0 : 0<k := hphysical.trans_le hphys
  have hL : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)≤log k := by
    have he : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)=
        log (ZetaRieszPrimeHeadPeriods.physicalEndpoint u (dyadicMomentOrder j)) := by
      simp only [SquarefreeVaughanLogSource.length,ZetaRieszPrimeHeadPeriods.physicalEndpoint,
        Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
    rw [he]
    exact log_le_log (by exact_mod_cast hphysical) (by exact_mod_cast hphys)
  simp only [joinedIncrement,if_neg hn,
    ZetaRieszPrimeHeadPeriods.headIncrement_eq_zero hk0 hL,sub_self]

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

/-- Same old central whole-period cost on the extended common endpoint. -/
theorem blockCost_joinedIncrement (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ)
    (q : Fin 6→ℝ) (a : ℝ) :
    blockCost (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
      (joinedIncrement u y j p q a)=ZetaRieszBalancedRadialPayment.cost u y j p q a := by
  have he : joinedIncrement u y j p q a=fun k =>
      if k≤ZetaRieszPrimeHeadPeriods.endpoint u j then joinedIncrement u y j p q a k else 0 := by
    funext k
    by_cases hk : k≤ZetaRieszPrimeHeadPeriods.endpoint u j
    · simp only [if_pos hk]
    · simp only [if_neg hk,joinedIncrement_eq_zero (lt_of_not_ge hk)]
  have hXY : ZetaRieszPrimeHeadPeriods.endpoint u j≤endpoint u j := le_max_left _ _
  rw [he,blockCost_extend _ _ hXY]
  rfl

/-- Choose the better of BOTH exact signed orientations, after charging
every original zero group and every crossed group. No fixed-count debit. -/
def gain (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  let K := Finset.Icc 1 (endpoint u j)
  let g := cutoffPeriod y
  let t := joinedIncrement u y j p q a
  max (ZetaRieszQuantitativeNullStep.guaranteedGain K g t (direction u y j))
    (ZetaRieszQuantitativeNullStep.guaranteedGain K g t (fun k => -direction u y j k))

theorem gain_nonneg (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    0≤gain u y j p q a := by
  exact (ZetaRieszQuantitativeNullStep.guaranteedGain_nonneg _ _ _ _).trans (le_max_left _ _)

/-- A direct signed arithmetic inequality for the WHOLE central sum
minus its same prime correction. The new credit is spent in that floor. -/
theorem central_floor_with_gain (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ)
    (q : Fin 6→ℝ) (a : ℝ) :
    -ZetaRieszBalancedRadialPayment.cost u y j p q a+gain u y j p q a≤
      (ZetaRieszBalancedRadialPayment.centralRest u y j).re-
        nativeHead u y (dyadicMomentOrder j) := by
  have hpos := ZetaRieszQuantitativeNullStep.floor_with_guaranteed_gain
    (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
      (direction u y j) (sum_direction u y j)
  have hnull : (∑ k∈Finset.Icc 1 (endpoint u j),-direction u y j k)=0 := by
    rw [Finset.sum_neg_distrib,sum_direction,neg_zero]
  have hneg := ZetaRieszQuantitativeNullStep.floor_with_guaranteed_gain
    (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
      (fun k => -direction u y j k) hnull
  rw [blockCost_joinedIncrement,sum_joinedIncrement] at hpos hneg
  unfold gain
  dsimp only
  rcases le_total
    (ZetaRieszQuantitativeNullStep.guaranteedGain _ _ _ (direction u y j))
    (ZetaRieszQuantitativeNullStep.guaranteedGain _ _ _ (fun k => -direction u y j k)) with h | h
  · rw [max_eq_right h]
    exact hneg
  · rw [max_eq_left h]
    exact hpos

/-- Move the head and the existing free main profiles TOGETHER. A single
signed direction carries both changes; zero-face costs are computed only
after they have been added. The whole native tangent columns are retained. -/
def coupledDirection (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) (k : ℕ) : ℝ :=
  joinedIncrement u y j r q a k-joinedIncrement u y j p q a k+b*direction u y j k

theorem sum_coupledDirection (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) :
    (∑ k∈Finset.Icc 1 (endpoint u j),coupledDirection u y j p q a r b k)=0 := by
  simp only [coupledDirection,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [sum_joinedIncrement,sum_joinedIncrement,sum_direction]
  ring

/-- Exact finite-step savings, with NO inverse-margin upper estimate.
All original zero faces and adverse crossings stay in crossingCost. -/
def coupledCredit (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ)
    (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) : ℝ :=
  let K := Finset.Icc 1 (endpoint u j)
  let g := cutoffPeriod y
  let t := joinedIncrement u y j p q a
  let v := coupledDirection u y j p q a r b
  max (ZetaRieszSignedNullGain.adverseCorrelation K g t v-
    ZetaRieszSignedNullGain.crossingCost K g t v 1) 0

theorem coupledCredit_nonneg (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ)
    (q : Fin 6→ℝ) (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) :
    0≤coupledCredit u y j p q a r b := le_max_right _ _

/-- The credit is EXACTLY the positive cost reduction of the entire
coupled update. No periodwise or countwise fitted coefficient is allowed. -/
theorem coupledCredit_eq_cost_saving (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ)
    (q : Fin 6→ℝ) (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) :
    coupledCredit u y j p q a r b=
      max (ZetaRieszBalancedRadialPayment.cost u y j p q a-
        blockCost (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
          (fun k => joinedIncrement u y j r q a k+b*direction u y j k)) 0 := by
  have h := ZetaRieszSignedNullGain.blockCost_shift_eq
    (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
      (coupledDirection u y j p q a r b) 1
  have he k : joinedIncrement u y j p q a k+1*coupledDirection u y j p q a r b k=
      joinedIncrement u y j r q a k+b*direction u y j k := by
    unfold coupledDirection
    ring
  simp_rw [he] at h
  rw [blockCost_joinedIncrement,one_mul] at h
  unfold coupledCredit
  dsimp only
  congr 1
  linarith only [h]

/-- Direct one-sided inequality after cancelling the marked-prime
correction jointly with the free main profiles and all retained counts. -/
theorem central_floor_with_coupled_credit (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ)
    (q : Fin 6→ℝ) (a : ℝ) (r : Fin 5→ℝ) (b : ℝ) :
    -ZetaRieszBalancedRadialPayment.cost u y j p q a+coupledCredit u y j p q a r b≤
      (ZetaRieszBalancedRadialPayment.centralRest u y j).re-
        nativeHead u y (dyadicMomentOrder j) := by
  have hnull := sum_coupledDirection u y j p q a r b
  have hold := block_floor (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y)
    (joinedIncrement u y j p q a)
  have hnew := ZetaRieszSignedNullGain.floor_with_null_gain
    (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
      (coupledDirection u y j p q a r b) 1 hnull
  rw [blockCost_joinedIncrement,sum_joinedIncrement] at hold hnew
  rw [one_mul] at hnew
  unfold coupledCredit
  dsimp only
  by_cases h : ZetaRieszSignedNullGain.adverseCorrelation
      (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
        (coupledDirection u y j p q a r b)-ZetaRieszSignedNullGain.crossingCost
          (Finset.Icc 1 (endpoint u j)) (cutoffPeriod y) (joinedIncrement u y j p q a)
            (coupledDirection u y j p q a r b) 1≤0
  · rw [max_eq_right h,add_zero]
    exact hold
  · rw [max_eq_left (le_of_not_ge h)]
    linarith only [hnew]

private theorem transfer_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (B : ℕ→ℝ) (hf : ∀ j,-B j≤(ZetaRieszBalancedRadialPayment.centralRest u y j).re-
      nativeHead u y (dyadicMomentOrder j)) :
    ∀ᶠ j in atTop,
      -B j-ZetaRieszBalancedOwnerFloor.budget u y j-
          ZetaRieszBalancedAllocationPayment.allocationBudget j-
            ZetaRieszBalancedRadialPayment.radialBudget j-
              ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [ZetaRieszBalancedOwnerFloor.eventually_high_packet_joint_bound hu hU hy]
    with j hb
  have hfloor := hf j
  have ha := ZetaRieszBalancedAllocationPayment.unallocated_sub_rest_bound
    (by linarith : 0≤u) hU j y
  have hrad := ZetaRieszBalancedRadialPayment.central_sub_unallocated_real_bound
    (by linarith : 0≤u) hU j y
  let P := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
    (dyadicMomentOrder j) (dyadicPrimeCount j)
  let Q := (u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
    (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)
  have hr : Q.re-P.re≤‖Q-P‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (Q-P)
  have he := ZetaRieszBalancedOwnerFloor.native_real_eq_rest_high u y j
  change Q.re=ZetaRieszBalancedOwnerFloor.restPacket u y j+
    ZetaRieszBalancedOwnerFloor.highPacket u y j at he
  change -B j-ZetaRieszBalancedOwnerFloor.budget u y j-
      ZetaRieszBalancedAllocationPayment.allocationBudget j-
        ZetaRieszBalancedRadialPayment.radialBudget j-(4*|P.im|+5*‖Q-P‖)≤P.re
  linarith only [hfloor,he,hr,(abs_le.mp hb).1,(abs_le.mp ha).2,(abs_le.mp hrad).2,
    abs_nonneg P.im,norm_nonneg (Q-P)]

/-- Spend the mathematically defined crossing-square credit in the
literal endgame, with every independently paid difference retained. -/
theorem eventually_joined_floor_with_gain {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -ZetaRieszBalancedRadialPayment.cost u y j (p j) (q j) (a j)+gain u y j (p j) (q j) (a j)-
        ZetaRieszBalancedOwnerFloor.budget u y j-
          ZetaRieszBalancedAllocationPayment.allocationBudget j-
            ZetaRieszBalancedRadialPayment.radialBudget j-
              ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have h := transfer_floor hu hU hy
    (fun j => ZetaRieszBalancedRadialPayment.cost u y j (p j) (q j) (a j)-gain u y j (p j) (q j) (a j))
    (fun j => by linarith only [central_floor_with_gain u y j (p j) (q j) (a j)])
  exact h.mono (fun j hj => by linarith only [hj])

/-- The SAME endgame with the stronger exact coupled finite-step credit.
Its arithmetic size is explicit and OPEN, never put into an error term. -/
theorem eventually_joined_floor_coupled {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ)
    (r : ℕ→Fin 5→ℝ) (b : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -ZetaRieszBalancedRadialPayment.cost u y j (p j) (q j) (a j)+
        coupledCredit u y j (p j) (q j) (a j) (r j) (b j)-
          ZetaRieszBalancedOwnerFloor.budget u y j-
            ZetaRieszBalancedAllocationPayment.allocationBudget j-
              ZetaRieszBalancedRadialPayment.radialBudget j-
                ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have h := transfer_floor hu hU hy
    (fun j => ZetaRieszBalancedRadialPayment.cost u y j (p j) (q j) (a j)-
      coupledCredit u y j (p j) (q j) (a j) (r j) (b j))
    (fun j => by linarith only [central_floor_with_coupled_credit u y j (p j) (q j) (a j) (r j) (b j)])
  exact h.mono (fun j hj => by linarith only [hj])

/-- Preserve all older funded prices as alternatives, not stacked credits. -/
def price (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) : ℝ :=
  min (ZetaRieszBalancedRadialPayment.price u y j p q a)
    (ZetaRieszBalancedRadialPayment.cost u y j p q a-gain u y j p q a+
      ZetaRieszBalancedOwnerFloor.budget u y j+
        ZetaRieszBalancedAllocationPayment.allocationBudget j+
          ZetaRieszBalancedRadialPayment.radialBudget j)

theorem price_le_previous (u y : ℝ) (j : ℕ) (p : Fin 5→ℝ) (q : Fin 6→ℝ) (a : ℝ) :
    price u y j p q a≤ZetaRieszBalancedRadialPayment.price u y j p q a := min_le_left _ _

theorem eventually_joined_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|)
    (p : ℕ→Fin 5→ℝ) (q : ℕ→Fin 6→ℝ) (a : ℕ→ℝ) :
    ∀ᶠ j in atTop,
      -price u y j (p j) (q j) (a j)-ZetaRieszComplexProjection.nativeError u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszGammaJoint.joinedPhysical u y
          (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  filter_upwards [eventually_joined_floor_with_gain hu hU hy p q a,
    ZetaRieszBalancedRadialPayment.eventually_joined_floor hu hU hy p q a]
    with j hnew hold
  unfold price
  rcases le_total (ZetaRieszBalancedRadialPayment.price u y j (p j) (q j) (a j))
    (ZetaRieszBalancedRadialPayment.cost u y j (p j) (q j) (a j)-gain u y j (p j) (q j) (a j)+
      ZetaRieszBalancedOwnerFloor.budget u y j+
        ZetaRieszBalancedAllocationPayment.allocationBudget j+
          ZetaRieszBalancedRadialPayment.radialBudget j) with h | h
  · rw [min_eq_left h]
    exact hold
  · rw [min_eq_right h]
    linarith only [hnew]

end RiemannGaussian.ZetaRieszPrimeHeadTransport
