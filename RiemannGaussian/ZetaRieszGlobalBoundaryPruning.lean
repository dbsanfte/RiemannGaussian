/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalCentralPayment

/-!
# Pay all balanced completion-mask failures together

Below the native count ceiling, every nonzero balanced central squarefree
label satisfies the original masks. A physical-cutoff failure is exactly
zero at counts >=3. The remaining balanced failures have high count and
are paid by the existing uniform full-population geometric bound.

The entire remaining completion boundary therefore contains only ordinary
primes, semiprimes, raw high owners and the SAME head. Those signed terms
stay joined and are not claimed small.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalBoundaryPruning
open ZetaRieszGlobalBulkPayment ZetaRieszGlobalCentralPayment
open ZetaRieszBalancedRadialPayment ZetaRieszBalancedOwnerFloor
open ZetaRieszPrimeCountFrequency ZetaRieszOwnedCells
open ZetaRieszPrimeEndpoint
open ZetaRieszJointAllocation

private theorem central_log {N n : ℕ} (hn : n∈centralFullLabels N) :
    (1971/1000 : ℝ)*N<log n ∧ log n≤(2029/1000 : ℝ)*N :=
  (Finset.mem_filter.mp hn).2

private theorem order_pos (j : ℕ) : (0 : ℝ)<dyadicMomentOrder j := by
  unfold dyadicMomentOrder dyadicPrimeCount
  positivity

private theorem prime_not_of_count {n : ℕ} (hc : 3≤n.primeFactors.card) : ¬n.Prime := by
  intro hp
  simp only [hp.primeFactors,Finset.card_singleton] at hc
  omega

private theorem coefficient_eq_original {L : ℝ} {n : ℕ}
    (hc : 3≤n.primeFactors.card) :
    completedCoefficient L n=SquarefreeVaughanLogSource.coefficient L n := by
  simp only [completedCoefficient,SquarefreeVaughanLogSource.coefficient,
    prime_not_of_count hc,not_false_eq_true,and_true]

/-- A failed upper physical prime mask contributes EXACTLY zero at counts
>=3 throughout the strict core. No prime tail is discarded. -/
theorem completedCoefficient_zero_of_physical_failure {u : ℝ} {j n : ℕ}
    (hn : n∈centralFullLabels (dyadicMomentOrder j)) (hs : Squarefree n)
    (hc : 3≤n.primeFactors.card)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hphys : ¬∀ p∈n.primeFactors,
      p<(ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2) :
    completedCoefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=0 := by
  let N := dyadicMomentOrder j
  let X := (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2
  have hX : 0<X := by dsimp [X]; positivity
  have hlogX : log (X^2 : ℕ)=2*SquarefreeVaughanLogSource.length u N := by
    simp only [X,SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,
      Nat.cast_ofNat,log_pow]
  have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hs.ne_zero
  have hnX : n<X^2 := by
    have ht := (central_log hn).2
    have hNp := order_pos j
    have hl : log n<log (X^2 : ℕ) := by
      rw [hlogX]
      dsimp [N] at *
      nlinarith only [ht,hL,hNp]
    exact_mod_cast (log_lt_log_iff hn0 (by exact_mod_cast pow_pos hX 2)).mp hl
  rw [coefficient_eq_original hc]
  by_contra hnot
  push Not at hphys
  obtain ⟨p,hpn,hpX⟩ := hphys
  have hp := Nat.prime_of_mem_primeFactors hpn
  obtain ⟨a,ha,_haX,he,_⟩ :=
    ZetaRieszPhysicalProductBounds.nonzero_extreme_below_square_is_semiprime hp
      (Nat.dvd_of_mem_primeFactors hpn) hpX hnX hnot
  have htwo := ZetaRieszMaskSupport.pair_prime_count_le_two hp ha
  rw [he] at hc
  omega

private theorem balanced_prime_log {j n p : ℕ} (hp : p∈n.primeFactors)
    (hb : log (largestPrime n)<(51/50 : ℝ)*dyadicMomentOrder j) :
    log p<(51/50 : ℝ)*dyadicMomentOrder j := by
  have hmax : p≤largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  exact (log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    (by exact_mod_cast hmax)).trans_lt hb

/-- No original deletion or allocation-sector support mask rejects a
balanced central label with low count and physical primes. -/
theorem balanced_mem_native_central {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n : ℕ} (hj : 32≤j)
    (hn : n∈centralFullLabels (dyadicMomentOrder j)) (hs : Squarefree n)
    (hc : 3≤n.primeFactors.card)
    (hct : n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)
    (hb : log (largestPrime n)<(51/50 : ℝ)*dyadicMomentOrder j)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (hphys : ∀ p∈n.primeFactors,
      p<(ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2) :
    n∈centralLabels u j := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  have ht := central_log hn
  have hNp := order_pos j
  have hN : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hlog : 0<log n := by dsimp [N] at hN; nlinarith only [ht.1,hN]
  have hW : n∈literalWindow N := by
    apply (mem_literalWindow N n).mpr
    dsimp [N] at *
    constructor <;> nlinarith only [ht.1,ht.2,hNp]
  have hcount : n.primeFactors.card<K :=
    hct.trans_le (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2
  have hmask := ZetaRieszMaskSupport.window_mem_originalMask j hj hu
    (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le) hL hW hs hc hcount hphys
  have hnotC : n∉cancellingSector u N K := by
    intro h
    obtain ⟨_,_,_,_,_,p,hp,_,_,_,hhi⟩ := Finset.mem_filter.mp h
    have hl := ZetaRieszMarkedSaturation.log_split hs hp
    have hpL := balanced_prime_log hp hb
    have hco := (div_le_iff₀ hlog).mp hhi
    dsimp [N] at *
    nlinarith only [ht.1,hco,hl,hpL,hNp]
  have hret : n∈ZetaRieszMaskSupport.retainedBand u N K :=
    Finset.mem_sdiff.mpr ⟨hmask,hnotC⟩
  have hnotD : n∉ZetaRieszDominantAllocation.dominantSector u N K := by
    intro h
    obtain ⟨_,_,_,_,p,hp,_,_,hdom⟩ := Finset.mem_filter.mp h
    have hpL := balanced_prime_log hp hb
    dsimp [N] at *
    nlinarith only [ht.1,hdom,hpL,hNp]
  have hnd : n∈ZetaRieszDominantAllocation.nondominantBand u N K :=
    Finset.mem_sdiff.mpr ⟨hret,hnotD⟩
  have hcore : n∈ZetaRieszParityPacket.coreBand u N K := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnd,?_,?_⟩,?_,?_⟩
    all_goals dsimp [N] at *
    all_goals nlinarith only [ht.1,ht.2,hNp]
  have hnative : n∈ZetaRieszPaidIncidenceFloor.nativeLabels u j := by
    unfold ZetaRieszPaidIncidenceFloor.nativeLabels
    rw [ZetaRieszJointCountFloor.coreBand_count_filter _ _ _ _
      (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).2]
    exact Finset.mem_filter.mpr ⟨hcore,hct⟩
  exact mem_centralLabels.mpr ⟨mem_restLabels.mpr ⟨Finset.mem_filter.mpr ⟨hnative,hs⟩,hb⟩,ht⟩

/-- Raw high owners at EVERY count. No physical or old allocation mask
is imposed; zero physical failures may remain as literal zero slots. -/
def rawHighLabels (j : ℕ) : Finset ℕ :=
  (centralFullLabels (dyadicMomentOrder j)).filter (fun n =>
    Squarefree n ∧ 3≤n.primeFactors.card ∧
      (51/50 : ℝ)*dyadicMomentOrder j≤log (largestPrime n))

theorem rawHigh_subset_rejected (u : ℝ) (j : ℕ) :
    rawHighLabels j⊆rejectedLabels u j := by
  intro n hn
  obtain ⟨hn,hs,hc,hh⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,hs,hc,?_⟩
  intro hcN
  have hlo := (mem_restLabels.mp (mem_centralLabels.mp hcN).1).2
  linarith only [hlo,hh]

/-- Exactly the balanced mask failures, before paying their high-count
subset. They are not silently replaced by arbitrary rough labels. -/
def balancedFailures (u : ℝ) (j : ℕ) : Finset ℕ :=
  rejectedLabels u j\rawHighLabels j

private theorem failure_data {u : ℝ} {j n : ℕ} (hn : n∈balancedFailures u j) :
    n∈centralFullLabels (dyadicMomentOrder j) ∧ Squarefree n ∧ 3≤n.primeFactors.card ∧
      log (largestPrime n)<(51/50 : ℝ)*dyadicMomentOrder j ∧ n∉centralLabels u j := by
  obtain ⟨hr,hh⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hf,hs,hc,hnot⟩ := Finset.mem_filter.mp hr
  have hb : log (largestPrime n)<(51/50 : ℝ)*dyadicMomentOrder j := by
    by_contra h
    exact hh (Finset.mem_filter.mpr ⟨hf,hs,hc,le_of_not_gt h⟩)
  exact ⟨hf,hs,hc,hb,hnot⟩

/-- Below the count ceiling, EVERY balanced completion failure is an
exact zero. This removes physical/deletion/nondominant failure labels
without any phase estimate or per-sector debit. -/
theorem low_failure_coefficient_zero {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {j n : ℕ} (hj : 32≤j)
    (hn : n∈balancedFailures u j)
    (hct : n.primeFactors.card<ZetaRieszNearCriticalCountPayment.countCeiling j)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) :
    completedCoefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n=0 := by
  obtain ⟨hf,hs,hc,hb,hnot⟩ := failure_data hn
  by_cases hp : ∀ p∈n.primeFactors,
      p<(ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2
  · exact False.elim (hnot (balanced_mem_native_central hu hU hj hf hs hc hct hb hL hp))
  · exact completedCoefficient_zero_of_physical_failure hf hs hc hL hp

/-- An exact high-count subpopulation, retaining every remaining mask. -/
def highFailures (u : ℝ) (j : ℕ) : Finset ℕ :=
  (balancedFailures u j).filter (fun n =>
    ZetaRieszNearCriticalCountPayment.countCeiling j≤n.primeFactors.card)

/-- All mask failures are paid together, uniformly in height, by the
already proved high-count rate. No unsigned bound on the raw high owners
or ordinary-prime correction occurs. -/
theorem eventually_balanced_failures_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ j in atTop, ∀ y : ℝ,
      ‖completionTerm u y (dyadicMomentOrder j) (balancedFailures u j)‖≤
        ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszMaskSupport.eventually_length_lower (by linarith : 0<u)
        (hU.trans ZetaRieszWideOwnerAudit.radius_lt_source.le)),
    ZetaRieszNearCriticalCountPayment.eventually_nearCritical_count_sum_bound]
    with j hj hL hb
  intro y
  have he : completionTerm u y (dyadicMomentOrder j) (balancedFailures u j)=
      completionTerm u y (dyadicMomentOrder j) (highFailures u j) := by
    unfold completionTerm highFailures
    rw [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : ZetaRieszNearCriticalCountPayment.countCeiling j≤n.primeFactors.card
    · simp only [if_pos hc]
    · rw [if_neg hc,low_failure_coefficient_zero hu hU hj hn (by omega) hL,zero_mul]
  rw [he]
  apply hb (highFailures u j)
    (completedCoefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)))
      y u (by linarith : 0≤u) hU
  · intro n _
    have hc := completedCoefficient_norm_le
      (SquarefreeVaughanLogSource.length_pos u (dyadicMomentOrder j)) n
    have hn := zetaMoebiusLogMajorant_nonneg n
    linarith only [hc,hn]
  · intro n hn
    exact (failure_data (Finset.mem_filter.mp hn).1).2.1
  · intro n hn
    have ht := (central_log (failure_data (Finset.mem_filter.mp hn).1).1).2
    have hN : (0 : ℝ)≤dyadicMomentOrder j := Nat.cast_nonneg _
    nlinarith only [ht,hN]
  · intro n hn
    have hc := (Finset.mem_filter.mp hn).2
    have hK := (ZetaRieszNearCriticalCountPayment.countCeiling_bounds j).1
    omega

/-- All remaining source-carrying completion terms stay together: every
ordinary prime, every semiprime, raw high owners at ALL counts, SAME head.
All balanced rejected masks have a separate proved geometric payment. -/
def prunedBoundary (u y : ℝ) (j : ℕ) : ℂ :=
  let N := dyadicMomentOrder j
  completionTerm u y N (primeLabels N)+completionTerm u y N (semiprimeLabels N)+
    completionTerm u y N (rawHighLabels j)+
      (ZetaRieszRoughPrimePairCancellation.nativeHead u y N : ℂ)

/-- Exact signed difference; no masked population is replaced silently. -/
theorem joined_sub_pruned_eq_failures (u y : ℝ) (j : ℕ) :
    joinedBoundary u y j-prunedBoundary u y j=
      completionTerm u y (dyadicMomentOrder j) (balancedFailures u j) := by
  have he : completionTerm u y (dyadicMomentOrder j) (rejectedLabels u j)-
      completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)=
        completionTerm u y (dyadicMomentOrder j) (balancedFailures u j) := by
    unfold completionTerm balancedFailures
    rw [← mul_sub,Finset.sum_sdiff_eq_sub (rawHigh_subset_rejected u j)]
  unfold joinedBoundary prunedBoundary
  dsimp only
  linear_combination he

/-- Pay EVERY balanced completion-mask failure by the full-population
count rate, before making any new signed price for the retained boundary. -/
theorem eventually_joined_sub_pruned_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ j in atTop, ∀ y : ℝ, ‖joinedBoundary u y j-prunedBoundary u y j‖≤
      ZetaRieszNearCriticalCountPayment.allowance j := by
  filter_upwards [eventually_balanced_failures_bound hu hU] with j hj
  intro y
  rw [joined_sub_pruned_eq_failures]
  exact hj y

/-- The original whole native error budget plus the newly paid COMPLETION
count tail. No raw high-owner response is counted as a vanishing error. -/
def nativePrunedBudget (u y : ℝ) (j : ℕ) : ℝ :=
  nativeBoundaryBudget u y j+ZetaRieszNearCriticalCountPayment.allowance j

theorem nativePrunedBudget_tendsto (u y : ℝ) :
    Tendsto (nativePrunedBudget u y) atTop (𝓝 0) := by
  change Tendsto (fun j => nativeBoundaryBudget u y j+
    ZetaRieszNearCriticalCountPayment.allowance j) atTop (𝓝 0)
  simpa only [add_zero] using (nativeBoundaryBudget_tendsto u y).add
    ZetaRieszNearCriticalCountPayment.tendsto_allowance

/-- Spend the new geometric payment INSIDE the literal native signed
floor ledger, removing all balanced count/physical/deletion failures at
once. Every source-carrying prime/high-owner term remains joined. -/
theorem eventually_native_pruned_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        (prunedBoundary u y j).re|≤nativePrunedBudget u y j := by
  filter_upwards [eventually_native_boundary_bound hu hU hy,
    eventually_joined_sub_pruned_bound hu hU] with j hn he
  have hr : |(joinedBoundary u y j).re-(prunedBoundary u y j).re|≤
      ZetaRieszNearCriticalCountPayment.allowance j := by
    exact (Complex.abs_re_le_norm _).trans (he y)
  apply abs_le.mpr
  unfold nativePrunedBudget
  constructor <;> linarith only [(abs_le.mp hn).1,(abs_le.mp hn).2,
    (abs_le.mp hr).1,(abs_le.mp hr).2]

theorem tendsto_native_plus_pruned_boundary {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
          (prunedBoundary u y j).re) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (nativePrunedBudget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_native_pruned_bound hu hU hy

/-- The whole native floor is now reduced to the signed prime/semiprime/
raw-high-owner/head boundary, with a fully paid geometric mask transfer.
An independent upper bound for this retained joint scalar is still open. -/
theorem eventually_native_pruned_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -(prunedBoundary u y j).re-nativePrunedBudget u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_pruned_bound hu hU hy] with j hj
  linarith only [(abs_le.mp hj).1]

end RiemannGaussian.ZetaRieszGlobalBoundaryPruning
