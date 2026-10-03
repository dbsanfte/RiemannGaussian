/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnallocatedOwnerPayment

/-!
# Remove raw high-owner counts from the native boundary, with their correction

The literal unallocated count>=3 population and its exact unallocated
prime correction are paid together. The full original head stays in the
remaining signed prime/prime-pair boundary. No numerical floor is claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalHighOwnerPayment
open ZetaRieszUnallocatedOwnerPayment ZetaRieszOwnerLatticePhase
open ZetaRieszGlobalBulkPayment ZetaRieszGlobalCentralPayment
open ZetaRieszGlobalBoundaryPruning ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCountFrequency ZetaRieszBalancedRadialPayment

/-- Every raw high owner on the ORIGINAL wide window, at every count. -/
def fullRawLabels (N : ℕ) : Finset ℕ :=
  (fullLabels N).filter (fun n => Squarefree n ∧ 3≤n.primeFactors.card ∧
    (51/50 : ℝ)*N≤log (largestPrime n))

/-- Removing owners above the moving cutoff loses only exact zero slots. -/
def boundedRawLabels (u : ℝ) (N : ℕ) : Finset ℕ :=
  (fullRawLabels N).filter (fun n => log (largestPrime n)≤SquarefreeVaughanLogSource.length u N)

private def incidences (u : ℝ) (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (highOwners u N).sigma (rowCofactors N)

private def product (e : Σ _ : ℕ, ℕ) : ℕ := e.1*e.2

private theorem incidence_data {u : ℝ} {N : ℕ} (hN : 65536≤N)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {e : Σ _ : ℕ, ℕ} (he : e∈incidences u N) :
    e.1∈highOwners u N ∧ e.2∈rowCofactors N e.1 ∧
      1<e.2 ∧ e.2<e.1 ∧ log e.2≤SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hp,ha⟩ := Finset.mem_sigma.mp he
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have hLlo : (51/50 : ℝ)*N≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hlo,Nat.cast_nonneg (α:=ℝ) N]
  obtain ⟨ha1,hap,haL⟩ := cofactor_window_data hu (by omega) hp hLlo (Finset.mem_filter.mp ha).1
  exact ⟨hp,ha,ha1,hap,haL⟩

private theorem incidence_largest {u : ℝ} {N : ℕ} (hN : 65536≤N)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {e : Σ _ : ℕ, ℕ} (he : e∈incidences u N) :
    largestPrime (product e)=e.1 := by
  obtain ⟨hp,ha,_ha1,hap,_haL⟩ := incidence_data hN hu hU he
  have hs := (Finset.mem_filter.mp ha).2.1
  apply ZetaRieszPrimeIntervals.largestPrime_mul e.1 e.2 (highOwner_data hp).1 hs.ne_zero
  intro q hq
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) (Nat.dvd_of_mem_primeFactors hq)).trans_lt hap

private theorem product_injective {u : ℝ} {N : ℕ} (hN : 65536≤N)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Set.InjOn product (incidences u N) := by
  intro e he f hf h
  have hp : e.1=f.1 := by
    rw [← incidence_largest hN hu hU he,← incidence_largest hN hu hU hf,h]
  have hp0 := (highOwner_data (incidence_data hN hu hU he).1).1.pos
  have ha : e.2=f.2 := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    simpa only [product,← hp] using h
  exact Sigma.ext hp (heq_of_eq ha)

private theorem squarefree_count_ge_two {a : ℕ} (hs : Squarefree a)
    (ha1 : a≠1) (hap : ¬a.Prime) : 2≤a.primeFactors.card := by
  by_contra h
  have hc : a.primeFactors.card≤1 := by omega
  rcases eq_or_lt_of_le hc with h1 | h0
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp h1
    have hmem : p∈a.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have hpp := Nat.prime_of_mem_primeFactors hmem
    have he := Nat.prod_primeFactors_of_squarefree hs
    rw [hp,Finset.prod_singleton] at he
    exact hap (he ▸ hpp)
  · have hz : a.primeFactors=∅ := Finset.card_eq_zero.mp (by omega)
    have he := Nat.prod_primeFactors_of_squarefree hs
    rw [hz,Finset.prod_empty] at he
    exact ha1 he.symm

private theorem product_mem_bounded {u : ℝ} {N : ℕ} (hN : 65536≤N)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling)
    {e : Σ _ : ℕ, ℕ} (he : e∈incidences u N) : product e∈boundedRawLabels u N := by
  obtain ⟨hp,ha,ha1,hap,_haL⟩ := incidence_data hN hu hU he
  obtain ⟨hpp,_hpQ,hc,hpL⟩ := highOwner_data hp
  obtain ⟨haw,has,hanp⟩ := Finset.mem_filter.mp ha
  have hn0 : e.2≠0 := has.ne_zero
  have hnot : ¬e.1∣e.2 := fun hd => (Nat.le_of_dvd (by omega : 0<e.2) hd).not_gt hap
  have hs : Squarefree (product e) := Nat.squarefree_mul_iff.mpr
    ⟨hpp.coprime_iff_not_dvd.mpr hnot,hpp.squarefree,has⟩
  have hpnot : e.1∉e.2.primeFactors := fun hh => hnot (Nat.dvd_of_mem_primeFactors hh)
  have hcount : 3≤(product e).primeFactors.card := by
    have ha2 := squarefree_count_ge_two has (by omega) hanp
    simp only [product,Nat.primeFactors_mul hpp.ne_zero hn0,hpp.primeFactors,
      Finset.singleton_union,Finset.card_insert_of_notMem hpnot]
    omega
  have hlog : log (product e)=log e.1+log e.2 := by
    rw [product,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hn0)]
  have hf : product e∈fullLabels N := by
    apply (coreFloor_membership N 0 (Nat.pos_of_ne_zero hs.ne_zero)).mpr
    rw [zero_add,hlog]
    exact (coreFloor_membership N (log e.1) (by omega : 0<e.2)).mp haw
  simp only [boundedRawLabels,fullRawLabels,Finset.mem_filter]
  exact ⟨⟨hf,hs,hcount,by rwa [incidence_largest hN hu hU he]⟩,
    by rwa [incidence_largest hN hu hU he]⟩

private theorem bounded_eq_image {u : ℝ} {N : ℕ} (hN : 65536≤N)
    (hu : 1/2≤u) (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    boundedRawLabels u N=(incidences u N).image product := by
  apply Finset.Subset.antisymm
  · intro n hn
    obtain ⟨hraw,hpL⟩ := Finset.mem_filter.mp hn
    obtain ⟨hf,hs,hc,hpmin⟩ := Finset.mem_filter.mp hraw
    let p := largestPrime n
    have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨has,ha1,hanp,_hnot⟩ := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
    have hm : p*(n/p)=n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
    have hlog : log n=log p+log (n/p : ℕ) := by
      conv_lhs => rw [← hm,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
        (by exact_mod_cast has.ne_zero)]
    have hpP : p∈highOwners u N := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨hpp.pos,?_⟩,hpp,hpmin⟩
      apply Nat.le_floor
      rw [← exp_log (by exact_mod_cast hpp.pos : (0 : ℝ)<p)]
      exact exp_le_exp.mpr hpL
    have haW : n/p∈Finset.Ioc (coreFloor N (log p) (39/20))
        (coreFloor N (log p) (203/100)) := by
      apply (coreFloor_membership N (log p) (Nat.pos_of_ne_zero has.ne_zero)).mpr
      have hwin := (coreFloor_membership N 0 (Nat.pos_of_ne_zero hs.ne_zero)).mp hf
      rw [zero_add,hlog] at hwin
      exact hwin
    refine Finset.mem_image.mpr ⟨⟨p,n/p⟩,?_,hm⟩
    exact Finset.mem_sigma.mpr ⟨hpP,Finset.mem_filter.mpr ⟨haW,has,hanp⟩⟩
  · intro n hn
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hn
    exact product_mem_bounded hN hu hU he

private theorem fullRaw_cofactor_data {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈fullRawLabels N) :
    let p := largestPrime n
    p∈n.primeFactors ∧ Squarefree (n/p) ∧ n/p≠1 ∧ ¬(n/p).Prime ∧ ¬p∣n/p ∧
      log (n/p : ℕ)≤SquarefreeVaughanLogSource.length u N := by
  obtain ⟨hf,hs,hc,hpmin⟩ := Finset.mem_filter.mp hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2≤n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨has,ha1,hanp,hnot⟩ := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  have hm : largestPrime n*(n/largestPrime n)=n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hlog : log n=log (largestPrime n)+log (n/largestPrime n : ℕ) := by
    conv_lhs => rw [← hm,Nat.cast_mul,log_mul (by exact_mod_cast hpp.ne_zero)
      (by exact_mod_cast has.ne_zero)]
  have hw := (coreFloor_membership N 0 (Nat.pos_of_ne_zero hs.ne_zero)).mp hf
  simp only [zero_add] at hw
  have hlo := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0<u) hU
  have haL : log (n/largestPrime n : ℕ)≤SquarefreeVaughanLogSource.length u N := by
    nlinarith only [hw.2,hpmin,hlog,hlo,Nat.cast_nonneg (α:=ℝ) N]
  exact ⟨hp,has,ha1,hanp,hnot,haL⟩

/-- Above-cutoff owners contribute EXACTLY zero at ALL counts>=3. -/
theorem fullRaw_coefficient_zero_of_large {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ} (hN : 65536≤N)
    (hn : n∈fullRawLabels N) (hpL : SquarefreeVaughanLogSource.length u N≤log (largestPrime n)) :
    completedCoefficient (SquarefreeVaughanLogSource.length u N) n=0 := by
  obtain ⟨hp,has,ha1,hanp,hnot,haL⟩ := fullRaw_cofactor_data hu hU hN hn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hm : largestPrime n*(n/largestPrime n)=n := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated has ha1 hanp haL
  have hr := ZetaSquarefreeRieszWindows.riesz_prime_mul (SquarefreeVaughanLogSource.length u N) hpp hnot
  rw [hm,hz,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hpL),sub_zero] at hr
  simp only [completedCoefficient,hr,mul_zero,zero_div,Complex.ofReal_zero,ite_self]

/-- Remove ONLY the zero above-length slots, not any ordinary-prime
completion correction or phase. -/
theorem fullRaw_term_eq_bounded {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    completionTerm u y N (fullRawLabels N)=completionTerm u y N (boundedRawLabels u N) := by
  unfold completionTerm boundedRawLabels
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpL : log (largestPrime n)≤SquarefreeVaughanLogSource.length u N
  · simp only [if_pos hpL]
  · rw [if_neg hpL,fullRaw_coefficient_zero_of_large hu hU hN hn (le_of_not_ge hpL),zero_mul]

/-- EXACT native-to-row connection. Every raw count>=3 physical label
has one largest-prime incidence; no duplicated pair or phase is used. -/
theorem fullRaw_re_eq_highRows {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536≤N) (y : ℝ) :
    (completionTerm u y N (fullRawLabels N)).re=highCompositeRows u y N := by
  rw [fullRaw_term_eq_bounded hu hU hN y]
  unfold completionTerm
  rw [bounded_eq_image hN hu hU,Finset.sum_image (product_injective hN hu hU),
    Finset.mul_sum,Complex.re_sum]
  simp only [incidences,Finset.sum_sigma]
  unfold highCompositeRows
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [product,mul_assoc] using literal_row_eq hu hU hN hp y

/-- Literal native raw high owners are precisely the contracted radial
projection of the full unallocated all-count population. -/
theorem rawHigh_eq_projection (j : ℕ) :
    rawHighLabels j=LogarithmicDeviation.deviationBand (fullRawLabels (dyadicMomentOrder j))
      (1971/1000) (2029/1000) (dyadicMomentOrder j) := by
  ext n
  simp only [rawHighLabels,centralFullLabels,fullRawLabels,
    LogarithmicDeviation.deviationBand,Finset.mem_filter]
  tauto

/-- Only the already-funded radial mismatch is paid. The actual
unallocated raw high-owner population is never replaced by an allocated one. -/
theorem rawHigh_sub_full_bound {u : ℝ} (hu : 0≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (j : ℕ) (y : ℝ) :
    ‖completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)-
      completionTerm u y (dyadicMomentOrder j) (fullRawLabels (dyadicMomentOrder j))‖≤radialBudget j := by
  have hb := (Classical.choose_spec ZetaRieszLargeOrderCore.exists_edge_bound).2
    (dyadicMomentOrder j) (fullRawLabels (dyadicMomentOrder j))
    (completedCoefficient (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)))
      (fun n _ => completedCoefficient_norm_le (SquarefreeVaughanLogSource.length_pos u _) n)
        y u hu hU
  rw [rawHigh_eq_projection]
  unfold completionTerm radialBudget radialConstant
  rw [norm_sub_rev]
  simpa only [mul_sub] using hb

/-- ALL raw native high-owner counts plus their literal unallocated
prime correction have an independent source-o(1) estimate. -/
theorem rawHigh_add_correction_bound {u y : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54≤|y|)
    {j : ℕ} (hN : 65536≤dyadicMomentOrder j) :
    |(completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re+
      highPrimeCorrection u y (dyadicMomentOrder j)|≤
      radialBudget j+(1+(7/5 : ℝ)*dyadicMomentOrder j)*ownerBudget u y (dyadicMomentOrder j) := by
  have he := rawHigh_sub_full_bound (by linarith : 0≤u) hU j y
  have hr : |(completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re-
      (completionTerm u y (dyadicMomentOrder j) (fullRawLabels (dyadicMomentOrder j))).re|≤
        radialBudget j := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm _).trans he
  have hb := highRows_add_correction_bound hu hU hy (by omega : 64≤dyadicMomentOrder j)
  rw [← fullRaw_re_eq_highRows hu hU hN y] at hb
  have hs := (abs_add_le
    ((completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re-
      (completionTerm u y (dyadicMomentOrder j) (fullRawLabels (dyadicMomentOrder j))).re)
    ((completionTerm u y (dyadicMomentOrder j) (fullRawLabels (dyadicMomentOrder j))).re+
      highPrimeCorrection u y (dyadicMomentOrder j))).trans (add_le_add hr hb)
  convert hs using 1
  congr 1
  ring

/-- The remaining boundary has ONLY ordinary primes and distinct
prime pairs. The SAME full original head and the exact new unallocated
correction remain signed and joined. Neither correction is discarded. -/
def lowCountBoundary (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  (completionTerm u y N (primeLabels N)).re+
    (completionTerm u y N (semiprimeLabels N)).re+
      ZetaRieszRoughPrimePairCancellation.nativeHead u y N-highPrimeCorrection u y N

/-- Original native payments plus ONE new radial transfer and the
proved all-owner joint error. No head price or period credit is spent. -/
def nativeLowCountBudget (u y : ℝ) (j : ℕ) : ℝ :=
  let N := dyadicMomentOrder j
  nativePrunedBudget u y j+radialBudget j+(1+(7/5 : ℝ)*N)*ownerBudget u y N

/-- Exact signed change in the existing ledger. All high counts move
into a PAID joint error; the prime correction stays in the low-count main. -/
theorem pruned_sub_lowCount_eq (u y : ℝ) (j : ℕ) :
    (prunedBoundary u y j).re-lowCountBoundary u y j=
      (completionTerm u y (dyadicMomentOrder j) (rawHighLabels j)).re+
        highPrimeCorrection u y (dyadicMomentOrder j) := by
  simp only [prunedBoundary,lowCountBoundary,Complex.add_re,Complex.ofReal_re]
  ring

/-- Concrete global progress: every raw high-owner count is paid inside
THE native ledger. The remaining independent arithmetic upper bound is
on this ONE signed ordinary-prime/prime-pair combination. -/
theorem eventually_native_lowCount_bound {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      |((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
        lowCountBoundary u y j|≤nativeLowCountBudget u y j := by
  filter_upwards [eventually_native_pruned_bound hu hU hy,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (65536 : ℕ))] with j hp hN
  have he := rawHigh_add_correction_bound hu.le hU hy hN
  rw [← pruned_sub_lowCount_eq] at he
  apply abs_le.mpr
  unfold nativeLowCountBudget
  constructor <;> linarith only [(abs_le.mp hp).1,(abs_le.mp hp).2,
    (abs_le.mp he).1,(abs_le.mp he).2]

/-- Every new error vanishes on the original cofinal moment schedule. -/
theorem nativeLowCountBudget_tendsto (u y : ℝ) :
    Tendsto (nativeLowCountBudget u y) atTop (𝓝 0) := by
  have h := ((nativePrunedBudget_tendsto u y).add radialBudget_tendsto).add
    ((globalBudget_tendsto u y).comp tendsto_dyadicMomentOrder)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with j
  rfl

/-- Source-equivalence, with every actual prime/prime-pair correction
retained. An independent cofinal upper bound for lowCountBoundary remains
OPEN; no floor, ceiling, restricted exclusion or RH follows automatically. -/
theorem tendsto_native_plus_lowCountBoundary {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    Tendsto (fun j =>
      ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
        (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re+
          lowCountBoundary u y j) atTop (𝓝 0) := by
  apply squeeze_zero_norm' ?_ (nativeLowCountBudget_tendsto u y)
  simpa only [Real.norm_eq_abs] using eventually_native_lowCount_bound hu hU hy

/-- The exact remaining sufficient floor target is the upper bound on
the retained signed low-count main, not its divergent positive atom price. -/
theorem eventually_native_lowCount_floor {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54≤|y|) :
    ∀ᶠ j in atTop,
      -lowCountBoundary u y j-nativeLowCountBudget u y j≤
        ((u : ℂ)^(dyadicMomentOrder j+1)*ZetaRieszParityPacket.coreResponse u y
          (dyadicMomentOrder j) (ZetaRieszNearCriticalCountPayment.countCeiling j)).re := by
  filter_upwards [eventually_native_lowCount_bound hu hU hy] with j hj
  linarith only [(abs_le.mp hj).1]

end RiemannGaussian.ZetaRieszGlobalHighOwnerPayment
