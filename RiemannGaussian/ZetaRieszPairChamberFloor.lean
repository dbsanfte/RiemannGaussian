/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedPrefixFloor
import RiemannGaussian.ZetaRieszCardinalityChamber

/-!
# Signed pair cancellation on the unpaid physical core

When every prime log is between one third and one half of the reflected
cutoff, the unit, prime and prime-pair divisor sums cancel to one affine
expression. The resulting adverse charge is intersected with the CURRENT
prefix/reflection charge on the same label. Every allocation and phase is
retained, and the saving is spent only on a caller's unpaid subset.
This does not bound the remaining aggregate by 79/1000.
-/

namespace RiemannGaussian.ZetaRieszPairChamberFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszCardinalityChamber ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- All singleton and pair hinges are active; every higher hinge vanishes.
The equality includes every divisor sign, before applying a phase. -/
theorem kernel_pair_chamber {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hc : 2 ≤ S.card) (hx : ∀ i ∈ S, D/3 ≤ x i ∧ x i ≤ D/2) :
    ZetaRieszContinuumCascade.kernel S x D = chamberKernel S.card 2 (∑ i ∈ S, x i) D := by
  apply kernel_chamber S x D hc
  · intro A hA hcard
    have hb := Finset.sum_le_sum (fun i hi => (hx i (Finset.mem_powerset.mp hA hi)).2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hb
    have hcr : (A.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hcr (by positivity : 0 ≤ D/2)]
  · intro A hA hcard
    have hb := Finset.sum_le_sum (fun i hi => (hx i (Finset.mem_powerset.mp hA hi)).1)
    simp only [Finset.sum_const,nsmul_eq_mul] at hb
    have hcr : (3 : ℝ) ≤ A.card := by exact_mod_cast (show 3 ≤ A.card by omega)
    nlinarith [mul_le_mul_of_nonneg_right hcr (by positivity : 0 ≤ D/3)]

/-- A literal share geometry, without fixing a prime count or radial slice. -/
def PairChamber (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ 2 ≤ n.primeFactors.card ∧ L ≤ Real.log n ∧
    ∀ p ∈ n.primeFactors,
      (Real.log n-L)/3 ≤ Real.log p ∧ Real.log p ≤ (Real.log n-L)/2

/-- The affine result of summing the three active divisor levels together. -/
def pairCoefficient (L : ℝ) (n : ℕ) : ℝ :=
  -(Real.log n/L)*(-1 : ℝ)^n.primeFactors.card*
    (((n.primeFactors.card-1).choose 2 : ℝ)*(Real.log n-L)-
      ((n.primeFactors.card-2 : ℕ) : ℝ)*Real.log n)

/-- The actual coefficient equals the signed affine result for every label
in this geometry; no completion or prime-density approximation enters. -/
theorem coefficient_eq_pair {L : ℝ} {n : ℕ} (h : PairChamber L n) :
    (SquarefreeVaughanLogSource.coefficient L n).re = pairCoefficient L n := by
  have hk := kernel_pair_chamber n.primeFactors (fun p => Real.log p)
    (sub_nonneg.mpr h.2.2.1) h.2.1 h.2.2.2
  rw [ZetaRieszContinuumCascade.kernel_primeFactors h.1,
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum h.1] at hk
  have hc2 := h.2.1
  have hc : n.primeFactors.card = (n.primeFactors.card-2)+2 := by omega
  have he := chamberKernel_eq (n.primeFactors.card-2) 1 (Real.log n) (Real.log n-L)
  have hc1 : n.primeFactors.card-2+1 = n.primeFactors.card-1 := by omega
  rw [← hc,hc1] at he
  norm_num only [Nat.choose_one_right,pow_two,neg_one_sq,one_mul] at he
  rw [he] at hk
  rw [coefficient_eq_active h.1 h.2.1,← riesz_eq_active _ h.1,hk]
  rfl

/-- The original phase determines the exact adverse part AFTER the unit,
prime and pair cancellation. Favorable observations remain untouched. -/
def pairCost (L y : ℝ) (n : ℕ) : ℝ :=
  max (-(pairCoefficient L n*Real.cos (y*Real.log n))) 0

theorem pairCost_nonneg (L y : ℝ) (n : ℕ) : 0 ≤ pairCost L y n := le_max_right _ _

/-- On this whole geometry the retained floor is an equality. -/
theorem pair_floor_exact (A : Finset ℕ) (L y : ℝ) (N : ℕ) {n : ℕ}
    (h : PairChamber L n) :
    let f := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max f 0-weight A N n*pairCost L y n = f := by
  dsimp only
  rw [re_residual_atom,coefficient_eq_pair h]
  let x := pairCoefficient L n*Real.cos (y*Real.log n)
  change max (weight A N n*x) 0-weight A N n*max (-x) 0 = weight A N n*x
  have hw := weight_nonneg A N n
  by_cases hx : 0 ≤ x
  · rw [max_eq_left (mul_nonneg hw hx),max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_ge hx)),
      max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
    ring

/-- Only an improvement beyond BOTH existing charges is counted. -/
def pairSaving (L y : ℝ) (n : ℕ) : ℝ :=
  if PairChamber L n then
    max (min (ZetaRieszSevenPrimeReflection.floorCost L y n)
      (ZetaRieszSaturatedCoreFloor.floorCost L y n)-pairCost L y n) 0
  else 0

theorem pairSaving_nonneg (L y : ℝ) (n : ℕ) : 0 ≤ pairSaving L y n := by
  unfold pairSaving
  split_ifs <;> positivity

/-- A nondegenerate balanced region with literal logarithms. The moving
length is retained and the radial variable is not frozen at its saddle. -/
def BalancedSeven (L : ℝ) (n : ℕ) : Prop :=
  Squarefree n ∧ n.primeFactors.card = 7 ∧
    2*Real.log n ≤ 3*L ∧ 10*L ≤ 7*Real.log n ∧
    ∀ p ∈ n.primeFactors, (2/15 : ℝ)*Real.log n ≤ Real.log p ∧
      Real.log p ≤ (3/20 : ℝ)*Real.log n

theorem balancedSeven_pair {L : ℝ} {n : ℕ} (h : BalancedSeven L n) : PairChamber L n := by
  refine ⟨h.1,by have := h.2.1; omega,by
    have := h.2.2.2.1
    linarith [Real.log_natCast_nonneg n],?_⟩
  intro p hp
  have hl := h.2.2.2.2 p hp
  have h₀ := h.2.2.1
  have h₁ := h.2.2.2.1
  constructor <;> linarith [Real.log_natCast_nonneg n]

/-- Seven-prime cancellation evaluated exactly, including its sign. -/
theorem balancedSeven_coefficient {L : ℝ} {n : ℕ} (h : BalancedSeven L n) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      -(Real.log n/L)*(15*L-10*Real.log n) := by
  rw [coefficient_eq_pair (balancedSeven_pair h),pairCoefficient,h.2.1]
  norm_num [Nat.choose]
  ring

theorem balancedSeven_outer_empty {L : ℝ} {n : ℕ} (h : BalancedSeven L n) :
    outerPrimes (Real.log n-L) n = ∅ := by
  have hn1 : n ≠ 1 := by intro he; simpa [he] using h.2.1
  have hn : 1 < n := by have := h.1.ne_zero; omega
  have hT : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hmem := Finset.mem_filter.mp hp
  have hsmall := (h.2.2.2.2 p hmem.1).2
  have hcut := h.2.2.2.1
  linarith

/-- The comparison is against the optimized old seven-prime charge,
not the larger mean-prime/Sperner envelope. -/
theorem balancedSeven_previous_cost {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : BalancedSeven L n) :
    ZetaRieszSevenPrimeReflection.floorCost L y n =
      (Real.log n/L*Real.log n.minFac)*
        (5*max (Real.cos (y*Real.log n)) 0+10*max (-Real.cos (y*Real.log n)) 0) := by
  have ho : (outerPrimes (Real.log n-L) n).card = 0 := by rw [balancedSeven_outer_empty h]; rfl
  have hb : 0 ≤ Real.log n/L*Real.log n.minFac :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (Real.log_natCast_nonneg n.minFac)
  have h₀ : activeCapacity 7 0 0 = 10 := by decide +kernel
  have h₁ : activeCapacity 7 0 1 = 10 := by decide +kernel
  have ha₀ : ZetaRieszReflectedPrimeBounds.allowance L n 0 =
      5*(Real.log n/L*Real.log n.minFac) := by
    norm_num [ZetaRieszReflectedPrimeBounds.allowance,previousAllowance,
      activeAllowance,ZetaRieszIntersectingWindow.allowance,h.1,h.2.1,ho,h₀,
      ZetaRieszIntersectingWindow.oddWindowCapacity_five.2]
    rw [min_eq_left (by nlinarith only [hb])]
    ring
  have ha₁ : ZetaRieszReflectedPrimeBounds.allowance L n 1 =
      10*(Real.log n/L*Real.log n.minFac) := by
    norm_num [ZetaRieszReflectedPrimeBounds.allowance,previousAllowance,
      activeAllowance,ZetaRieszIntersectingWindow.allowance,h.1,h.2.1,ho,h₁,
      ZetaRieszIntersectingWindow.oddWindowCapacity_five.1]
    ring
  rw [ZetaRieszSevenPrimeReflection.floorCost,ZetaRieszSevenPrimeReflection.lowerAllowance,
    if_neg (by omega),ha₀,ha₁]
  ring

/-- Joint prime/pair cancellation saves at least a quarter of the already
optimized charge throughout this open-width geometry, for EVERY phase. -/
theorem balancedSeven_cost_le_three_quarters {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : BalancedSeven L n) :
    pairCost L y n ≤ (3/4 : ℝ)*ZetaRieszSevenPrimeReflection.floorCost L y n := by
  have hn1 : n ≠ 1 := by intro he; simpa [he] using h.2.1
  have hmin := (Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) h.1.ne_zero
  have hr := (h.2.2.2.2 n.minFac hmin).1
  have h₀ := h.2.2.1
  have h₁ := h.2.2.2.1
  have ht : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hc0 : 0 ≤ 15*L-10*Real.log n := by linarith
  have hcr : 15*L-10*Real.log n ≤ (15/4 : ℝ)*Real.log n.minFac := by linarith
  have he := balancedSeven_coefficient h
  rw [coefficient_eq_pair (balancedSeven_pair h)] at he
  rw [pairCost,he,balancedSeven_previous_cost hL y h]
  have he' : -(-(Real.log n/L)*(15*L-10*Real.log n)*Real.cos (y*Real.log n)) =
      (Real.log n/L)*(15*L-10*Real.log n)*Real.cos (y*Real.log n) := by ring
  rw [he']
  have hnonneg := mul_nonneg ht hc0
  by_cases hc : 0 ≤ Real.cos (y*Real.log n)
  · rw [max_eq_left (mul_nonneg hnonneg hc),max_eq_left hc,
      max_eq_right (neg_nonpos.mpr hc)]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcr ht) hc
    nlinarith only [hh]
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hnonneg (le_of_not_ge hc))]
    positivity [Real.log_natCast_nonneg n.minFac]

/-- After the former cutoff credit and the new pair cancellation are joined,
at least a quarter of the old optimized charge is gone on this region. -/
theorem balancedSeven_savings_ge_quarter {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : BalancedSeven L n) :
    (1/4 : ℝ)*ZetaRieszSevenPrimeReflection.floorCost L y n ≤
      ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+pairSaving L y n := by
  have hb := balancedSeven_cost_le_three_quarters hL y h
  have hh : PairChamber L n := balancedSeven_pair h
  rw [pairSaving,if_pos hh]
  have hs := le_max_left
    (min (ZetaRieszSevenPrimeReflection.floorCost L y n)
      (ZetaRieszSaturatedCoreFloor.floorCost L y n)-pairCost L y n) 0
  unfold ZetaRieszJoinedPrefixFloor.cutoffSaving
  rcases le_total (ZetaRieszSevenPrimeReflection.floorCost L y n)
    (ZetaRieszSaturatedCoreFloor.floorCost L y n) with hle | hle
  · rw [max_eq_right (sub_nonpos.mpr hle),min_eq_left hle]
    rw [min_eq_left hle] at hs
    linarith
  · rw [max_eq_left (sub_nonneg.mpr hle),min_eq_right hle]
    rw [min_eq_right hle] at hs
    linarith

/-- These balanced labels were not paid by the earlier saturation/prefix
test. This separates the NEW quarter saving from all previous credits. -/
theorem balancedSeven_old_saving_eq_zero {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : BalancedSeven L n) : ZetaRieszJoinedPrefixFloor.cutoffSaving L y n = 0 := by
  have hn1 : n ≠ 1 := by intro he; simpa [he] using h.2.1
  have hn : 1 < n := by have := h.1.ne_zero; omega
  have hT : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlo := h.2.2.1
  have hhi := h.2.2.2.1
  have haD : activePart (Real.log n-L) n = n := by
    rw [activePart]
    have hf : activePrimes (Real.log n-L) n = n.primeFactors := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have := (h.2.2.2.2 p hp).2
      linarith
    rw [hf,Nat.prod_primeFactors_of_squarefree h.1]
  have haL : activePart L n = n := by
    rw [activePart]
    have hf : activePrimes L n = n.primeFactors := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have := (h.2.2.2.2 p hp).2
      linarith
    rw [hf,Nat.prod_primeFactors_of_squarefree h.1]
  have ho : outerPart (Real.log n-L) n = 1 := by
    rw [outerPart,balancedSeven_outer_empty h,Finset.prod_empty]
  have hsat : ¬(ZetaRieszSaturatedCoreFloor.SaturatedActive L n ∨
      ZetaRieszSaturatedCoreFloor.ReflectedPrefixSaturated L n) := by
    rintro (hs | hs)
    · have hb := hs.2.2
      rw [haD] at hb
      linarith
    · have hb := hs.2.2.2
      simp only [haD,ho,Nat.cast_one,Real.log_one,sub_zero,haL] at hb
      linarith
  have hprefix : ¬ZetaRieszSaturatedCoreFloor.TwoOuterPrimePrefix L n := by
    intro hh
    have hb := hh.2.2.1
    rw [balancedSeven_outer_empty h,Finset.card_empty] at hb
    omega
  have hbase := (ZetaRieszSevenPrimeReflection.costs_le_previous L y n).1
  have hnext := (ZetaRieszReflectedPrimeBounds.costs_le_previous L y n).1
  have hodd : n.primeFactors.card%2 = 1 := by rw [h.2.1]
  have hlast := (ZetaRieszIntersectingWindow.costs_le_previous hL y n hodd).1
  rw [if_neg (by omega : ¬n.primeFactors.card%2 = 0)] at hnext
  rw [ZetaRieszJoinedPrefixFloor.cutoffSaving,ZetaRieszSaturatedCoreFloor.floorCost,
    if_neg hsat,if_neg hprefix]
  apply max_eq_right
  linarith

/-- A NEW quarter of the optimized charge is removed, above all prefix
credits already included in the previous joined floor. -/
theorem balancedSeven_new_saving_ge_quarter {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (h : BalancedSeven L n) :
    (1/4 : ℝ)*ZetaRieszSevenPrimeReflection.floorCost L y n ≤ pairSaving L y n := by
  have hb := balancedSeven_savings_ge_quarter hL y h
  simpa only [balancedSeven_old_saving_eq_zero hL y h,zero_add] using hb

/-- The additional quarter saving survives summation with the actual
factorial/allocation weights, on ANY such subset of the unpaid labels. -/
theorem weighted_new_saving_ge_quarter (S T A : Finset ℕ) (N : ℕ)
    {L : ℝ} (hL : 0 < L) (y : ℝ) (hTS : T ⊆ S)
    (hT : ∀ n ∈ T, BalancedSeven L n) :
    (1/4 : ℝ)*(∑ n ∈ T, weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n) ≤
      ∑ n ∈ S.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
        weight A N n*pairSaving L y n := by
  calc
    _ ≤ ∑ n ∈ T, weight A N n*pairSaving L y n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hb := mul_le_mul_of_nonneg_left
        (balancedSeven_new_saving_ge_quarter hL y (hT n hn)) (weight_nonneg A N n)
      nlinarith only [hb]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro n hn
      exact Finset.mem_filter.mpr ⟨hTS hn,by have := (hT n hn).2.1; omega⟩)
      (fun n _ _ => mul_nonneg (weight_nonneg A N n) (pairSaving_nonneg L y n))

private theorem old_charge_sub_saving (L y : ℝ) (n : ℕ) :
    ZetaRieszSevenPrimeReflection.floorCost L y n-
      ZetaRieszJoinedPrefixFloor.cutoffSaving L y n =
      min (ZetaRieszSevenPrimeReflection.floorCost L y n)
        (ZetaRieszSaturatedCoreFloor.floorCost L y n) := by
  unfold ZetaRieszJoinedPrefixFloor.cutoffSaving
  rcases le_total (ZetaRieszSevenPrimeReflection.floorCost L y n)
    (ZetaRieszSaturatedCoreFloor.floorCost L y n) with h | h
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h,sub_zero]
  · rw [max_eq_left (sub_nonneg.mpr h),min_eq_right h]
    ring

/-- The new signed floor never spends an earlier saving again. It reduces
the remaining charge of the SAME observation, with its literal weight. -/
theorem residual_floor_with_saving (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 5 ≤ n.primeFactors.card)
    (hcut : 2*Real.log n ≤ 3*L) (hq : Real.log n < 4*(Real.log n-L))
    (htwo : 2*Real.log n ≤ 7*(Real.log n-L)) :
    let f := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max f 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n+
      weight A N n*ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      weight A N n*pairSaving L y n ≤ f := by
  dsimp only
  have hold := ZetaRieszJoinedPrefixFloor.residual_floor_with_saving A hL y N hc hcut hq htwo
  dsimp only at hold
  rw [pairSaving]
  split_ifs with h
  · have hnew := pair_floor_exact A L y N h
    dsimp only at hnew
    have he := old_charge_sub_saving L y n
    by_cases hb : pairCost L y n ≤ min (ZetaRieszSevenPrimeReflection.floorCost L y n)
        (ZetaRieszSaturatedCoreFloor.floorCost L y n)
    · rw [max_eq_left (sub_nonneg.mpr hb)]
      rw [← he]
      nlinarith only [hnew]
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hb)),mul_zero,add_zero]
      exact hold
  · simpa only [mul_zero,add_zero] using hold

/-- All counts and labels in a literal unpaid subset are assembled before
comparison. Existing prefix credits, favorable terms, and exact low-count
observations survive; the additional saving is uniformly nonnegative. -/
theorem eventually_core_subset_floor {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*((∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re)+
        ∑ n ∈ S.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+pairSaving L y n)) ≤
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hcut hN K y S hS
  dsimp only
  rw [Finset.sum_filter,← Finset.sum_add_distrib,← Complex.ofReal_pow,
    Complex.re_ofReal_mul,Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) _)
  apply Finset.sum_le_sum
  intro n hn
  split_ifs with hc
  · have hb := residual_floor_with_saving (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length_pos u N) y N
      (by omega : 5 ≤ n.primeFactors.card) (hcut K n (hS hn))
      (core_cutoff_quarter hu.le hN (hS hn))
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu.le hN (hS hn)).le
    dsimp only at hb
    nlinarith only [hb]
  · simp only [add_zero,le_refl]

open ZetaRieszPrimeCountFrequency ZetaRieszLeastOrderOverflow
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation
open ZetaRieszFourPrimeHead ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead
open ZetaRieszSevenCountTail

/-- Pair cancellation strengthens the CURRENT compensated joined floor after
all existing radial payments. The nonnegative G is charged only to the
unpaid rest; all former prefix credits and the unspent 1/64 supply are retained.
No floor constant or zero hypothesis is assumed, and -79/1000 is not claimed. -/
theorem eventually_joined_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let Gs := radialHeads S N P V L
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let B := wholeTail S N R
        let E := S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B)
        let W := ∑ n ∈ E, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-err j ≤
          ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,hbase⟩ :=
    ZetaRieszSevenCountTail.eventually_core_full_floor hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually
    (eventually_core_subset_floor hu hU)] with j hj hbound
  obtain ⟨v,hvb,hY,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ts := radialTail S N R
  let Ys := radialSupply N h v
  let B := wholeTail S N R
  let E := S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B)
  let W := ∑ n ∈ E, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+pairSaving L y n)
  have hE : E ⊆ coreBand u N (dyadicPrimeCount j) := Finset.sdiff_subset
  have hb := hbound (dyadicPrimeCount j) y E hE
  dsimp only at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ =>
    mul_nonneg (weight_nonneg A N n) (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n) (pairSaving_nonneg L y n)))
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  refine ⟨v,hvb,hY,hG,?_⟩
  change u^(N+1)*(W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-(r^N*C+e j) ≤ ((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re
  change u^(N+1)*(W+G) ≤ u^(N+1)*(∑ n ∈ E, f n).re at hb
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
            max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-((u : ℂ)^(N+1)*(ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j))).re ≤ e j at hbridge
  nlinarith only [hcore,hb,hbridge]

end
end RiemannGaussian.ZetaRieszPairChamberFloor
