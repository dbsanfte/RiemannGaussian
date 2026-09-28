/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszIntersectingWindow
import RiemannGaussian.ZetaRieszExtremePrimeProfile
import RiemannGaussian.ZetaRieszZeroParityCascade

/-!
# Reflected large primes reduce the signed coefficient cost

Only primes below the reflected Riesz cutoff enter its divisor response.
Counting those active primes sharpens both signed capacities without
changing the original integer, phase, allocation or factorial kernel.
Three reflected large primes force exact vanishing on the literal core
at every prime count at least five.
-/

namespace RiemannGaussian.ZetaRieszReflectedPrimeBounds
noncomputable section
open scoped BigOperators Classical
open ZetaRieszSignedSperner ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- Prime factors which can enter a divisor below the specified cutoff. -/
def activePrimes (D : ℝ) (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => Real.log p < D)

/-- The complementary prime factors include equality at the cutoff. -/
def outerPrimes (D : ℝ) (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => D ≤ Real.log p)

/-- The literal active cofactor, used only to bound the old coefficient. -/
def activePart (D : ℝ) (n : ℕ) : ℕ := ∏ p ∈ activePrimes D n, p

/-- The literal product of reflected large primes. -/
def outerPart (D : ℝ) (n : ℕ) : ℕ := ∏ p ∈ outerPrimes D n, p

/-- The two disjoint prime selections reconstruct the original label. -/
theorem factorization (D : ℝ) {n : ℕ} (hn : Squarefree n) :
    outerPart D n * activePart D n = n := by
  simpa [outerPart,activePart,outerPrimes,activePrimes,not_le] using
    (Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => D ≤ Real.log p) (fun p => p)).trans (Nat.prod_primeFactors_of_squarefree hn)

/-- No multiplicities or factors are lost in the active product. -/
theorem activePart_primeFactors (D : ℝ) (n : ℕ) :
    (activePart D n).primeFactors = activePrimes D n :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

/-- The outer product has exactly the selected genuine prime factors. -/
theorem outerPart_primeFactors (D : ℝ) (n : ℕ) :
    (outerPart D n).primeFactors = outerPrimes D n :=
  Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

/-- The count split is exact, including factors at the cutoff. -/
theorem count_split (D : ℝ) (n : ℕ) :
    (outerPrimes D n).card + (activePrimes D n).card = n.primeFactors.card := by
  simpa [outerPrimes,activePrimes,not_le] using
    Finset.card_filter_add_card_filter_not (s := n.primeFactors) (p := fun p => D ≤ Real.log p)

/-- The reflected profile forgets only inactive divisors, not their
original phase or their prime-count parity in the coefficient. -/
theorem riesz_eq_active (D : ℝ) {n : ℕ} (hn : Squarefree n) :
    VaughanLogAverage.riesz D n = VaughanLogAverage.riesz D (activePart D n) := by
  have hs : Squarefree (outerPart D n * activePart D n) := by rw [factorization D hn]; exact hn
  have he := ZetaRieszExtremePrimeProfile.riesz_mul_eq_of_extreme_rough hs (L := D) (by
    intro p hp
    rw [outerPart_primeFactors] at hp
    exact (Finset.mem_filter.mp hp).2)
  simpa only [factorization D hn] using he

/-- A nonempty active factor retains the original least prime exactly. -/
theorem activePart_minFac {D : ℝ} {n : ℕ} (hn : Squarefree n)
    (ha : (activePrimes D n).Nonempty) : (activePart D n).minFac = n.minFac := by
  have he := factorization D hn
  have hne : n ≠ 1 := by
    intro h
    simp [activePrimes,h] at ha
  have hane : activePart D n ≠ 1 := by
    intro h
    have hf := activePart_primeFactors D n
    rw [h] at hf
    rw [← hf] at ha
    simp at ha
  have hmin := (Nat.minFac_prime hne).mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  obtain ⟨p,hp⟩ := ha
  have hp' := Finset.mem_filter.mp hp
  have hle := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp'.1).two_le
    (Nat.dvd_of_mem_primeFactors hp'.1)
  have hlog : Real.log n.minFac < D := (Real.log_le_log
    (by exact_mod_cast (Nat.minFac_prime hne).pos : (0 : ℝ) < n.minFac)
    (by exact_mod_cast hle : (n.minFac : ℝ) ≤ p)).trans_lt hp'.2
  have hminA : n.minFac ∈ (activePart D n).primeFactors := by
    rw [activePart_primeFactors]
    exact Finset.mem_filter.mpr ⟨hmin,hlog⟩
  apply le_antisymm
  · exact Nat.minFac_le_of_dvd (Nat.minFac_prime hne).two_le (Nat.dvd_of_mem_primeFactors hminA)
  · have hd : activePart D n ∣ n :=
      (dvd_mul_left (activePart D n) (outerPart D n)).trans (dvd_of_eq he)
    exact Nat.minFac_le_of_dvd (Nat.minFac_prime hane).two_le
      ((Nat.minFac_dvd (activePart D n)).trans hd)

/-- Reflection, inactive-prime removal and the original parity commute
exactly. In particular the sign is not the parity of the active cofactor. -/
theorem coefficient_eq_active {L : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 2 ≤ n.primeFactors.card) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      -(Real.log n/L)*(-1 : ℝ)^n.primeFactors.card*
        VaughanLogAverage.riesz (Real.log n-L) (activePart (Real.log n-L) n) := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  have hr := VaughanLogAverage.riesz_reflection (Real.log n-L) hn hn1 hnp
  rw [sub_sub_cancel,ZetaRieszReflectedLinear.moebius_eq_primeCount hn] at hr
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one] at hr
  have hsupport : Squarefree n ∧ ¬ n.Prime := ⟨hn,hnp⟩
  simp only [SquarefreeVaughanLogSource.coefficient,if_pos hsupport,Complex.ofReal_re]
  rw [hr,riesz_eq_active (Real.log n-L) hn]
  ring

/-- The active count gives an independent signed interval for the
original coefficient. All removed factors still determine its parity. -/
theorem coefficient_active_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card)
    (ha : 2 ≤ (activePrimes (Real.log n-L) n).card) :
    -(Real.log n/L*Real.log n.minFac*
        (parityCapacity ((activePrimes (Real.log n-L) n).card-2) (n.primeFactors.card%2) : ℝ)) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        Real.log n/L*Real.log n.minFac*
          (parityCapacity ((activePrimes (Real.log n-L) n).card-2) (1-n.primeFactors.card%2) : ℝ) := by
  let D := Real.log n-L
  have hs : Squarefree (outerPart D n * activePart D n) := by rw [factorization D hn]; exact hn
  have h := riesz_bounds_minFac D hs.of_mul_right (by rw [activePart_primeFactors]; exact ha)
  have hapos : 0 < (activePrimes D n).card := by change 0 < (activePrimes (Real.log n-L) n).card; omega
  rw [activePart_minFac hn (Finset.card_pos.mp hapos),activePart_primeFactors] at h
  rw [coefficient_eq_active hn hc,neg_one_pow_eq_pow_mod_two]
  have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hlo := mul_le_mul_of_nonneg_left h.1 hscale
  have hhi := mul_le_mul_of_nonneg_left h.2 hscale
  rcases Nat.mod_two_eq_zero_or_one n.primeFactors.card with he | ho
  · simp only [he,pow_zero,mul_one,Nat.sub_zero]
    constructor <;> nlinarith only [hlo,hhi]
  · simp only [ho,pow_one,mul_neg,neg_mul,neg_neg,Nat.sub_self]
    constructor <;> nlinarith only [hlo,hhi]

/-- Beyond one quarter of the total log, at most three prime factors
can be reflected large. This is a deterministic log-budget bound. -/
theorem outer_count_le_three {D : ℝ} {n : ℕ} (hn : Squarefree n)
    (hD : Real.log n < 4*D) : (outerPrimes D n).card ≤ 3 := by
  have hD0 : 0 < D := by linarith [Real.log_natCast_nonneg n]
  have hs := Finset.sum_le_sum (s := outerPrimes D n) (fun p hp => (Finset.mem_filter.mp hp).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hsum : (∑ p ∈ outerPrimes D n, Real.log p) ≤ Real.log n := by
    rw [CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => Real.log_natCast_nonneg p)
  by_contra! h
  have hc : (4 : ℝ) ≤ (outerPrimes D n).card := by exact_mod_cast h
  nlinarith [mul_le_mul_of_nonneg_right hc hD0.le]

/-- Every high-count label in the reflected quarter regime has at
least two active primes, so the signed antichain bound applies directly. -/
theorem active_count_ge_two {D : ℝ} {n : ℕ} (hn : Squarefree n)
    (hc : 5 ≤ n.primeFactors.card) (hD : Real.log n < 4*D) :
    2 ≤ (activePrimes D n).card := by
  have := outer_count_le_three hn hD
  have := count_split D n
  omega

/-- Three reflected large primes leave a fully saturated composite
active cofactor. Both signs cancel exactly, before phase or norms. -/
theorem coefficient_eq_zero_of_three_outer {L : ℝ} {n : ℕ}
    (hn : Squarefree n) (hc : 5 ≤ n.primeFactors.card)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : 3 ≤ (outerPrimes (Real.log n-L) n).card) :
    SquarefreeVaughanLogSource.coefficient L n = 0 := by
  let D := Real.log n-L
  have hs : Squarefree (outerPart D n * activePart D n) := by rw [factorization D hn]; exact hn
  have hca := active_count_ge_two hn hc hD
  have ha1 : activePart D n ≠ 1 := by
    intro h
    rw [← activePart_primeFactors,h] at hca
    norm_num at hca
  have hap : ¬ (activePart D n).Prime := by
    intro h
    rw [← activePart_primeFactors,h.primeFactors,Finset.card_singleton] at hca
    omega
  have hsum := Finset.sum_le_sum (s := outerPrimes D n) (fun p hp => (Finset.mem_filter.mp hp).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [← outerPart_primeFactors,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_left] at hsum
  rw [outerPart_primeFactors] at hsum
  have hlog : Real.log n = Real.log (outerPart D n)+Real.log (activePart D n) := by
    conv_lhs => rw [← factorization D hn]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hs.of_mul_left.ne_zero) (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hD0 : 0 < D := by dsimp [D]; linarith [Real.log_natCast_nonneg n]
  have hoR : (3 : ℝ) ≤ (outerPrimes D n).card := by exact_mod_cast ho
  have haD : Real.log (activePart D n) ≤ D := by
    nlinarith [mul_le_mul_of_nonneg_right hoR hD0.le]
  have hz := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs.of_mul_right ha1 hap haD
  have hreal := coefficient_eq_active hn (by omega : 2 ≤ n.primeFactors.card) (L := L)
  rw [hz,mul_zero] at hreal
  apply Complex.ext hreal
  exact ZetaRieszCosineCarrier.coefficient_im_eq_zero L n

/-- The two signed capacities depend on the active count, but their
orientation still uses the complete label's parity. -/
def activeCapacity (k o b : ℕ) : ℕ :=
  if 3 ≤ o then 0 else parityCapacity (k-o-2) (if b = 0 then k%2 else 1-k%2)

/-- Exact capacities for one and two reflected large primes. The
third-large-prime case is zero by the saturation theorem, not a norm. -/
theorem activeCapacity_table :
    (activeCapacity 7 1 0,activeCapacity 7 1 1) = (4,6) ∧
    (activeCapacity 7 2 0,activeCapacity 7 2 1) = (3,3) ∧
    (activeCapacity 8 1 0,activeCapacity 8 1 1) = (10,10) ∧
    (activeCapacity 8 2 0,activeCapacity 8 2 1) = (6,4) ∧
    (activeCapacity 9 1 0,activeCapacity 9 1 1) = (20,15) ∧
    (activeCapacity 9 2 0,activeCapacity 9 2 1) = (10,10) ∧
    (activeCapacity 10 1 0,activeCapacity 10 1 1) = (35,35) ∧
    (activeCapacity 10 2 0,activeCapacity 10 2 1) = (15,20) := by
  decide +kernel

/-- The active-prime arithmetic allowance is zero on the exactly
vanishing sector and outside squarefree high-count support. -/
def activeAllowance (L : ℝ) (n b : ℕ) : ℝ :=
  if Squarefree n ∧ 5 ≤ n.primeFactors.card then
    Real.log n/L*Real.log n.minFac*
      (activeCapacity n.primeFactors.card (outerPrimes (Real.log n-L) n).card b : ℝ)
  else 0

/-- All active capacities are nonnegative numerical charges. -/
theorem activeAllowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) :
    0 ≤ activeAllowance L n b := by
  unfold activeAllowance
  split_ifs
  · positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]
  · rfl

/-- Both independent signed bounds, with the exact third-large-prime
zero and all original parity data retained. -/
theorem coefficient_activeAllowance_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 5 ≤ n.primeFactors.card) (hD : Real.log n < 4*(Real.log n-L)) :
    -activeAllowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ activeAllowance L n 1 := by
  by_cases hn : Squarefree n
  · have hs : Squarefree n ∧ 5 ≤ n.primeFactors.card := ⟨hn,hc⟩
    by_cases ho : 3 ≤ (outerPrimes (Real.log n-L) n).card
    · rw [coefficient_eq_zero_of_three_outer hn hc hD ho]
      simp only [activeAllowance,if_pos hs,activeCapacity,if_pos ho,Nat.cast_zero,
        mul_zero,Complex.zero_re,neg_zero,le_refl,and_self]
    · have ha := active_count_ge_two hn hc hD
      have h := coefficient_active_bounds hL hn (by omega) ha
      have he : (activePrimes (Real.log n-L) n).card =
          n.primeFactors.card-(outerPrimes (Real.log n-L) n).card := by
        have := count_split (Real.log n-L) n
        omega
      rw [he] at h
      simpa only [activeAllowance,if_pos hs,activeCapacity,if_neg ho,ite_true,
        ite_false,show ¬ (1 : ℕ) = 0 by omega] using h
  · simp only [activeAllowance,SquarefreeVaughanLogSource.coefficient,hn,false_and,
      if_false,Complex.zero_re,neg_zero,le_refl,and_self]

/-- One reflected large prime improves both seven-prime coefficient
costs from the previous interval [-5,10] to [-4,6]. -/
theorem coefficient_seven_one_outer {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    -(4*(Real.log n/L)*Real.log n.minFac) ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ 6*(Real.log n/L)*Real.log n.minFac := by
  have h := coefficient_activeAllowance_bounds hL (by omega : 5 ≤ n.primeFactors.card) hD
  have he := activeCapacity_table.1
  have h₀ : activeCapacity 7 1 0 = 4 := congrArg Prod.fst he
  have h₁ : activeCapacity 7 1 1 = 6 := congrArg Prod.snd he
  simp only [activeAllowance,hn,hc,show 5 ≤ (7 : ℕ) by omega,and_self,ite_true,ho,h₀,h₁,
    Nat.cast_ofNat] at h
  constructor <;> nlinarith only [h.1,h.2]

/-- Two reflected large primes leave the symmetric capacity three for
the same seven-prime coefficient, with no incidence averaging. -/
theorem coefficient_seven_two_outer {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    -(3*(Real.log n/L)*Real.log n.minFac) ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ 3*(Real.log n/L)*Real.log n.minFac := by
  have h := coefficient_activeAllowance_bounds hL (by omega : 5 ≤ n.primeFactors.card) hD
  have he := activeCapacity_table.2.1
  have h₀ : activeCapacity 7 2 0 = 3 := congrArg Prod.fst he
  have h₁ : activeCapacity 7 2 1 = 3 := congrArg Prod.snd he
  simp only [activeAllowance,hn,hc,show 5 ≤ (7 : ℕ) by omega,and_self,ite_true,ho,h₀,h₁,
    Nat.cast_ofNat] at h
  constructor <;> nlinarith only [h.1,h.2]

/-- Keep the previously proved even/odd divisor-window costs available;
the new bound is intersected with them, never substituted at a larger cost. -/
def previousAllowance (L : ℝ) (n b : ℕ) : ℝ :=
  if n.primeFactors.card%2 = 0 then ZetaRieszComplementWindow.allowance L n b
  else ZetaRieszIntersectingWindow.allowance L n b

/-- The earlier higher-count costs are nonnegative in both parities. -/
theorem previousAllowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) :
    0 ≤ previousAllowance L n b := by
  unfold previousAllowance
  split_ifs
  · exact ZetaRieszComplementWindow.allowance_nonneg hL n b
  · exact ZetaRieszIntersectingWindow.allowance_nonneg hL n b

private theorem coefficient_previous_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 2 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L) :
    -previousAllowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ previousAllowance L n 1 := by
  by_cases he : n.primeFactors.card%2 = 0
  · simpa only [previousAllowance,if_pos he] using
      ZetaRieszComplementWindow.coefficient_allowance_bounds hL hc he hcut
  · have ho : n.primeFactors.card%2 = 1 := by omega
    simpa only [previousAllowance,if_neg he] using
      ZetaRieszIntersectingWindow.coefficient_allowance_bounds hL hc ho hcut

/-- A pointwise intersection of two proved intervals for the same
literal coefficient; this is not an added supply or a changed carrier. -/
def allowance (L : ℝ) (n b : ℕ) : ℝ :=
  min (previousAllowance L n b) (activeAllowance L n b)

/-- The refined charge never increases either previous signed cost. -/
theorem allowance_le_previous (L : ℝ) (n b : ℕ) :
    allowance L n b ≤ previousAllowance L n b := min_le_left _ _

/-- Both refined coefficient charges are nonnegative. -/
theorem allowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) :
    0 ≤ allowance L n b := le_min (previousAllowance_nonneg hL n b) (activeAllowance_nonneg hL n b)

/-- The new interval combines the actual reflected cutoff with the
already proved parity/correlation estimates on the same coefficient. -/
theorem coefficient_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hD : Real.log n < 4*(Real.log n-L)) :
    -allowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ allowance L n 1 := by
  have h := coefficient_previous_bounds hL (by omega : 2 ≤ n.primeFactors.card) hcut
  have ha := coefficient_activeAllowance_bounds hL hc hD
  constructor
  · unfold allowance
    by_cases hle : previousAllowance L n 0 ≤ activeAllowance L n 0
    · simpa only [min_eq_left hle] using h.1
    · simpa only [min_eq_right (le_of_not_ge hle)] using ha.1
  · exact le_min h.2 ha.2

/-- The original positive and negative cosine orientations keep their
different signed coefficient charges. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  allowance L n 0*max (Real.cos (y*Real.log n)) 0+
    allowance L n 1*max (-Real.cos (y*Real.log n)) 0

/-- The upper comparison uses the opposite charges on the same phase. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  allowance L n 1*max (Real.cos (y*Real.log n)) 0+
    allowance L n 0*max (-Real.cos (y*Real.log n)) 0

/-- Both observations cost no more than their earlier parity-specific
estimate, at every actual height and prime label. -/
theorem costs_le_previous (L y : ℝ) (n : ℕ) :
    floorCost L y n ≤
      (if n.primeFactors.card%2 = 0 then ZetaRieszComplementWindow.floorCost L y n
        else ZetaRieszIntersectingWindow.floorCost L y n) ∧
    ceilingCost L y n ≤
      (if n.primeFactors.card%2 = 0 then ZetaRieszComplementWindow.ceilingCost L y n
        else ZetaRieszIntersectingWindow.ceilingCost L y n) := by
  have h₀ := allowance_le_previous L n 0
  have h₁ := allowance_le_previous L n 1
  by_cases he : n.primeFactors.card%2 = 0
  · simp only [previousAllowance,if_pos he] at h₀ h₁
    simp only [if_pos he,floorCost,ceilingCost,ZetaRieszComplementWindow.floorCost,
      ZetaRieszComplementWindow.ceilingCost]
    constructor <;> gcongr
  · simp only [previousAllowance,if_neg he] at h₀ h₁
    simp only [if_neg he,floorCost,ceilingCost,ZetaRieszIntersectingWindow.floorCost,
      ZetaRieszIntersectingWindow.ceilingCost]
    constructor <;> gcongr

/-- Both exact residual-atom estimates retain the full factorial,
allocation and product phase. -/
theorem residual_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hD : Real.log n < 4*(Real.log n-L)) :
    -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*ceilingCost L y n := by
  have hh := coefficient_bounds hL hc hcut hD
  rw [re_residual_atom]
  have hw := weight_nonneg A N n
  suffices hs : -floorCost L y n ≤
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤ ceilingCost L y n by
    exact ⟨by simpa only [mul_neg] using mul_le_mul_of_nonneg_left hs.1 hw,
      mul_le_mul_of_nonneg_left hs.2 hw⟩
  by_cases hx : 0 ≤ Real.cos (y*Real.log n)
  · have hlo := mul_le_mul_of_nonneg_right hh.1 hx
    have hhi := mul_le_mul_of_nonneg_right hh.2 hx
    simp only [floorCost,ceilingCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),mul_zero,add_zero]
    constructor <;> nlinarith only [hlo,hhi]
  · have hx' := le_of_not_ge hx
    have hlo := mul_le_mul_of_nonpos_right hh.2 hx'
    have hhi := mul_le_mul_of_nonpos_right hh.1 hx'
    simp only [floorCost,ceilingCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),mul_zero,zero_add]
    constructor <;> nlinarith only [hlo,hhi]

/-- Every favorable selected observation stays in its original signed
comparison; the smaller charge does not spend any supply twice. -/
theorem residual_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hD : Real.log n < 4*(Real.log n-L)) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  dsimp only
  have hh := residual_bounds A hL y N hc hcut hD
  have hl : 0 ≤ weight A N n*floorCost L y n := by
    unfold floorCost
    positivity [weight_nonneg A N n,allowance_nonneg hL n 0,allowance_nonneg hL n 1]
  have hu : 0 ≤ weight A N n*ceilingCost L y n := by
    unfold ceilingCost
    positivity [weight_nonneg A N n,allowance_nonneg hL n 0,allowance_nonneg hL n 1]
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hl]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hu]

open Filter Topology ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- The literal core lies strictly beyond the reflected quarter edge;
the moving length is not replaced by a limiting constant. -/
theorem core_cutoff_quarter {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) :
    Real.log n < 4*(Real.log n-SquarefreeVaughanLogSource.length u N) := by
  have hg := ZetaRieszZeroParityCascade.core_support_gap hu hN hn
  have hlo := (Finset.mem_filter.mp hn).2.1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 0 < Real.log n := by linarith
  have hfrac : SquarefreeVaughanLogSource.length u N/Real.log n < (18/25 : ℝ) := by linarith
  have hm := (div_lt_iff₀ ht).mp hfrac
  linarith

/-- Three reflected large primes cost exactly zero throughout the
literal core, uniformly in height and with every finite mask intact. -/
theorem core_coefficient_eq_zero {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hc : 5 ≤ n.primeFactors.card)
    (ho : 3 ≤ (outerPrimes (Real.log n-SquarefreeVaughanLogSource.length u N) n).card) :
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n = 0 := by
  rw [residualCoefficient,coefficient_eq_zero_of_three_outer hs hc (core_cutoff_quarter hu hN hn) ho,mul_zero]

/-- The exact deletion also covers nonsquarefree labels through their
already zero coefficient; no new support premise is needed in a sum. -/
theorem core_residual_eq_zero_of_three_outer {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (hc : 5 ≤ n.primeFactors.card)
    (ho : 3 ≤ (outerPrimes (Real.log n-SquarefreeVaughanLogSource.length u N) n).card) :
    residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n = 0 := by
  by_cases hs : Squarefree n
  · exact core_coefficient_eq_zero hu hN hn hs hc ho
  · simp only [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs,false_and,if_false,mul_zero]

/-- Every nonzero high-count label left in any actual core rest has at
most two reflected large primes. No prime-density claim is used. -/
theorem nonzero_core_outer_le_two {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) (hc : 5 ≤ n.primeFactors.card)
    (hz : residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n ≠ 0) :
    (outerPrimes (Real.log n-SquarefreeVaughanLogSource.length u N) n).card ≤ 2 := by
  by_contra! h
  exact hz (core_residual_eq_zero_of_three_outer hu hN hn hc h)

/-- Exact deletion on every selected literal core sum, including the
full phase and every factorial/allocation weight. Lower counts stay intact. -/
theorem core_sum_eq_outer_filter {u : ℝ} (hu : 1/2 ≤ u) {N K : ℕ}
    (hN : 2 ≤ N) (y : ℝ) (S : Finset ℕ) (hS : S ⊆ coreBand u N K) :
    let f := fun n => residualCoefficient (intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, f n) = ∑ n ∈ S.filter (fun n : ℕ => n.primeFactors.card < 5 ∨
      (outerPrimes (Real.log n-SquarefreeVaughanLogSource.length u N) n).card < 3), f n := by
  dsimp only
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with h
  · rfl
  · have h' := not_or.mp h
    rw [core_residual_eq_zero_of_three_outer hu hN (hS hn)
      (Nat.le_of_not_gt h'.1) (Nat.le_of_not_gt h'.2),zero_mul]

/-- Every higher-count subset of the actual core inherits both improved
signed inequalities. This includes any unpaid rest from earlier ledgers;
all other counts and every favorable observation are retained exactly. -/
theorem eventually_core_subset_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
          ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
          u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hcut hN K y S hS
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hsum :
      (∑ n ∈ S, if 7 ≤ n.primeFactors.card then max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        (∑ n ∈ S, f n).re ∧
      (∑ n ∈ S, f n).re ≤
        ∑ n ∈ S, if 7 ≤ n.primeFactors.card then min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re := by
    rw [Complex.re_sum]
    constructor
    · apply Finset.sum_le_sum
      intro n hn
      split_ifs with hc
      · exact (residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N
          (by omega) (hcut K n (hS hn)) (core_cutoff_quarter hu.le hN (hS hn))).1
      · exact le_rfl
    · apply Finset.sum_le_sum
      intro n hn
      split_ifs with hc
      · exact (residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N
          (by omega) (hcut K n (hS hn)) (core_cutoff_quarter hu.le hN (hS hn))).2
      · exact le_rfl
  have hlo := mul_le_mul_of_nonneg_left hsum.1 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  have hhi := mul_le_mul_of_nonneg_left hsum.2 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hlo hhi

end
end RiemannGaussian.ZetaRieszReflectedPrimeBounds
