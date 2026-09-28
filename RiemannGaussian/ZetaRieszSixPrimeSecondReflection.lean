/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixPrimeCentered

/-!
# A second reflection reduces both whole six-prime charges

Only the divisor response inside the original coefficient is reflected.
The original integer, phase, factorial allocation and complementary sum
remain unchanged. The resulting asymmetric intervals are spent directly
in the lower and upper bounds on any unpaid core subset.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeSecondReflection
noncomputable section
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszSignedSperner
open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- Reflect the five-prime active cofactor at its own total logarithm. -/
def secondCutoff (L : ℝ) (n : ℕ) : ℝ :=
  Real.log (activePart (Real.log n-L) n)-(Real.log n-L)

/-- The actual factors still active after the second reflection. -/
def secondActive (L : ℝ) (n : ℕ) : ℕ :=
  activePart (secondCutoff L n) (activePart (Real.log n-L) n)

/-- The count of actual cofactor primes removed at the second cutoff. -/
def secondCount (L : ℝ) (n : ℕ) : ℕ :=
  (outerPrimes (secondCutoff L n) (activePart (Real.log n-L) n)).card

private theorem active_squarefree (D : ℝ) {n : ℕ} (hs : Squarefree n) :
    Squarefree (activePart D n) := by
  have h : Squarefree (outerPart D n*activePart D n) := by
    rw [factorization D hs]
    exact hs
  exact h.of_mul_right

private theorem first_count {L : ℝ} {n : ℕ} (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    (activePart (Real.log n-L) n).primeFactors.card = 5 := by
  have h := count_split (Real.log n-L) n
  rw [ho,hc,← activePart_primeFactors] at h
  omega

/-- The odd active-cofactor reflection reverses the old minus sign.
No phase or factorial order is changed. -/
theorem coefficient_eq_twice_active {L : ℝ} {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    (SquarefreeVaughanLogSource.coefficient L n).re =
      (Real.log n/L)*VaughanLogAverage.riesz (secondCutoff L n) (secondActive L n) := by
  have ha := active_squarefree (Real.log n-L) hs
  have hac := first_count hc ho
  have ha1 : activePart (Real.log n-L) n ≠ 1 := by intro h; simp [h] at hac
  have hap : ¬ (activePart (Real.log n-L) n).Prime := by intro h; simp [h.primeFactors] at hac
  have hr := VaughanLogAverage.riesz_reflection (Real.log n-L) ha ha1 hap
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount ha,hac] at hr
  norm_num at hr
  have hr' : VaughanLogAverage.riesz (secondCutoff L n) (secondActive L n) =
      -VaughanLogAverage.riesz (Real.log n-L) (activePart (Real.log n-L) n) := by
    rw [secondActive,← riesz_eq_active (secondCutoff L n) ha]
    exact hr
  rw [coefficient_eq_active hs (by omega),hc,hr']
  norm_num only [show (-1 : ℝ)^6 = 1 by norm_num,mul_one]
  ring


/-- The second removal keeps the original least prime whenever at least
two factors remain. All counts and squarefreeness are derived literally. -/
theorem second_active_data {L : ℝ} {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n ≤ 3) :
    Squarefree (secondActive L n) ∧
      (secondActive L n).primeFactors.card = 5-secondCount L n ∧
      (secondActive L n).minFac = n.minFac := by
  have ha := active_squarefree (Real.log n-L) hs
  have hac := first_count hc ho
  have hc₂ := count_split (secondCutoff L n) (activePart (Real.log n-L) n)
  rw [hac,← activePart_primeFactors] at hc₂
  change secondCount L n+(secondActive L n).primeFactors.card = 5 at hc₂
  have hne₂ : (activePrimes (secondCutoff L n) (activePart (Real.log n-L) n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [← activePart_primeFactors]
    change 0 < (secondActive L n).primeFactors.card
    omega
  have hne₁ : (activePrimes (Real.log n-L) n).Nonempty := by
    apply Finset.card_pos.mp
    rw [← activePart_primeFactors,hac]
    norm_num
  refine ⟨active_squarefree _ ha,by omega,?_⟩
  exact (activePart_minFac ha hne₂).trans (activePart_minFac hs hne₁)

/-- The exact second active count gives a new asymmetric interval for
the original six-prime coefficient. -/
theorem coefficient_inner_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n ≤ 3) :
    -((Real.log n/L)*Real.log n.minFac*
      (parityCapacity (3-secondCount L n) 1 : ℝ)) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/L)*Real.log n.minFac*
      (parityCapacity (3-secondCount L n) 0 : ℝ) := by
  obtain ⟨hsa,hca,hma⟩ := second_active_data hs hc ho hi
  have hh := riesz_bounds_minFac (secondCutoff L n) hsa (by omega)
  rw [hca,hma,show 5-secondCount L n-2 = 3-secondCount L n by omega] at hh
  rw [coefficient_eq_twice_active hs hc ho]
  have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  exact ⟨by simpa only [mul_neg,mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hscale,
    by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hscale⟩

/-- Removing one additional cofactor prime improves [-3,3] to [-2,1]
in original least-prime units, without changing the actual atom. -/
theorem coefficient_one_inner {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n = 1) :
    -(2*(Real.log n/L*Real.log n.minFac)) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ Real.log n/L*Real.log n.minFac := by
  have hh := coefficient_inner_bounds hL hs hc ho (by omega)
  have hcap : parityCapacity 2 1 = 2 ∧ parityCapacity 2 0 = 1 := by decide +kernel
  simpa [hi,hcap.1,hcap.2,mul_comm] using hh

/-- Two additional inactive factors leave the exact interval [-1,1]. -/
theorem coefficient_two_inner {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n = 2) :
    -(Real.log n/L*Real.log n.minFac) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ Real.log n/L*Real.log n.minFac := by
  have hh := coefficient_inner_bounds hL hs hc ho (by omega)
  have hcap : parityCapacity 1 1 = 1 ∧ parityCapacity 1 0 = 1 := by decide +kernel
  simpa [hi,hcap.1,hcap.2] using hh

/-- Three additional inactive factors force the original coefficient
nonnegative, so one adverse phase direction has zero cost. -/
theorem coefficient_three_inner {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n = 3) :
    0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ Real.log n/L*Real.log n.minFac := by
  have hh := coefficient_inner_bounds hL hs hc ho (by omega)
  have hcap : parityCapacity 0 1 = 0 ∧ parityCapacity 0 0 = 1 := by decide +kernel
  simpa [hi,hcap.1,hcap.2] using hh

/-- One second-reflected prime leaves a four-prime response. In its outer
thirds both coefficient costs are one least-prime unit. -/
theorem coefficient_inner_one_thirds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hi : secondCount L n = 1)
    (hthird : 3*secondCutoff L n ≤ Real.log (secondActive L n) ∨
      2*Real.log (secondActive L n) ≤ 3*secondCutoff L n) :
    -((Real.log n/L)*Real.log n.minFac) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re := by
  obtain ⟨hsa,hca,hma⟩ := second_active_data hs hc ho (by omega)
  rw [hi] at hca
  norm_num at hca
  have hb : -Real.log (secondActive L n).minFac ≤
      VaughanLogAverage.riesz (secondCutoff L n) (secondActive L n) := by
    rcases hthird with h | h
    · exact ZetaRieszSixPrimeReflection.riesz_four_lower_third_ge hsa hca h
    · exact ZetaRieszSixPrimeReflection.riesz_four_upper_two_thirds_ge hsa hca h
  rw [hma] at hb
  rw [coefficient_eq_twice_active hs hc ho]
  simpa only [mul_neg] using mul_le_mul_of_nonneg_left hb
    (div_nonneg (Real.log_natCast_nonneg n) hL.le)

/-- Negative coefficient units after the inner reflection, with the
four-factor outer-third improvement retained. -/
def lowerUnits (L : ℝ) (n : ℕ) : ℝ :=
  if secondCount L n = 1 then
    if 3*secondCutoff L n ≤ Real.log (secondActive L n) ∨
        2*Real.log (secondActive L n) ≤ 3*secondCutoff L n then 1 else 2
  else if secondCount L n = 2 then 1
  else if secondCount L n = 3 then 0 else 3

/-- Every nonempty second deletion leaving two to four factors reduces
the positive coefficient allowance to one original least-prime unit. -/
def upperUnits (L : ℝ) (n : ℕ) : ℝ :=
  if secondCount L n = 1 ∨ secondCount L n = 2 ∨ secondCount L n = 3 then 1 else 3

/-- Both new one-sided capacities lie inside the preceding three units. -/
theorem units_bounds (L : ℝ) (n : ℕ) :
    0 ≤ lowerUnits L n ∧ lowerUnits L n ≤ 3 ∧
      0 ≤ upperUnits L n ∧ upperUnits L n ≤ 3 := by
  unfold lowerUnits upperUnits
  split_ifs <;> norm_num

/-- The capacities bound the original coefficient in every inner-count
case; unsupported cases keep the previous charge rather than disappearing. -/
theorem coefficient_units_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    -((Real.log n/L*Real.log n.minFac)*lowerUnits L n) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re ∧
    (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/L*Real.log n.minFac)*upperUnits L n := by
  have h0 : parityCapacity 0 1 = 0 ∧ parityCapacity 0 0 = 1 := by decide +kernel
  have h1 : parityCapacity 1 1 = 1 ∧ parityCapacity 1 0 = 1 := by decide +kernel
  have h2 : parityCapacity 2 1 = 2 ∧ parityCapacity 2 0 = 1 := by decide +kernel
  by_cases hi1 : secondCount L n = 1
  · have hh := coefficient_inner_bounds hL hs hc ho (by omega)
    norm_num only [hi1,Nat.reduceSub,h2.1,h2.2,Nat.cast_ofNat,Nat.cast_one,mul_one] at hh
    simp only [lowerUnits,upperUnits,hi1,ite_true,true_or]
    split_ifs with ht
    · simpa only [mul_one] using And.intro (coefficient_inner_one_thirds hL hs hc ho hi1 ht) hh.2
    · simpa only [mul_one] using hh
  by_cases hi2 : secondCount L n = 2
  · have hh := coefficient_inner_bounds hL hs hc ho (by omega)
    simpa [lowerUnits,upperUnits,hi1,hi2,h1.1,h1.2] using hh
  by_cases hi3 : secondCount L n = 3
  · have hh := coefficient_inner_bounds hL hs hc ho (by omega)
    simpa [lowerUnits,upperUnits,hi1,hi2,hi3,h0.1,h0.2] using hh
  · have hh := ZetaRieszSixPrimeReflection.coefficient_six_one_outer hL hs hc hD ho
    simpa [lowerUnits,upperUnits,hi1,hi2,hi3,mul_comm] using hh

/-- The previous central cancellation amplitude before its phase cost. -/
def centerAmplitude (L : ℝ) (n : ℕ) : ℝ :=
  (Real.log n/L)*min (3*Real.log n.minFac)
    (4*|2*(Real.log n-L)-Real.log (activePart (Real.log n-L) n)|)

/-- Clip the negative allowance against the earlier midpoint estimate. -/
def lowerAmplitude (L : ℝ) (n : ℕ) : ℝ :=
  min (centerAmplitude L n) ((Real.log n/L*Real.log n.minFac)*lowerUnits L n)

/-- Clip the positive allowance independently, retaining its smaller sign. -/
def upperAmplitude (L : ℝ) (n : ℕ) : ℝ :=
  min (centerAmplitude L n) ((Real.log n/L*Real.log n.minFac)*upperUnits L n)

/-- The exact two-stage interval and the old midpoint cancellation hold
simultaneously for the same literal coefficient. -/
theorem coefficient_clipped_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    -lowerAmplitude L n ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ upperAmplitude L n := by
  have hc' := abs_le.mp (ZetaRieszSixPrimeCentered.coefficient_six_one_outer_centered hL hs hc hD ho)
  have hu := coefficient_units_bounds hL hs hc hD ho
  have hlo : -(SquarefreeVaughanLogSource.coefficient L n).re ≤ lowerAmplitude L n :=
    le_min (by exact neg_le.mpr hc'.1) (by linarith only [hu.1])
  exact ⟨by linarith only [hlo],le_min hc'.2 hu.2⟩

/-- The clipped capacities are nonnegative and never exceed the old
central amplitude, independently of coefficient-support assumptions. -/
theorem amplitude_bounds {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ lowerAmplitude L n ∧ lowerAmplitude L n ≤ centerAmplitude L n ∧
      0 ≤ upperAmplitude L n ∧ upperAmplitude L n ≤ centerAmplitude L n := by
  have hu := units_bounds L n
  have hbase : 0 ≤ Real.log n/L*Real.log n.minFac := by
    positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]
  have hcenter : 0 ≤ centerAmplitude L n := by
    unfold centerAmplitude
    positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]
  exact ⟨le_min hcenter (mul_nonneg hbase hu.1),min_le_left _ _,
    le_min hcenter (mul_nonneg hbase hu.2.2.1),min_le_left _ _⟩

/-- The adverse lower phase chooses the negative and positive coefficient
allowances separately, keeping the original cosine. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  if (outerPrimes (Real.log n-L) n).card = 1 then
    lowerAmplitude L n*max (Real.cos (y*Real.log n)) 0+
      upperAmplitude L n*max (-Real.cos (y*Real.log n)) 0
  else ZetaRieszSixPrimeCentered.centeredSixCost L y n

/-- The upper cost reverses the two signed coefficient allowances. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  if (outerPrimes (Real.log n-L) n).card = 1 then
    upperAmplitude L n*max (Real.cos (y*Real.log n)) 0+
      lowerAmplitude L n*max (-Real.cos (y*Real.log n)) 0
  else ZetaRieszSixPrimeCentered.centeredSixCost L y n

private theorem centered_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ ZetaRieszSixPrimeCentered.centeredSixCost L y n := by
  unfold ZetaRieszSixPrimeCentered.centeredSixCost
    ZetaRieszSixPrimeReflection.reflectedSixCost ZetaRieszSixPrimeReflection.twoOuterCost
  split_ifs <;> positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]

/-- Both new directed costs are nonnegative and no larger than the
previous charge on the same label, phase and cutoff. -/
theorem costs_le_centered {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ floorCost L y n ∧
      floorCost L y n ≤ ZetaRieszSixPrimeCentered.centeredSixCost L y n ∧
      0 ≤ ceilingCost L y n ∧
      ceilingCost L y n ≤ ZetaRieszSixPrimeCentered.centeredSixCost L y n := by
  by_cases ho : (outerPrimes (Real.log n-L) n).card = 1
  · have ha := amplitude_bounds hL n
    have hp := le_max_right (Real.cos (y*Real.log n)) 0
    have hn := le_max_right (-Real.cos (y*Real.log n)) 0
    have hLp := mul_le_mul_of_nonneg_right ha.2.1 hp
    have hLn := mul_le_mul_of_nonneg_right ha.2.1 hn
    have hUp := mul_le_mul_of_nonneg_right ha.2.2.2 hp
    have hUn := mul_le_mul_of_nonneg_right ha.2.2.2 hn
    simp only [floorCost,ceilingCost,ZetaRieszSixPrimeCentered.centeredSixCost,if_pos ho]
    change 0 ≤ lowerAmplitude L n*max (Real.cos (y*Real.log n)) 0+
        upperAmplitude L n*max (-Real.cos (y*Real.log n)) 0 ∧
      lowerAmplitude L n*max (Real.cos (y*Real.log n)) 0+
        upperAmplitude L n*max (-Real.cos (y*Real.log n)) 0 ≤
        centerAmplitude L n*(max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0) ∧
      0 ≤ upperAmplitude L n*max (Real.cos (y*Real.log n)) 0+
        lowerAmplitude L n*max (-Real.cos (y*Real.log n)) 0 ∧
      upperAmplitude L n*max (Real.cos (y*Real.log n)) 0+
        lowerAmplitude L n*max (-Real.cos (y*Real.log n)) 0 ≤
        centerAmplitude L n*(max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0)
    exact ⟨add_nonneg (mul_nonneg ha.1 hp) (mul_nonneg ha.2.2.1 hn),
      by nlinarith only [hLp,hUn],
      add_nonneg (mul_nonneg ha.2.2.1 hp) (mul_nonneg ha.1 hn),
      by nlinarith only [hUp,hLn]⟩
  · simp only [floorCost,ceilingCost,if_neg ho,le_refl,and_true]
    exact ⟨centered_nonneg hL y n,True.intro,centered_nonneg hL y n⟩

/-- The same original residual atom keeps every favorable observation,
while its adverse sign pays only the new asymmetric charge. -/
theorem residual_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : 1 ≤ (outerPrimes (Real.log n-L) n).card) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  by_cases ho₁ : (outerPrimes (Real.log n-L) n).card = 1
  · have hn1 : n ≠ 1 := by intro h; simp [h] at hc
    have ht : 0 < Real.log n := Real.log_pos (by
      exact_mod_cast (show 1 < n by have := hs.ne_zero; omega))
    have hb := coefficient_clipped_bounds hL hs hc (by linarith only [ht,hD]) ho₁
    have hw := weight_nonneg A N n
    have costs := costs_le_centered hL y n
    have raw : -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
          weight A N n*ceilingCost L y n := by
      rw [re_residual_atom]
      suffices hh : -floorCost L y n ≤
          (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
          (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤
            ceilingCost L y n by
        exact ⟨by simpa only [mul_neg,mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hw,
          by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hw⟩
      by_cases hp : 0 ≤ Real.cos (y*Real.log n)
      · have hl := mul_le_mul_of_nonneg_right hb.1 hp
        have hu := mul_le_mul_of_nonneg_right hb.2 hp
        simp only [floorCost,ceilingCost,if_pos ho₁,max_eq_left hp,
          max_eq_right (neg_nonpos.mpr hp),mul_zero,add_zero]
        constructor <;> nlinarith only [hl,hu]
      · have hp' := le_of_not_ge hp
        have hl := mul_le_mul_of_nonpos_right hb.2 hp'
        have hu := mul_le_mul_of_nonpos_right hb.1 hp'
        simp only [floorCost,ceilingCost,if_pos ho₁,max_eq_right hp',
          max_eq_left (neg_nonneg.mpr hp'),mul_zero,zero_add]
        constructor <;> nlinarith only [hl,hu]
    dsimp only
    have hln := mul_nonneg hw costs.1
    have hun := mul_nonneg hw costs.2.2.1
    by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    · rw [max_eq_left hv,min_eq_right hv]
      constructor <;> linarith only [raw.2,hln]
    · have hv' := le_of_not_ge hv
      rw [max_eq_right hv',min_eq_left hv']
      constructor <;> linarith only [raw.1,hun]
  · simpa only [floorCost,ceilingCost,if_neg ho₁] using
      ZetaRieszSixPrimeCentered.residual_centered_retained_bounds A hL y N hs hc hD ho

open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- The improved signed costs apply jointly to any exact unpaid core
subset. All other integers retain their full original signed atom. -/
theorem core_subset_bounds {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (y : ℝ) (S : Finset ℕ) (hS : S ⊆ coreBand u N K) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
        u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
          1 ≤ (outerPrimes (Real.log n-L) n).card then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hp (n : ℕ) (hn : n ∈ S) (hs : Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card) :=
    residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N hs.1 hs.2.1
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu hN (hS hn)).le hs.2.2
  have hlo := Finset.sum_le_sum (s := S) (f := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      max (f n).re 0-weight A N n*floorCost L y n else (f n).re) (g := fun n => (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).1; rfl)
  have hhi := Finset.sum_le_sum (s := S) (f := fun n => (f n).re) (g := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).2; rfl)
  rw [← Complex.re_sum] at hlo hhi
  have hulo := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have huhi := mul_le_mul_of_nonneg_left hhi (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hulo huhi

end
end RiemannGaussian.ZetaRieszSixPrimeSecondReflection
