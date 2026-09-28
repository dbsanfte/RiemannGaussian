/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixPrimeReflection
import RiemannGaussian.ZetaRieszTentSlope

/-!
# Centered cancellation inside the one-large six-prime charge

The five active prime factors have an exactly antisymmetric Riesz response.
Its central zero and the proved cutoff slope improve the original six-prime
charge without changing its integer, phase, allocation or signed complement.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeCentered
noncomputable section
open scoped BigOperators Classical
open ZetaRieszReflectedPrimeBounds ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- Every squarefree five-prime response vanishes at its exact midpoint. -/
theorem riesz_five_center_eq_zero {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) :
    VaughanLogAverage.riesz (Real.log n/2) n = 0 := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  have hr := VaughanLogAverage.riesz_reflection (Real.log n/2) hs hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc,
    show Real.log n-Real.log n/2 = Real.log n/2 by ring] at hr
  norm_num at hr
  linarith

/-- The full five-prime response costs at most four times its distance
from the doubled central cutoff, with every divisor sign retained. -/
theorem abs_riesz_five_le_center_gap {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) (D : ℝ) :
    |VaughanLogAverage.riesz D n| ≤ 4*|2*D-Real.log n| := by
  have h := ZetaRieszTentSlope.riesz_cutoff_lipschitz_quarter D (Real.log n/2) hs
    (by omega : 2 ≤ n.primeFactors.card)
  rw [riesz_five_center_eq_zero hs hc,sub_zero,
    ZetaRieszTentSlope.absolute_divisor_mass_eq_card hs,
    ZetaRieszSmoothHead.card_divisors_of_squarefree hs,hc] at h
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at h
  have he : D-Real.log n/2 = (2*D-Real.log n)/2 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- The original six-prime coefficient is simultaneously controlled by
the least prime and the central cancellation of its five active factors. -/
theorem coefficient_six_one_outer_centered {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    |(SquarefreeVaughanLogSource.coefficient L n).re| ≤
      (Real.log n/L)*min (3*Real.log n.minFac)
        (4*|2*(Real.log n-L)-Real.log (activePart (Real.log n-L) n)|) := by
  let D := Real.log n-L
  have hsf : Squarefree (outerPart D n * activePart D n) := by
    rw [factorization D hs]
    exact hs
  have hcount : (activePart D n).primeFactors.card = 5 := by
    have hh := count_split D n
    rw [activePart_primeFactors]
    change (outerPrimes (Real.log n-L) n).card+(activePrimes D n).card = _ at hh
    omega
  have hb := abs_riesz_five_le_center_gap hsf.of_mul_right hcount D
  have h₀ := ZetaRieszSixPrimeReflection.coefficient_six_one_outer hL hs hc hD ho
  have hmin : |(SquarefreeVaughanLogSource.coefficient L n).re| ≤
      (Real.log n/L)*(3*Real.log n.minFac) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h₀.1,h₀.2]
  have hnonneg : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  rw [mul_min_of_nonneg _ _ hnonneg]
  refine le_min hmin ?_
  rw [coefficient_eq_active hs (by omega : 2 ≤ n.primeFactors.card),hc]
  norm_num only [show (-1 : ℝ)^6 = 1 by norm_num,mul_one,abs_mul,abs_neg,
    abs_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_left hb hnonneg

/-- A midpoint hit gives an exact zero of the actual original coefficient. -/
theorem coefficient_six_one_outer_eq_zero {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1)
    (hcenter : 2*(Real.log n-L) = Real.log (activePart (Real.log n-L) n)) :
    (SquarefreeVaughanLogSource.coefficient L n).re = 0 := by
  have h := coefficient_six_one_outer_centered hL hs hc hD ho
  rw [hcenter,sub_self,abs_zero,mul_zero,
    min_eq_right (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n.minFac)),mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The one-large charge uses its central zero. The other reflected
sectors retain their independently proved charges, including exact zero. -/
def centeredSixCost (L y : ℝ) (n : ℕ) : ℝ :=
  if (outerPrimes (Real.log n-L) n).card = 1 then
    (Real.log n/L)*min (3*Real.log n.minFac)
      (4*|2*(Real.log n-L)-Real.log (activePart (Real.log n-L) n)|)*
      (max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0)
  else ZetaRieszSixPrimeReflection.reflectedSixCost L y n

/-- The centered refinement never enlarges either previous directed charge. -/
theorem centeredSixCost_le_reflected {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    centeredSixCost L y n ≤ ZetaRieszSixPrimeReflection.reflectedSixCost L y n := by
  by_cases ho : (outerPrimes (Real.log n-L) n).card = 1
  · simp only [centeredSixCost,if_pos ho,ZetaRieszSixPrimeReflection.reflectedSixCost]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (min_le_left (3*Real.log n.minFac)
        (4*|2*(Real.log n-L)-Real.log (activePart (Real.log n-L) n)|))
        (div_nonneg (Real.log_natCast_nonneg n) hL.le))
      (add_nonneg (le_max_right (Real.cos (y*Real.log n)) 0)
        (le_max_right (-Real.cos (y*Real.log n)) 0))
    dsimp only [ZetaRieszSixPrimeReflection.twoOuterCost]
    nlinarith only [h]
  · simp only [centeredSixCost,if_neg ho,le_refl]

/-- The literal atom keeps every favorable observation; only its adverse
part is charged, now with the exact midpoint cancellation included. -/
theorem residual_centered_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : 1 ≤ (outerPrimes (Real.log n-L) n).card) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*centeredSixCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*centeredSixCost L y n := by
  by_cases ho₁ : (outerPrimes (Real.log n-L) n).card = 1
  · have hn1 : n ≠ 1 := by intro h; simp [h] at hc
    have ht : 0 < Real.log n := Real.log_pos (by
      exact_mod_cast (show 1 < n by have := hs.ne_zero; omega))
    have hb := coefficient_six_one_outer_centered hL hs hc (by linarith only [ht,hD]) ho₁
    let c := (Real.log n/L)*min (3*Real.log n.minFac)
      (4*|2*(Real.log n-L)-Real.log (activePart (Real.log n-L) n)|)
    have hc0 : 0 ≤ c := by dsimp [c]; positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]
    have hcn : 0 ≤ centeredSixCost L y n := by
      simp only [centeredSixCost,if_pos ho₁]
      exact mul_nonneg hc0 (add_nonneg (le_max_right _ _) (le_max_right _ _))
    have he : |(residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re| ≤
        weight A N n*centeredSixCost L y n := by
      rw [re_residual_atom,abs_mul,abs_mul,abs_of_nonneg (weight_nonneg A N n)]
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (weight_nonneg A N n))
        (abs_nonneg (Real.cos (y*Real.log n)))
      have habs : |Real.cos (y*Real.log n)| =
          max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0 := by
        by_cases hp : 0 ≤ Real.cos (y*Real.log n)
        · simp only [abs_of_nonneg hp,max_eq_left hp,max_eq_right (neg_nonpos.mpr hp),add_zero]
        · have hp' := le_of_not_ge hp
          simp only [abs_of_nonpos hp',max_eq_right hp',max_eq_left (neg_nonneg.mpr hp'),zero_add]
      simpa only [centeredSixCost,if_pos ho₁,habs,mul_assoc] using h
    dsimp only
    have hd := mul_nonneg (weight_nonneg A N n) hcn
    have bounds := abs_le.mp he
    by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    · rw [max_eq_left hv,min_eq_right hv]
      constructor <;> linarith only [bounds.2,hd]
    · have hv' := le_of_not_ge hv
      rw [max_eq_right hv',min_eq_left hv']
      constructor <;> linarith only [bounds.1,hd]
  · simpa only [centeredSixCost,if_neg ho₁] using
      ZetaRieszSixPrimeReflection.residual_reflected_retained_bounds A hL y N hs hc hD ho

open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- Both bounds on any unpaid core subset improve the existing reflected
charges and keep every other label in the same exact signed sum. -/
theorem core_centered_subset_bounds {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (y : ℝ) (S : Finset ℕ) (hS : S ⊆ coreBand u N K) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card then
        max (f n).re 0-weight A N n*centeredSixCost L y n else (f n).re) ≤
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
        u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
          1 ≤ (outerPrimes (Real.log n-L) n).card then
            min (f n).re 0+weight A N n*centeredSixCost L y n else (f n).re) := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hp (n : ℕ) (hn : n ∈ S) (hs : Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card) :=
    residual_centered_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N hs.1 hs.2.1
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu hN (hS hn)).le hs.2.2
  have hlo := Finset.sum_le_sum (s := S) (f := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      max (f n).re 0-weight A N n*centeredSixCost L y n else (f n).re) (g := fun n => (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).1; rfl)
  have hhi := Finset.sum_le_sum (s := S) (f := fun n => (f n).re) (g := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      min (f n).re 0+weight A N n*centeredSixCost L y n else (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).2; rfl)
  rw [← Complex.re_sum] at hlo hhi
  have hulo := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have huhi := mul_le_mul_of_nonneg_left hhi (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hulo huhi

end
end RiemannGaussian.ZetaRieszSixPrimeCentered
