/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSevenPrimeReflection

/-!
# Two reflected large primes reduce the six-prime interval to [-1,1]

The second reflection is applied inside the original signed coefficient.
The prime label, total logarithm, phase and factorial allocation are unchanged.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeReflection
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszReflectedLinear
open ZetaRieszSperner ZetaRieszSignedSperner ZetaRieszReflectedPrimeBounds

private theorem prime_cofactor {n P : ℕ} (hs : Squarefree n) (hP : P ∈ n.primeFactors) :
    ∃ a : ℕ, n = P*a ∧ Squarefree (P*a) ∧ a.primeFactors = n.primeFactors.erase P ∧
      Real.log n = Real.log P+Real.log a := by
  let a := ∏ p ∈ n.primeFactors.erase P, p
  have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
  have he : n = P*a := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Finset.mul_prod_erase _ _ hP).symm
  have hsp : Squarefree (P*a) := he ▸ hs
  refine ⟨a,he,hsp,hfa,?_⟩
  rw [he,Nat.cast_mul,Real.log_mul
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hP).ne_zero)
    (by exact_mod_cast hsp.of_mul_right.ne_zero)]

/-- The complete four-prime response below its first third costs at
most one least-prime logarithm on its negative side. The singleton
chamber is nonnegative; a deleted large prime leaves the three-prime bound. -/
theorem riesz_four_lower_third_ge {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) {D : ℝ} (hthird : 3*D ≤ Real.log n) :
    -Real.log n.minFac ≤ VaughanLogAverage.riesz D n := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hmin := Nat.minFac_prime hn1
  have hminmem := hmin.mem_primeFactors (Nat.minFac_dvd n) hs.ne_zero
  by_cases hbase : D ≤ Real.log n.minFac
  · have h := ZetaRieszExtremePrimeProfile.riesz_mul_eq_of_extreme_rough
      (a := 1) (b := n) (L := D) (by simpa using hs) (by
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        have hle := Nat.minFac_le_of_dvd hp'.two_le (Nat.dvd_of_mem_primeFactors hp)
        exact hbase.trans (Real.log_le_log (by exact_mod_cast hmin.pos) (by exact_mod_cast hle)))
    simp only [mul_one] at h
    rw [h]
    exact (neg_nonpos.mpr (Real.log_natCast_nonneg n.minFac)).trans (by simp [VaughanLogAverage.riesz])
  by_cases hlarge : ∃ P ∈ n.primeFactors, D ≤ Real.log P
  · obtain ⟨P,hP,hPD⟩ := hlarge
    obtain ⟨a,he,hsp,hfa,hlog⟩ := prime_cofactor hs hP
    have hac : a.primeFactors.card = 3 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
    have hp := Nat.prime_of_mem_primeFactors hP
    have hpn : ¬ P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
    have hPmin : n.minFac ≠ P := by intro hh; rw [← hh] at hPD; exact hbase hPD
    have hmema : n.minFac ∈ a.primeFactors := by
      rw [hfa]
      exact Finset.mem_erase.mpr ⟨hPmin,hminmem⟩
    have ha1 : a ≠ 1 := by intro hh; simp [hh] at hac
    have hminEq : a.minFac = n.minFac := by
      apply le_antisymm
      · exact Nat.minFac_le_of_dvd hmin.two_le (Nat.dvd_of_mem_primeFactors hmema)
      · apply Nat.minFac_le_of_dvd (Nat.minFac_prime ha1).two_le
        rw [he]
        exact dvd_mul_of_dvd_right (Nat.minFac_dvd a) P
    have hb := (riesz_bounds_minFac D hsp.of_mul_right (by omega : 2 ≤ a.primeFactors.card)).1
    have hcap : parityCapacity 1 1 = 1 := by decide +kernel
    rw [hac,show 3-2 = 1 by rfl,hcap,hminEq] at hb
    norm_num only [Nat.cast_one,mul_one,one_mul] at hb
    conv_rhs => rw [he,riesz_prime_mul D hp hpn,
      ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith : D-Real.log P ≤ 0),sub_zero]
    exact hb
  · have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    let P := n.primeFactors.max' hne
    have hP : P ∈ n.primeFactors := Finset.max'_mem _ _
    have hmax (p : ℕ) (hp : p ∈ n.primeFactors) : Real.log p ≤ Real.log P :=
      Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by exact_mod_cast Finset.le_max' _ p hp)
    have hsmall : Real.log P ≤ D := le_of_lt (lt_of_not_ge (fun h => hlarge ⟨P,hP,h⟩))
    have hD : 0 ≤ D := (Real.log_natCast_nonneg P).trans hsmall
    rw [ZetaRieszFivePrimeFloor.riesz_four_small_cutoff hs hc hP hmax hD hsmall hthird]
    linarith only [hthird,Real.log_natCast_nonneg n.minFac]

/-- Reflection preserves the sign for four prime factors and transports
the one-unit lower bound to cutoffs above two thirds of the total log. -/
theorem riesz_four_upper_two_thirds_ge {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) {D : ℝ} (hthird : 2*Real.log n ≤ 3*D) :
    -Real.log n.minFac ≤ VaughanLogAverage.riesz D n := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  have hb := riesz_four_lower_third_ge hs hc (D := Real.log n-D) (by linarith)
  have hr := VaughanLogAverage.riesz_reflection D hs hn1 hnp
  rw [moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  rwa [hr] at hb

/-- The actual six-prime coefficient with exactly two reflected large
primes lies in [-1,1] in its original least-prime units. -/
theorem coefficient_six_two_outer_sharp {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    -(Real.log n/L*Real.log n.minFac) ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ Real.log n/L*Real.log n.minFac := by
  let D := Real.log n-L
  have hs : Squarefree (outerPart D n * activePart D n) := by
    rw [factorization D hn]
    exact hn
  have hcount : (activePrimes D n).card = 4 := by
    have hh := count_split D n
    change (outerPrimes (Real.log n-L) n).card + (activePrimes D n).card = _ at hh
    omega
  have hlog : Real.log n = Real.log (outerPart D n)+Real.log (activePart D n) := by
    conv_lhs => rw [← factorization D hn]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hs.of_mul_left.ne_zero) (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hsum := Finset.sum_le_sum (s := outerPrimes D n) (fun p hp => (Finset.mem_filter.mp hp).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [← outerPart_primeFactors,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_left,
    outerPart_primeFactors] at hsum
  change (outerPrimes (Real.log n-L) n).card*D ≤ Real.log (outerPart D n) at hsum
  rw [ho] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have haD : 2*Real.log (activePart D n) ≤ 3*D := by dsimp only [D] at *; linarith
  have hac : (activePart D n).primeFactors.card = 4 := by rw [activePart_primeFactors]; exact hcount
  have hb := riesz_four_upper_two_thirds_ge hs.of_mul_right hac haD
  have ht := (riesz_bounds_minFac D hs.of_mul_right (by omega : 2 ≤ (activePart D n).primeFactors.card)).2
  have hcap : parityCapacity 2 0 = 1 := by decide +kernel
  rw [hac,show 4-2 = 2 by rfl,hcap] at ht
  norm_num only [Nat.cast_one,mul_one,one_mul] at ht
  have hm := activePart_minFac hn (Finset.card_pos.mp (by omega : 0 < (activePrimes D n).card))
  rw [hm] at hb ht
  have hlo := mul_le_mul_of_nonneg_left hb (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  have hhi := mul_le_mul_of_nonneg_left ht (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  rw [coefficient_eq_active hn (by omega : 2 ≤ n.primeFactors.card),hc]
  norm_num only [show (-1 : ℝ)^6 = 1 by norm_num,mul_one]
  dsimp only [D] at hlo hhi
  constructor <;> nlinarith only [hlo,hhi]

open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- The two-large six-prime cost retains the actual cosine and its two
orientations. It does not bound any other count or sum over labels. -/
def twoOuterCost (L y : ℝ) (n : ℕ) : ℝ :=
  (Real.log n/L*Real.log n.minFac)*
    (max (Real.cos (y*Real.log n)) 0+max (-Real.cos (y*Real.log n)) 0)

/-- The sharpened charge is nonnegative on every label. -/
theorem twoOuterCost_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ twoOuterCost L y n := by
  unfold twoOuterCost
  positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]

/-- The actual atom has a one-unit coefficient charge, with its original
factorial weight and missing allocation fraction unchanged. -/
theorem residual_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    -(weight A N n*twoOuterCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*twoOuterCost L y n := by
  have hh := coefficient_six_two_outer_sharp hL hs hc hD ho
  have hw := weight_nonneg A N n
  rw [re_residual_atom]
  suffices hb : -twoOuterCost L y n ≤
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤ twoOuterCost L y n by
    exact ⟨by simpa only [mul_neg] using mul_le_mul_of_nonneg_left hb.1 hw,
      mul_le_mul_of_nonneg_left hb.2 hw⟩
  by_cases hx : 0 ≤ Real.cos (y*Real.log n)
  · have hlo := mul_le_mul_of_nonneg_right hh.1 hx
    have hhi := mul_le_mul_of_nonneg_right hh.2 hx
    simp only [twoOuterCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),add_zero]
    constructor <;> nlinarith only [hlo,hhi]
  · have hx' := le_of_not_ge hx
    have hlo := mul_le_mul_of_nonpos_right hh.2 hx'
    have hhi := mul_le_mul_of_nonpos_right hh.1 hx'
    simp only [twoOuterCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),zero_add]
    constructor <;> nlinarith only [hlo,hhi]

/-- Favorable signed atoms are retained on both sides; the improved
charge is paid only in the corresponding unfavorable direction. -/
theorem residual_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*twoOuterCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*twoOuterCost L y n := by
  dsimp only
  have hh := residual_bounds A hL y N hs hc hD ho
  have hd := mul_nonneg (weight_nonneg A N n) (twoOuterCost_nonneg hL y n)
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hd]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hd]

/-- Compared with the earlier six-prime charges, the two-large sector
saves at least two least-prime units in one phase and three in the other.
These improve alternative one-sided bounds; they are not additive supply. -/
theorem costs_save_least_prime_units {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6) :
    (Real.log n/L*Real.log n.minFac)*
        (2*max (Real.cos (y*Real.log n)) 0+3*max (-Real.cos (y*Real.log n)) 0) ≤
      ZetaRieszSixPrimeGeometry.floorCost L y n-twoOuterCost L y n ∧
      (Real.log n/L*Real.log n.minFac)*
        (3*max (Real.cos (y*Real.log n)) 0+2*max (-Real.cos (y*Real.log n)) 0) ≤
      ZetaRieszSixPrimeGeometry.ceilingCost L y n-twoOuterCost L y n := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hm := smallest_prime_log_le_mean hs (by omega : 0 < n.primeFactors.card) (Nat.minFac_prime hn1)
    (fun p hp => Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
      (Nat.dvd_of_mem_primeFactors hp))
  have hb := mul_le_mul_of_nonneg_left hm (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  have he : middleLayerAllowance L n = 6*(Real.log n/L*(Real.log n/n.primeFactors.card)) := by
    rw [middleLayerAllowance,if_pos ⟨hs,(by omega : 2 ≤ n.primeFactors.card)⟩,hc]
    norm_num [Nat.choose]
    ring
  have hp := mul_le_mul_of_nonneg_right hb (le_max_right (Real.cos (y*Real.log n)) 0)
  have hn := mul_le_mul_of_nonneg_right hb (le_max_right (-Real.cos (y*Real.log n)) 0)
  dsimp only [ZetaRieszSixPrimeGeometry.floorCost,ZetaRieszSixPrimeGeometry.ceilingCost,twoOuterCost]
  rw [he]
  constructor <;> nlinarith only [hp,hn]

open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- Every unpaid subset of the literal core inherits both six-prime
bounds from order two onwards. All other labels stay signed and exact. -/
theorem core_subset_bounds {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (y : ℝ) (S : Finset ℕ) (hS : S ⊆ coreBand u N K) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
      (outerPrimes (Real.log n-L) n).card = 2 then
        max (f n).re 0-weight A N n*twoOuterCost L y n else (f n).re) ≤
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
        u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
          (outerPrimes (Real.log n-L) n).card = 2 then
            min (f n).re 0+weight A N n*twoOuterCost L y n else (f n).re) := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hp (n : ℕ) (hn : n ∈ S) (hs : Squarefree n ∧ n.primeFactors.card = 6 ∧
      (outerPrimes (Real.log n-L) n).card = 2) :=
    residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N hs.1 hs.2.1
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu hN (hS hn)).le hs.2.2
  have hlo := Finset.sum_le_sum (s := S) (f := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ (outerPrimes (Real.log n-L) n).card = 2 then
      max (f n).re 0-weight A N n*twoOuterCost L y n else (f n).re) (g := fun n => (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).1; rfl)
  have hhi := Finset.sum_le_sum (s := S) (f := fun n => (f n).re) (g := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ (outerPrimes (Real.log n-L) n).card = 2 then
      min (f n).re 0+weight A N n*twoOuterCost L y n else (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).2; rfl)
  rw [← Complex.re_sum] at hlo hhi
  have hulo := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have huhi := mul_le_mul_of_nonneg_left hhi (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hulo huhi

/-- One reflected large prime leaves five active factors, so the earlier
positive six-prime capacity four falls to three on this larger sector. -/
theorem coefficient_six_one_outer {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : Real.log n < 4*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 1) :
    -(3*(Real.log n/L*Real.log n.minFac)) ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ 3*(Real.log n/L*Real.log n.minFac) := by
  have hh := coefficient_activeAllowance_bounds hL (by omega : 5 ≤ n.primeFactors.card) hD
  have h₀ : activeCapacity 6 1 0 = 3 := by decide +kernel
  have h₁ : activeCapacity 6 1 1 = 3 := by decide +kernel
  simp only [activeAllowance,hs,hc,show 5 ≤ (6 : ℕ) by omega,and_self,ite_true,ho,h₀,h₁,
    Nat.cast_ofNat] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

/-- The actual reflected-prime count selects capacities three, one or
zero. The zero case is exact divisor cancellation, not discarded phase. -/
def reflectedSixCost (L y : ℝ) (n : ℕ) : ℝ :=
  (if (outerPrimes (Real.log n-L) n).card = 1 then 3
    else if (outerPrimes (Real.log n-L) n).card = 2 then 1 else 0)*twoOuterCost L y n

/-- All reflected six-prime sectors retain their favorable observations
and their full original kernel. Three reflected large primes cost zero. -/
theorem residual_reflected_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hs : Squarefree n) (hc : n.primeFactors.card = 6)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : 1 ≤ (outerPrimes (Real.log n-L) n).card) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*reflectedSixCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*reflectedSixCost L y n := by
  dsimp only
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have ht : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by have := hs.ne_zero; omega))
  have hquarter : Real.log n < 4*(Real.log n-L) := by linarith only [ht,hD]
  by_cases ho₁ : (outerPrimes (Real.log n-L) n).card = 1
  · have hh := coefficient_six_one_outer hL hs hc hquarter ho₁
    have hw := weight_nonneg A N n
    have hb := twoOuterCost_nonneg hL y n
    have bounds : -(weight A N n*(3*twoOuterCost L y n)) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*(3*twoOuterCost L y n) := by
      rw [re_residual_atom]
      have hlo := mul_le_mul_of_nonneg_left hh.1 hw
      have hhi := mul_le_mul_of_nonneg_left hh.2 hw
      by_cases hx : 0 ≤ Real.cos (y*Real.log n)
      · have h₀ := mul_le_mul_of_nonneg_right hlo hx
        have h₁ := mul_le_mul_of_nonneg_right hhi hx
        simp only [twoOuterCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),add_zero]
        constructor <;> nlinarith only [h₀,h₁]
      · have hx' := le_of_not_ge hx
        have h₀ := mul_le_mul_of_nonpos_right hhi hx'
        have h₁ := mul_le_mul_of_nonpos_right hlo hx'
        simp only [twoOuterCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),zero_add]
        constructor <;> nlinarith only [h₀,h₁]
    rw [reflectedSixCost,if_pos ho₁]
    have hd : 0 ≤ weight A N n*(3*twoOuterCost L y n) := by positivity
    by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    · rw [max_eq_left hv,min_eq_right hv]
      constructor <;> linarith only [bounds.2,hd]
    · have hv' := le_of_not_ge hv
      rw [max_eq_right hv',min_eq_left hv']
      constructor <;> linarith only [bounds.1,hd]
  · by_cases ho₂ : (outerPrimes (Real.log n-L) n).card = 2
    · simpa only [reflectedSixCost,if_neg ho₁,if_pos ho₂,one_mul] using
        residual_retained_bounds A hL y N hs hc hD ho₂
    · have hz := coefficient_eq_zero_of_three_outer hs (by omega : 5 ≤ n.primeFactors.card)
        hquarter (by omega : 3 ≤ (outerPrimes (Real.log n-L) n).card)
      simp only [reflectedSixCost,if_neg ho₁,if_neg ho₂,zero_mul,mul_zero,re_residual_atom,
        hz,Complex.zero_re,max_self,min_self,sub_zero,add_zero,le_refl,and_self]

/-- Every unpaid subset of the literal core inherits both six-prime
bounds from order two onwards. All other labels stay signed and exact. -/
theorem core_reflected_subset_bounds {u : ℝ} (hu : 1/2 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    (K : ℕ) (y : ℝ) (S : Finset ℕ) (hS : S ⊆ coreBand u N K) :
    let A := intermediatePrimes u N
    let L := SquarefreeVaughanLogSource.length u N
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card then
        max (f n).re 0-weight A N n*reflectedSixCost L y n else (f n).re) ≤
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
      ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
        u^(N+1)*(∑ n ∈ S, if Squarefree n ∧ n.primeFactors.card = 6 ∧
          1 ≤ (outerPrimes (Real.log n-L) n).card then
            min (f n).re 0+weight A N n*reflectedSixCost L y n else (f n).re) := by
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hp (n : ℕ) (hn : n ∈ S) (hs : Squarefree n ∧ n.primeFactors.card = 6 ∧
      1 ≤ (outerPrimes (Real.log n-L) n).card) :=
    residual_reflected_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N hs.1 hs.2.1
      (ZetaRieszSevenPrimeReflection.core_cutoff_two_sevenths hu hN (hS hn)).le hs.2.2
  have hlo := Finset.sum_le_sum (s := S) (f := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      max (f n).re 0-weight A N n*reflectedSixCost L y n else (f n).re) (g := fun n => (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).1; rfl)
  have hhi := Finset.sum_le_sum (s := S) (f := fun n => (f n).re) (g := fun n : ℕ =>
    if Squarefree n ∧ n.primeFactors.card = 6 ∧ 1 ≤ (outerPrimes (Real.log n-L) n).card then
      min (f n).re 0+weight A N n*reflectedSixCost L y n else (f n).re)
    (fun n hn => by split_ifs with hs; exact (hp n hn hs).2; rfl)
  rw [← Complex.re_sum] at hlo hhi
  have hulo := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have huhi := mul_le_mul_of_nonneg_left hhi (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hulo huhi

end
end RiemannGaussian.ZetaRieszSixPrimeReflection
