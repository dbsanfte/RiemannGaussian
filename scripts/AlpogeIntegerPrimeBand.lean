import CheckAlpogeMinedBounds

/-! # The unit-density integer model for the reciprocal prime weights -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real Filter Topology

private theorem harmonic_reciprocals (n : ℕ) :
    ∑ d ∈ Ioc 0 n, (d:ℝ)⁻¹ = (harmonic n:ℝ) := by
  rw [harmonic_eq_sum_Icc,show Ioc 0 n = Icc 1 n by ext d; simp; omega]
  push_cast
  rfl

private theorem quotient_eq (N d : ℕ) (hd : 0 < d) :
    ((N/d:ℕ):ℝ) = (N:ℝ)/d-1+weight N d := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have he : ((N%d:ℕ):ℝ) + d*((N/d:ℕ):ℝ) = N := by exact_mod_cast Nat.mod_add_div N d
  unfold weight
  field_simp
  linarith

private theorem count_row {a b d N : ℕ} (hd : 0 < d) (h : N/d ≤ b) :
    (∑ e ∈ Ioc a b, if e*d ≤ N then (1:ℝ) else 0) = ((N/d-a:ℕ):ℝ) := by
  have hset : (Ioc a b).filter (fun e => e*d ≤ N) = Ioc a (N/d) := by
    ext e
    simp only [mem_filter,mem_Ioc,← Nat.le_div_iff_mul_le hd]
    omega
  rw [← Finset.sum_filter,hset]
  simp

/-- Counting the part of the divisor hyperbola strictly above its square side by columns. -/
private theorem quotient_tail (k : ℕ) :
    (∑ d ∈ Ioc k (k^2), ((k^2/d:ℕ):ℝ)) =
      (∑ j ∈ Ioc 0 k, ((k^2/j:ℕ):ℝ)) - (k:ℝ)^2 := by
  calc
    _ = ∑ d ∈ Ioc k (k^2), ∑ j ∈ Ioc 0 k, if j*d ≤ k^2 then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro d hd
      have hdk := (mem_Ioc.mp hd).1
      have hd0 : 0 < d := by omega
      have hcut : k^2/d ≤ k := by
        by_contra! hh
        have hp := (Nat.le_div_iff_mul_le hd0).mp (show k+1 ≤ k^2/d by omega)
        nlinarith only [hp,Nat.mul_le_mul_left (k+1) (show k+1 ≤ d by omega)]
      simpa using (count_row (a := 0) hd0 hcut).symm
    _ = ∑ j ∈ Ioc 0 k, ∑ d ∈ Ioc k (k^2), if d*j ≤ k^2 then (1:ℝ) else 0 := by
      rw [sum_comm]
      simp only [Nat.mul_comm]
    _ = ∑ j ∈ Ioc 0 k, (((k^2/j:ℕ):ℝ) - k) := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj0,hjk⟩ := mem_Ioc.mp hj
      have hcut : k ≤ k^2/j := (Nat.le_div_iff_mul_le hj0).mpr (by
        simpa only [pow_two] using Nat.mul_le_mul_left k hjk)
      rw [count_row hj0 (Nat.div_le_self _ _),Nat.cast_sub hcut]
    _ = _ := by simp [sum_sub_distrib,pow_two]

/-- The same weights as the large-prime statistic applied to every integer on the band. -/
def integerBand (k : ℕ) : ℝ := ∑ d ∈ Ioc k (k^2), weight (k^2) d

/-- The high band at a square is determined exactly by two harmonic numbers and the
weighted part through the square root. -/
theorem integerBand_eq (k : ℕ) :
    integerBand k = (k:ℝ)^2*(2*(harmonic k:ℝ) - (harmonic (k^2):ℝ))
       - 2*k + ∑ d ∈ Ioc 0 k, weight (k^2) d := by
  have hk : k ≤ k^2 := Nat.le_self_pow (by decide) _
  have sumq (a b : ℕ) (hab : a ≤ b) :
      (∑ d ∈ Ioc a b, ((k^2/d:ℕ):ℝ)) =
        (k:ℝ)^2*(∑ d ∈ Ioc a b, (d:ℝ)⁻¹) - ((b:ℝ)-a) + ∑ d ∈ Ioc a b, weight (k^2) d := by
    calc _ = ∑ d ∈ Ioc a b, ((k:ℝ)^2*(d:ℝ)⁻¹ - 1 + weight (k^2) d) := by
           apply sum_congr rfl
           intro d hd
           have h := quotient_eq (k^2) d (by have := (mem_Ioc.mp hd).1; omega)
           rw [Nat.cast_pow,div_eq_mul_inv] at h
           exact h
         _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum]; simp [Nat.cast_sub hab]
  have split := sum_Ioc_consecutive (fun d : ℕ => (d:ℝ)⁻¹) (Nat.zero_le k) hk
  rw [harmonic_reciprocals,harmonic_reciprocals] at split
  have h := quotient_tail k
  rw [sumq _ _ hk,sumq _ _ (Nat.zero_le k),Nat.cast_zero,Nat.cast_pow] at h
  unfold integerBand
  nlinarith only [h,mul_le_mul_of_nonneg_left split.le (sq_nonneg (k:ℝ)),
    mul_le_mul_of_nonneg_left split.ge (sq_nonneg (k:ℝ)),congrArg (fun z => (k:ℝ)^2*z) (harmonic_reciprocals k)]

/-- The harmonic remainder lies between the endpoint half-weights at n and n+1. -/
theorem harmonic_half_remainder {n : ℕ} (hn : 0 < n) :
    1/(2*((n:ℝ)+1)) ≤ (harmonic n:ℝ)-log n-eulerMascheroniConstant ∧
    (harmonic n:ℝ)-log n-eulerMascheroniConstant ≤ 1/(2*(n:ℝ)) :=
  AlpogeZetaSamples.harmonic_half_bounds hn

/-- Adding the small-denominator fractional parts to the integer band gives the
Euler-constant main term with a one-sided error bounded by three halves at every square. -/
theorem corrected_integerBand_bounds {k : ℕ} (hk : 1 ≤ k) :
    let baseline := integerBand k + ∑ d ∈ Ioc 0 k, (1-weight (k^2) d)
    0 ≤ eulerMascheroniConstant*(k:ℝ)^2 - baseline ∧
    eulerMascheroniConstant*(k:ℝ)^2 - baseline ≤ 3/2 := by
  have hp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hsmall := harmonic_half_remainder (n := k) (by omega)
  have hbig := harmonic_half_remainder (n := k^2) (pow_pos (by omega) 2)
  rw [Nat.cast_pow,log_pow] at hbig
  norm_num only [Nat.cast_ofNat] at hbig
  have hu := mul_le_mul_of_nonneg_left hsmall.2 (by positivity : 0 ≤ 2*(k:ℝ)^2)
  have hl := mul_le_mul_of_nonneg_left hsmall.1 (by positivity : 0 ≤ 2*(k:ℝ)^2)
  have hbu := mul_le_mul_of_nonneg_left hbig.2 (sq_nonneg (k:ℝ))
  have hbl := mul_nonneg (sq_nonneg (k:ℝ)) ((by positivity : 0 ≤ 1/(2*((k:ℝ)^2+1))).trans hbig.1)
  rw [show 2*(k:ℝ)^2*(1/(2*k)) = k by field_simp] at hu
  rw [show (k:ℝ)^2*(1/(2*(k:ℝ)^2)) = 1/2 by field_simp] at hbu
  have hfloor : (k:ℝ)-1 ≤ 2*(k:ℝ)^2*(1/(2*((k:ℝ)+1))) := by field_simp; nlinarith
  simp only [integerBand_eq,sum_sub_distrib,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
  constructor <;> nlinarith only [hu,hl,hbu,hbl,hfloor]

/-- Signed discrepancy between integer density and ordinary-prime log weights on
the common band k < d ≤ k squared. -/
def integerPrimeDiscrepancy (k : ℕ) : ℝ :=
  ∑ d ∈ Ioc k (k^2), weight (k^2) d * (1 - if d.Prime then log d else 0)

/-- The correction depends only on rational residues at denominators through k. -/
def smallResidueCorrection (k : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 k, ((k^2 % d:ℕ):ℝ) / d

private theorem correction_eq (k : ℕ) :
    smallResidueCorrection k = ∑ d ∈ Ioc 0 k, (1-weight (k^2) d) := by
  unfold smallResidueCorrection weight
  simp

/-- The sum of the small-denominator residues lies between zero and the number of terms. -/
theorem smallResidueCorrection_bounds (k : ℕ) : 0 ≤ smallResidueCorrection k ∧
    smallResidueCorrection k ≤ k := by
  rw [correction_eq]
  refine ⟨sum_nonneg fun d hd => sub_nonneg.mpr (weight_mem (mem_Ioc.mp hd).1).2,?_⟩
  calc _ ≤ ∑ _d ∈ Ioc 0 k, (1:ℝ) := sum_le_sum fun d hd => sub_le_self _ (weight_mem (mem_Ioc.mp hd).1).1
       _ = _ := by simp

/-- Subtracting the prime band from the integer band recovers the signed discrepancy. -/
theorem integerPrimeDiscrepancy_eq (k : ℕ) :
    integerPrimeDiscrepancy k = integerBand k - largePrimeSum (k^2) := by
  classical
  have hs : sqrt ((k^2:ℕ):ℝ) = k := by rw [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _)]
  have hp : (((Ioc 0 (k^2)).filter Nat.Prime).filter (fun p : ℕ => sqrt ((k^2:ℕ):ℝ) < p))
      = (Ioc k (k^2)).filter Nat.Prime := by
    ext d
    simp only [mem_filter,mem_Ioc,hs,Nat.cast_lt]
    constructor
    · rintro ⟨⟨⟨_,hsize⟩,hprime⟩,hcut⟩
      exact ⟨⟨hcut,hsize⟩,hprime⟩
    · rintro ⟨⟨hcut,hsize⟩,hprime⟩
      exact ⟨⟨⟨by omega,hsize⟩,hprime⟩,hcut⟩
  unfold integerPrimeDiscrepancy integerBand largePrimeSum
  rw [hp,sum_filter,← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hd : d.Prime
  · simp [hd]
    ring
  · simp [hd]

/-- At a square, the corrected prime/integer comparison differs from the actual prime
deficit by a nonnegative error of at most three halves, independently of the cutoff. -/
theorem corrected_discrepancy_error {k : ℕ} (hk : 1 ≤ k) :
    let error := eulerMascheroniConstant*(k:ℝ)^2-largePrimeSum (k^2) -
      (integerPrimeDiscrepancy k + smallResidueCorrection k)
    0 ≤ error ∧ error ≤ 3/2 := by
  rw [integerPrimeDiscrepancy_eq,correction_eq]
  obtain ⟨a,b⟩ := corrected_integerBand_bounds hk
  dsimp only
  constructor <;> linarith only [a,b]

/-- At a fourth power the raw discrepancy accounts for the prime deficit up to an
additive error between zero and the square root of the cutoff plus three halves. -/
theorem raw_fourth_error {n : ℕ} (hn : 1 ≤ n) :
    let err := eulerMascheroniConstant*(n:ℝ)^4-largePrimeSum (n^4) - integerPrimeDiscrepancy (n^2)
    0 ≤ err ∧ err ≤ (n:ℝ)^2 + 3/2 := by
  have hb := corrected_discrepancy_error (Nat.one_le_pow 2 n hn)
  dsimp only at hb ⊢
  rw [show (n^2)^2=n^4 by ring,Nat.cast_pow,show ((n:ℝ)^2)^2=(n:ℝ)^4 by ring] at hb
  have hc := smallResidueCorrection_bounds (n^2)
  rw [Nat.cast_pow] at hc
  constructor <;> linarith only [hb.1,hb.2,hc.1,hc.2]

end
end RiemannGaussian.AlpogeMined
