/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WireKernel

/-! # Concrete original-grid dyadic factor acquisition for D.4
Integer valuation extraction is the executed Mathlib maxPowDvdDiv algorithm.
There is no rational coefficient, inverse, integrality or factor-table input.
Primitive bit/extension arithmetic clocks are separate from this data constructor.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WireKernelFactors
open scoped BigOperators
open SemiprimeD1WireKernel

/-- Original integer factor displacement, after cancelling the common grid shift. -/
def difference (j q : ℕ) : ℤ := (j:ℤ)-(q:ℤ)

/-- Nonzero grid differences have magnitude strictly below the original grid size. -/
theorem difference_abs_lt (N j q : ℕ) (hj : j<N) (hq : q<N) :
    (difference j q).natAbs<N := by
  by_cases h : q≤j
  · have he : difference j q=((j-q:ℕ):ℤ) := by unfold difference;omega
    rw [he,Int.natAbs_natCast]
    omega
  · have he : difference j q=-((q-j:ℕ):ℤ) := by unfold difference;omega
    rw [he,Int.natAbs_neg,Int.natAbs_natCast]
    omega

/-- Different original indices give a genuine nonzero integer factor. -/
theorem difference_ne_zero (j q : ℕ) (h : q≠j) : difference j q≠0 := by
  unfold difference
  omega

/-- Every nonzero factor uses at most k−1 powers of two on the 2^k grid. -/
theorem difference_order_lt (k j q : ℕ) (hj : j<2^k) (hq : q<2^k) (hne : q≠j) :
    padicValInt 2 (difference j q)<k := by
  have hz := difference_ne_zero j q hne
  have hp : 2^padicValInt 2 (difference j q) ≤ (difference j q).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hz)) pow_padicValNat_dvd
  have hl := hp.trans_lt (difference_abs_lt (2^k) j q hj hq)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp hl

/-- The original zero factor has alpha-content k; all others use their actual order. -/
def factorOrder (k j q : ℕ) : ℕ := if q=j then k else padicValInt 2 (difference j q)

/-- Original factor contents are bounded solely by original grid membership. -/
theorem factorOrder_le (k j q : ℕ) (hj : j<2^k) (hq : q<2^k) : factorOrder k j q≤k := by
  by_cases h : q=j
  · simp [factorOrder,h]
  · simpa only [factorOrder,h,ite_false] using (difference_order_lt k j q hj hq h).le

/-- Actual integer constant-factor divisibility, including the zero factor. -/
theorem factorOrder_dvd_difference (k j q : ℕ) :
    (2:ℤ)^factorOrder k j q ∣ difference j q := by
  by_cases h : q=j
  · simp [factorOrder,h,difference]
  · simpa [factorOrder,h] using padicValInt_dvd (p:=2) (difference j q)

/-- Actual alpha coefficient has every required factor content. -/
theorem factorOrder_dvd_alpha (k j q : ℕ) (hj : j<2^k) (hq : q<2^k) :
    (2:ℤ)^factorOrder k j q ∣ (2:ℤ)^k := by
  exact pow_dvd_pow 2 (factorOrder_le k j q hj hq)

/-- Original derivative products contain no zero factor. -/
theorem derivativeProduct_ne_zero (N j : ℕ) (hj : j<N) : derivativeProduct N j≠0 := by
  have h := derivativeProduct_natAbs N j hj
  intro hz
  rw [hz,Int.natAbs_zero] at h
  exact Nat.mul_ne_zero (Nat.factorial_ne_zero j) (Nat.factorial_ne_zero _) h.symm

private theorem valuation_prod (s : Finset ℕ) (f : ℕ→ℤ)
    (hf : ∀ q∈s,f q≠0) : padicValInt 2 (∏ q∈s,f q)=∑ q∈s,padicValInt 2 (f q) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hn : (∏ q∈s,f q)≠0 := Finset.prod_ne_zero_iff.mpr
      (fun q hq => hf q (Finset.mem_insert_of_mem hq))
    simp only [Finset.prod_insert ha,Finset.sum_insert ha,
      padicValInt.mul (hf a (by simp)) hn,ih (fun q hq => hf q (Finset.mem_insert_of_mem hq))]

/-- The total content of all original affine factors is E+k at EVERY t. -/
theorem total_factor_content (k j : ℕ) (hj : j<2^k) :
    (∑ q∈Finset.range (2^k),factorOrder k j q)=padicValNat 2 (2^k-1).factorial+k := by
  let f := fun q => if q=j then (1:ℤ) else difference j q
  have hf : ∀ q∈Finset.range (2^k),f q≠0 := by
    intro q _
    by_cases h : q=j
    · simp [f,h]
    · simpa only [f,h,ite_false] using difference_ne_zero j q h
  have hv := valuation_prod (Finset.range (2^k)) f hf
  have hc := derivativeProduct_content k j hj
  change padicValInt 2 (∏ q∈Finset.range (2^k),f q)=_ at hc
  rw [hv] at hc
  have he (q : ℕ) : factorOrder k j q=padicValInt 2 (f q)+(if q=j then k else 0) := by
    by_cases h : q=j <;> simp [factorOrder,f,h]
  simp_rw [he]
  rw [Finset.sum_add_distrib,hc]
  simp [Finset.mem_range,hj]

/-- Explicit exponent of two remaining after original denominator cancellation. -/
def excess (k j d : ℕ) : ℕ :=
  (∑ q∈(Finset.range (2^k)).erase d,factorOrder k j q)-padicValNat 2 (2^k-1).factorial

/-- The original omitted-factor numerator has enough content to cancel C'(0). -/
theorem omitted_content_ge (k j d : ℕ) (hj : j<2^k) (hd : d<2^k) :
    padicValNat 2 (2^k-1).factorial ≤
      ∑ q∈(Finset.range (2^k)).erase d,factorOrder k j q := by
  have hs := Finset.sum_erase_add (Finset.range (2^k)) (factorOrder k j) (Finset.mem_range.mpr hd)
  rw [total_factor_content k j hj] at hs
  have hl := factorOrder_le k j d hj hd
  omega

/-- A nonlocal omitted factor leaves a genuine additional factor two. -/
theorem excess_positive (k j d : ℕ) (hj : j<2^k) (hd : d<2^k) (hne : d≠j) :
    1≤excess k j d := by
  have hs := Finset.sum_erase_add (Finset.range (2^k)) (factorOrder k j) (Finset.mem_range.mpr hd)
  rw [total_factor_content k j hj] at hs
  have hl := difference_order_lt k j d hj hd hne
  rw [show factorOrder k j d=padicValInt 2 (difference j d) by simp [factorOrder,hne]] at hs
  unfold excess
  omega

/-- Integer linear factor data after cancelling only its actual powers of two. -/
structure Linear where
  /-- Original constant divided by its known content. -/
  constant : ℤ
  /-- Original alpha divided by the SAME known content. -/
  slope : ℤ

/-- Actual factor acquisition from original indices; both quotients are exact. -/
def normalizedFactor (k j q : ℕ) : Linear :=
  let power := (2:ℤ)^factorOrder k j q
  ⟨difference j q/power,(2:ℤ)^k/power⟩

/-- The acquired linear data reconstructs the actual original integer constant. -/
theorem normalized_constant (k j q : ℕ) :
    (normalizedFactor k j q).constant*(2:ℤ)^factorOrder k j q=difference j q :=
  Int.ediv_mul_cancel (factorOrder_dvd_difference k j q)

/-- The acquired linear data reconstructs the actual original alpha coefficient. -/
theorem normalized_slope (k j q : ℕ) (hj : j<2^k) (hq : q<2^k) :
    (normalizedFactor k j q).slope*(2:ℤ)^factorOrder k j q=(2:ℤ)^k :=
  Int.ediv_mul_cancel (factorOrder_dvd_alpha k j q hj hq)

end RiemannGaussian.SemiprimeD1WireKernelFactors
