/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityMaskTails

/-!
# The exact rectangle becomes automatic inside the selected log-share box

All four order boundaries are paid uniformly before any prime-phase
replacement. The original mask is retained in the exact error identity.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint

/-- The exact multinomial weight excluded by the original correlated rectangle. -/
def rectangleOmittedMass (N n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.piAntidiag n.primeFactors (N+1)).filter
    (fun d => d ∉ rectangleAllocations N n),
      allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d

/-- No factorial weight is lost in passing between the exact rectangle
and its explicitly defined complement. -/
theorem rectangleMass_add_omitted {n : ℕ} (h : FullParityBox n) (N : ℕ) :
    rectangleMass N (1-Real.log (largestPrime n)/Real.log n)
      (Real.log n.minFac/(Real.log n-Real.log (largestPrime n)))+
        rectangleOmittedMass N n = 1 := by
  rw [rectangleMass_eq_good_add_bad h, goodRectangleMass, badRectangleMass,
    Finset.sum_filter_add_sum_filter_not]
  have hf : (Finset.piAntidiag n.primeFactors (N+1)).filter
      (fun d => d ∈ rectangleAllocations N n) = rectangleAllocations N n := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hd => ⟨(Finset.mem_filter.mp hd).1, hd⟩⟩
  rw [rectangleOmittedMass]
  nth_rw 1 [← hf]
  rw [Finset.sum_filter_add_sum_filter_not]
  simp only [allocationWeight]
  rw [← Finset.sum_pow_eq_sum_piAntidiag, (fullParityBox_shares h).2, one_pow]

/-- The literal correlated order box misses exponentially little mass.
The weakest boundary is the lower order on the least prime. -/
theorem rectangleOmittedMass_bounds {n : ℕ} (h : FullParityBox n) (N : ℕ) :
    0 ≤ rectangleOmittedMass N n ∧
      rectangleOmittedMass N n ≤ 6*Real.exp (-(N : ℝ)/6000) := by
  let S := n.primeFactors
  let x := fun p : ℕ => Real.log p/Real.log n
  let p := largestPrime n
  let r := n.minFac
  have hp : p ∈ S := h.largest_mem
  have hr : r ∈ S := (Nat.minFac_prime h.nontrivial.ne').mem_primeFactors
    (Nat.minFac_dvd n) h.squarefree.ne_zero
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.nontrivial)
  have hrp : r ≠ p := by
    intro he
    have hlo := h.largest_lower
    change (43/80 : ℝ)*Real.log n ≤ Real.log p at hlo
    rw [← he] at hlo
    linarith [h.least_upper]
  have hx (i : ℕ) (hi : i ∈ S) : 0 ≤ x i := by
    exact div_nonneg (Real.log_natCast_nonneg _) hlog.le
  have hsum : ∑ i ∈ S, x i = 1 := (fullParityBox_shares h).2
  have hpx : (43/80 : ℝ) ≤ x p ∧ x p ≤ 9/16 :=
    ⟨(le_div_iff₀ hlog).mpr h.largest_lower, (div_le_iff₀ hlog).mpr h.largest_upper⟩
  have hrx : (3/250 : ℝ) ≤ x r ∧ x r ≤ 7/250 :=
    ⟨(le_div_iff₀ hlog).mpr h.least_lower, (div_le_iff₀ hlog).mpr h.least_upper⟩
  have hw := allocationWeight_nonneg S x hx
  let A := Finset.piAntidiag S (N+1)
  let E₁ := fun d : ℕ → ℕ => (d p : ℝ) < (21/40)*N
  let E₂ := fun d : ℕ → ℕ => (23/40 : ℝ)*N < d p
  let E₃ := fun d : ℕ → ℕ => (d r : ℝ) < (1/100)*N
  let E₄ := fun d : ℕ → ℕ => (1/25 : ℝ)*N-1 < d r
  have h₁ := coordinate_lower_tail S x hx hsum hp (q := 19/20) (b := 1557/1600)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [hpx.1]) rectangle_tail_rates.1 N
  have h₂ := coordinate_upper_tail S x hx hsum hp (q := 21/20) (b := 329/320) (D := 0)
    (by norm_num) (by norm_num) (by linarith [hpx.2]) rectangle_tail_rates.2.1 N
  have h₃ := coordinate_lower_tail S x hx hsum hr (q := 5/6) (b := 499/500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith [hrx.1]) rectangle_tail_rates.2.2.1 N
  have h₄ := coordinate_upper_tail S x hx hsum hr (q := 5/4) (b := 1007/1000) (D := 1)
    (by norm_num) (by norm_num) (by linarith [hrx.2]) rectangle_tail_rates.2.2.2 N
  simp only [sub_zero, zero_mul, Real.exp_zero, mul_one] at h₂
  simp only [one_mul, Real.exp_log (by norm_num : (0 : ℝ) < 5/4)] at h₄
  have hcover (d : ℕ → ℕ) (hd : d ∈ A) (hout : d ∉ rectangleAllocations N n) :
      E₁ d ∨ E₂ d ∨ E₃ d ∨ E₄ d := by
    by_contra he
    simp only [not_or, E₁, E₂, E₃, E₄, not_lt] at he
    have hjlo : 21*N ≤ 40*d p := by exact_mod_cast (show (21 : ℝ)*N ≤ 40*d p by linarith)
    have hjhi : 40*d p ≤ 23*N := by exact_mod_cast (show (40 : ℝ)*d p ≤ 23*N by linarith)
    have hrlo : N ≤ 100*(d r+1) := by
      exact_mod_cast (show (N : ℝ) ≤ 100*((d r : ℝ)+1) by linarith)
    have hrhi : 100*(d r+1) ≤ 4*N := by
      exact_mod_cast (show (100 : ℝ)*((d r : ℝ)+1) ≤ 4*N by linarith)
    have htot := (Finset.mem_piAntidiag.mp hd).1
    have heq := Finset.sum_erase_add S d hp
    rw [htot] at heq
    have hpart := Finset.single_le_sum (s := S.erase p) (f := d)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hrp, hr⟩)
    apply hout
    apply Finset.mem_filter.mpr
    refine ⟨hd, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · change d r < N+1-d p+1
      omega
    exact ⟨rectangle_mem_owner hjlo hjhi hrhi, hjlo, hjhi, hrlo, hrhi⟩
  have hbound : rectangleOmittedMass N n ≤
      (∑ d ∈ A.filter E₁, allocationWeight S x d)+
      (∑ d ∈ A.filter E₂, allocationWeight S x d)+
      (∑ d ∈ A.filter E₃, allocationWeight S x d)+
      (∑ d ∈ A.filter E₄, allocationWeight S x d) := by
    simp only [rectangleOmittedMass, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    by_cases hout : d ∉ rectangleAllocations N n
    · rw [if_pos hout]
      rcases hcover d hd hout with he | he | he | he <;>
        simp only [if_pos he] <;> split_ifs <;> linarith [hw d]
    · rw [if_neg hout]
      split_ifs <;> linarith [hw d]
  constructor
  · exact Finset.sum_nonneg (fun d _ => hw d)
  · change _ ≤ _ at h₁ h₂ h₃ h₄
    have hex : Real.exp (-(1/6000 : ℝ)*N) = Real.exp (-(N : ℝ)/6000) := by congr 1; ring
    rw [hex] at h₁ h₂ h₃ h₄
    dsimp only [E₁, E₂, E₃, E₄, A] at hbound
    linarith [Real.exp_pos (-(N : ℝ)/6000)]

end
end RiemannGaussian.ZetaRieszParityOrderTail
