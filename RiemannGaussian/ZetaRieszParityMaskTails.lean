/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityOrderPacket

/-!
# Quantitative factorial mask tails in the literal interior box

The tilts below are selected by the numerical rate audit, then checked
using exact rational powers and elementary exponential inequalities.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket

theorem coordinate_tilt_bound {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) {p : ι} (hp : p ∈ S) (M : ℕ)
    (E : ℕ → Prop) [DecidablePred E] {q B : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B)
    (htilt : ∀ k, E k → 1 ≤ B*q^k) :
    (∑ d ∈ (Finset.piAntidiag S M).filter (fun d => E (d p)), allocationWeight S x d) ≤
      B*(q*x p+∑ i ∈ S.erase p, x i)^M := by
  calc
    _ ≤ ∑ d ∈ (Finset.piAntidiag S M).filter (fun d => E (d p)),
        B*(q^(d p)*allocationWeight S x d) := by
      apply Finset.sum_le_sum
      intro d hd
      nlinarith [mul_le_mul_of_nonneg_right (htilt _ (Finset.mem_filter.mp hd).2)
        (allocationWeight_nonneg S x hx d)]
    _ ≤ ∑ d ∈ Finset.piAntidiag S M, B*(q^(d p)*allocationWeight S x d) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg hB
          (mul_nonneg (pow_nonneg hq _) (allocationWeight_nonneg S x hx d)))
    _ = _ := by rw [← Finset.mul_sum, allocation_tilt S x hp]

/-- A one-coordinate lower tail retaining the exact multinomial weights. -/
theorem coordinate_lower_tail {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hsum : ∑ i ∈ S, x i = 1) {p : ι} (hp : p ∈ S)
    {a b q c : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hbase : 1-x p+q*x p ≤ b) (hrate : Real.log b-a*Real.log q ≤ -c) (N : ℕ) :
    (∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => (d p : ℝ) < a*N),
      allocationWeight S x d) ≤ Real.exp (-c*N) := by
  have hlog : Real.log q ≤ 0 := Real.log_nonpos hq0.le hq1
  have hB : 0 < Real.exp (-a*N*Real.log q) := Real.exp_pos _
  have ht := coordinate_tilt_bound S x hx hp (N+1) (fun k => (k : ℝ) < a*N)
    hq0.le hB.le (by
      intro k hk
      rw [show q^k = Real.exp ((k : ℝ)*Real.log q) by
        rw [Real.exp_nat_mul, Real.exp_log hq0], ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonpos_right hk.le hlog])
  have hsum' := Finset.sum_erase_add S x hp
  rw [hsum] at hsum'
  have hbase0 : 0 ≤ q*x p+∑ i ∈ S.erase p, x i :=
    add_nonneg (mul_nonneg hq0.le (hx p hp))
      (Finset.sum_nonneg (fun i hi => hx i (Finset.mem_of_mem_erase hi)))
  calc
    _ ≤ _ := ht
    _ ≤ Real.exp (-a*N*Real.log q)*b^(N+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 (by linarith) _) hB.le
    _ ≤ Real.exp (-a*N*Real.log q)*b^N := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (pow_nonneg hb0.le _) hb1) hB.le
    _ = Real.exp ((Real.log b-a*Real.log q)*N) := by
      rw [show b^N = Real.exp ((N : ℝ)*Real.log b) by
        rw [Real.exp_nat_mul, Real.exp_log hb0], ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N))

/-- The upper tail includes the exact additive derivative-order shift. -/
theorem coordinate_upper_tail {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hsum : ∑ i ∈ S, x i = 1) {p : ι} (hp : p ∈ S)
    {a b q c D : ℝ} (hq : 1 ≤ q) (hb : 0 < b)
    (hbase : 1-x p+q*x p ≤ b) (hrate : Real.log b-a*Real.log q ≤ -c) (N : ℕ) :
    (∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => a*N-D < (d p : ℝ)),
      allocationWeight S x d) ≤ b*Real.exp (D*Real.log q)*Real.exp (-c*N) := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  have hB := Real.exp_pos (-(a*N-D)*Real.log q)
  have ht := coordinate_tilt_bound S x hx hp (N+1) (fun k => a*N-D < (k : ℝ))
    hq0.le hB.le (by
      intro k hk
      rw [show q^k = Real.exp ((k : ℝ)*Real.log q) by
        rw [Real.exp_nat_mul, Real.exp_log hq0], ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_right hk.le hlog])
  have hsum' := Finset.sum_erase_add S x hp
  rw [hsum] at hsum'
  have hbase0 : 0 ≤ q*x p+∑ i ∈ S.erase p, x i :=
    add_nonneg (mul_nonneg hq0.le (hx p hp))
      (Finset.sum_nonneg (fun i hi => hx i (Finset.mem_of_mem_erase hi)))
  calc
    _ ≤ _ := ht
    _ ≤ Real.exp (-(a*N-D)*Real.log q)*b^(N+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 (by linarith) _) hB.le
    _ = b*Real.exp (D*Real.log q)*Real.exp ((Real.log b-a*Real.log q)*N) := by
      rw [pow_succ, show b^N = Real.exp ((N : ℝ)*Real.log b) by
        rw [Real.exp_nat_mul, Real.exp_log hb]]
      rw [show Real.exp (-(a*N-D)*Real.log q)*(Real.exp ((N : ℝ)*Real.log b)*b) =
          b*(Real.exp (-(a*N-D)*Real.log q)*Real.exp ((N : ℝ)*Real.log b)) by ring,
        show b*Real.exp (D*Real.log q)*Real.exp ((Real.log b-a*Real.log q)*N) =
          b*(Real.exp (D*Real.log q)*Real.exp ((Real.log b-a*Real.log q)*N)) by ring,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N)))
      (mul_nonneg hb.le (Real.exp_pos _).le)

/-- Rational power comparison certifies a logarithmic tilt rate. -/
theorem log_rate_of_power {q b c : ℝ} (hq : 0 < q) (hb : 0 < b)
    (a m : ℕ) (hm : 0 < m) (h : b^m/q^a ≤ 1-(m : ℝ)*c) :
    Real.log b-((a : ℝ)/m)*Real.log q ≤ -c := by
  have he : b^m/q^a ≤ Real.exp (-(m : ℝ)*c) :=
    h.trans (by linarith [Real.add_one_le_exp (-(m : ℝ)*c)])
  have hl := Real.log_le_log (div_pos (pow_pos hb _) (pow_pos hq _)) he
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp] at hl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_iff_right₀ hmR).mp
  calc
    _ = (m : ℝ)*Real.log b-a*Real.log q := by field_simp
    _ ≤ _ := by nlinarith

/-- All four concrete rectangle boundaries have source-beating margins. -/
theorem rectangle_tail_rates :
    Real.log (1557/1600 : ℝ)-(21/40)*Real.log (19/20) ≤ -(1/6000) ∧
    Real.log (329/320 : ℝ)-(23/40)*Real.log (21/20) ≤ -(1/6000) ∧
    Real.log (499/500 : ℝ)-(1/100)*Real.log (5/6) ≤ -(1/6000) ∧
    Real.log (1007/1000 : ℝ)-(1/25)*Real.log (5/4) ≤ -(1/6000) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact log_rate_of_power (by norm_num) (by norm_num) 21 40 (by decide) (by norm_num)
  · exact log_rate_of_power (by norm_num) (by norm_num) 23 40 (by decide) (by norm_num)
  · simpa using log_rate_of_power (q := 5/6) (b := 499/500) (c := 1/6000)
      (by norm_num) (by norm_num) 1 100 (by decide) (by norm_num)
  · simpa using log_rate_of_power (q := 5/4) (b := 1007/1000) (c := 1/6000)
      (by norm_num) (by norm_num) 1 25 (by decide) (by norm_num)

end
end RiemannGaussian.ZetaRieszParityOrderTail
