/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteCatalog
import RiemannGaussian.RosserSchoenfeldAnchor

/-!
# Exact primorial certificates for the finite Chebyshev bounds

The proved complete prime catalog gives the literal primorial. Rational
bounds on exp(1) convert logarithmic endpoint inequalities to natural-number
power comparisons. Closed-cell monotonicity then covers every real point.
-/

namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
open RosserSchoenfeldFiniteBounds
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

/-- The product of every prime at or below the finite endpoint. -/
def prefixProduct (n : ℕ) : ℕ :=
  ((catalog16000.filter (fun p => decide (p ≤ n)))).prod

/-- The complete catalog product equals the actual primorial. -/
theorem primorial_eq_prefixProduct {n : ℕ} (hn : n ≤ 16000) :
    primorial n = prefixProduct n := by
  rw [primorial_eq_prod_primesLE,
    primesLE_eq_filtered_catalog catalog_complete_16000 hn,
    List.prod_toFinset _ (catalog_nodup.filter _)]
  simp [prefixProduct]

/-- An exact integer comparison gives a strict real logarithmic lower bound. -/
theorem log_lower {M L : ℕ} (hM : 0 < M)
    (hc : 11135 ^ L < 4096 ^ L * M) : (L : ℝ) < Real.log M := by
  apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hM)).mpr
  have he : Real.exp 1 ≤ (11135 / 4096 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he L
  rw [← Real.exp_nat_mul] at hp
  simp only [mul_one] at hp
  refine hp.trans_lt ?_
  rw [div_pow, div_lt_iff₀ (by positivity)]
  have hh : ((11135 ^ L : ℕ) : ℝ) < ((4096 ^ L * M : ℕ) : ℝ) := Nat.cast_lt.mpr hc
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hh

/-- An exact integer comparison gives a strict real logarithmic upper bound. -/
theorem log_upper {M U : ℕ} (hM : 0 < M)
    (hc : 4096 ^ U * M < 11134 ^ U) : Real.log M < (U : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr hM)).mpr
  have he : (11134 / 4096 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11134 / 4096) he U
  rw [← Real.exp_nat_mul] at hp
  simp only [mul_one] at hp
  refine lt_of_lt_of_le ?_ hp
  rw [div_pow, lt_div_iff₀ (by positivity)]
  have hh : ((4096 ^ U * M : ℕ) : ℝ) < ((11134 ^ U : ℕ) : ℝ) := Nat.cast_lt.mpr hc
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hh

/-- Two checked power comparisons enclose the actual finite Chebyshev value. -/
theorem theta_bounds_of_check {n L U : ℕ} (hn : n ≤ 16000)
    (hL : 11135 ^ L < 4096 ^ L * prefixProduct n)
    (hU : 4096 ^ U * prefixProduct n < 11134 ^ U) :
    (L : ℝ) < Chebyshev.theta n ∧ Chebyshev.theta n < U := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, primorial_eq_prefixProduct hn]
  have hp : 0 < prefixProduct n := by
    rw [← primorial_eq_prefixProduct hn]
    exact primorial_pos n
  exact ⟨log_lower hp hL, log_upper hp hU⟩

/-- Strict rational margins sufficient for the two published theta allowances. -/
def checkCell (a b L U : ℕ) : Bool := decide (
  ((b : ℚ)-L) * (logBox b).hi < (47/100) * a ∧
  ((U : ℚ)-a) * (logBox b).hi < (31/100) * a)

/-- Checked endpoint values and logarithmic margins cover a closed real cell. -/
theorem cell_bounds {a b L U : ℕ} (ha : 1 < a) (hab : a ≤ b)
    (hL : (L : ℝ) < Chebyshev.theta a) (hU : Chebyshev.theta b < (U : ℝ))
    (hc : checkCell a b L U = true)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) b) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  have haR : (1 : ℝ) < a := by exact_mod_cast ha
  have hb : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (ha.trans_le hab)
  have hx1 : 1 < x := haR.trans_le hx.1
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hH := (mem_logBox hb).2
  have hHpos : 0 < ((logBox b).hi : ℝ) := (Real.log_pos hbR).trans_le hH
  have hlxH : Real.log x ≤ ((logBox b).hi : ℝ) :=
    (Real.log_le_log (by linarith) hx.2).trans hH
  simp only [checkCell, decide_eq_true_eq] at hc
  have hcL : ((b : ℝ)-L) * ((logBox b).hi : ℝ) < (47/100) * a := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.1
    push_cast at hh
    exact hh
  have hcU : ((U : ℝ)-a) * ((logBox b).hi : ℝ) < (31/100) * a := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.2
    push_cast at hh
    exact hh
  have hcL' := (lt_div_iff₀ hHpos).mpr hcL
  have hcU' := (lt_div_iff₀ hHpos).mpr hcU
  have hcomp (c : ℝ) (hc0 : 0 ≤ c) :
      c*a/((logBox b).hi : ℝ) ≤ c*x/Real.log x := by
    apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hx.1 hc0) hlx hlxH
  have hLc := hcomp (47/100) (by norm_num)
  have hUc := hcomp (31/100) (by norm_num)
  have htL := hL.trans_le (Chebyshev.theta_mono hx.1)
  have htU := (Chebyshev.theta_mono hx.2).trans_lt hU
  constructor <;> linarith [hx.1, hx.2]

/-- Adjacent closed cells retain their shared endpoint and cover their union. -/
theorem join {a b c : ℝ}
    (h₁ : ∀ x ∈ Set.Icc a b, x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x)
    (h₂ : ∀ x ∈ Set.Icc b c, x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x) :
    ∀ x ∈ Set.Icc a c, x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  intro x hx
  by_cases h : x ≤ b
  · exact h₁ x ⟨hx.1, h⟩
  · exact h₂ x ⟨le_of_not_ge h, hx.2⟩

end RiemannGaussian.RosserSchoenfeldFiniteTheta
