/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PathRate

/-! # Exact eighth-ratio mode exponent with the unchanged integer floors -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1HybridPathRate
open SemiprimeD1PathRate

/-- Every actual path node contributes a dyadically summable fraction. -/
theorem node_term_le (s b d M : ℕ) (hu : 0<b/2^d) (hm : M*16^d ≤ s) :
    (M:ℝ)/Real.sqrt (b/2^d:ℕ) ≤
      (2*(s:ℝ)/Real.sqrt (b:ℝ))*(1/8:ℝ)^d := by
  have hbpos : 0<b := by
    have hle:=Nat.div_le_self b (2^d)
    omega
  have hsu : 0<Real.sqrt (b/2^d:ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast hu)
  have hsb : 0<Real.sqrt (b:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hbpos)
  have hsqrt:=sqrt_floor_le b d hu
  have hM : (M:ℝ)*(16:ℝ)^d ≤ s := by exact_mod_cast hm
  have he : (2:ℝ)^(d+1)*(8:ℝ)^d=2*(16:ℝ)^d := by
    rw [pow_succ]
    have h : (2:ℝ)^d*(8:ℝ)^d=(16:ℝ)^d := by rw [←mul_pow];norm_num
    nlinarith
  have hc : (M:ℝ)*(Real.sqrt (b:ℝ)*(8:ℝ)^d) ≤ 2*(s:ℝ)*Real.sqrt (b/2^d:ℕ) := by
    calc
      _  ≤  (M:ℝ)*((2:ℝ)^(d+1)*Real.sqrt (b/2^d:ℕ))*(8:ℝ)^d := by
        have hh:=mul_le_mul_of_nonneg_left hsqrt (show (0:ℝ) ≤ M by positivity)
        have hz:=mul_le_mul_of_nonneg_right hh (show (0:ℝ) ≤ (8:ℝ)^d by positivity)
        nlinarith
      _ = 2*((M:ℝ)*(16:ℝ)^d)*Real.sqrt (b/2^d:ℕ) := by
        calc
          _ = (M:ℝ)*Real.sqrt (b/2^d:ℕ)*((2:ℝ)^(d+1)*(8:ℝ)^d) := by ring
          _ = _ := by rw [he];ring
      _  ≤  _ := by nlinarith
  have hden : 0<Real.sqrt (b:ℝ)*(8:ℝ)^d := by positivity
  have hdiv := (div_le_div_iff₀ hsu hden).mpr hc
  convert hdiv using 1
  rw [div_pow,one_pow]
  field_simp

end RiemannGaussian.SemiprimeD1HybridPathRate
