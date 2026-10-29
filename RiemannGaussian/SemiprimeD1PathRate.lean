/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1Schedule

/-! # Fixed-constant path exponent for the literal dyadic D.1 schedule
No asymptotic replacement of the actual floors or supplied reciprocal-level
bound is assumed. This concerns retained positive levels, not failing leaves.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PathRate
open scoped BigOperators
open SemiprimeD1Schedule

/-- An actual positive floor quotient pays at most twice its dyadic block. -/
theorem floor_dyadic (b d : ℕ) (hu : 0<b/2^d) : b ≤ 2^(d+1)*(b/2^d) := by
  have hp : 0<(2:ℕ)^d := by positivity
  have hf:=Nat.lt_mul_div_succ b hp
  have hmul:=Nat.mul_le_mul_left (2^d) (show 1 ≤ b/2^d by omega)
  rw [pow_succ]
  nlinarith

/-- Exact integer floors imply the coarse but geometric-friendly square-root bound. -/
theorem sqrt_floor_le (b d : ℕ) (hu : 0<b/2^d) :
    Real.sqrt (b:ℝ) ≤ (2:ℝ)^(d+1)*Real.sqrt (b/2^d:ℕ) := by
  have hb : (b:ℝ) ≤ (2:ℝ)^(d+1)*(b/2^d:ℕ) := by exact_mod_cast floor_dyadic b d hu
  have hpow : (1:ℝ) ≤ (2:ℝ)^(d+1) := by
    exact_mod_cast (Nat.succ_le_of_lt (pow_pos (by decide : 0<(2:ℕ)) (d+1)))
  have hu0 : (0:ℝ) ≤ (b/2^d:ℕ) := by positivity
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_pow,Real.sq_sqrt hu0]
  have hh : (2:ℝ)^(d+1) ≤ ((2:ℝ)^(d+1))^2 := by nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_right hh hu0)

/-- Every actual path node contributes a dyadically summable fraction. -/
theorem node_term_le (s b d M : ℕ) (hu : 0<b/2^d) (hm : M*8^d ≤ s) :
    (M:ℝ)/Real.sqrt (b/2^d:ℕ) ≤ 
      (2*(s:ℝ)/Real.sqrt (b:ℝ))*(1/4:ℝ)^d := by
  have hbpos : 0<b := by
    have hle:=Nat.div_le_self b (2^d)
    omega
  have hsu : 0<Real.sqrt (b/2^d:ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast hu)
  have hsb : 0<Real.sqrt (b:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hbpos)
  have hsqrt:=sqrt_floor_le b d hu
  have hM : (M:ℝ)*(8:ℝ)^d ≤ s := by exact_mod_cast hm
  have he : (2:ℝ)^(d+1)*(4:ℝ)^d=2*(8:ℝ)^d := by
    rw [pow_succ]
    have h : (2:ℝ)^d*(4:ℝ)^d=(8:ℝ)^d := by rw [←mul_pow];norm_num
    nlinarith
  have hc : (M:ℝ)*(Real.sqrt (b:ℝ)*(4:ℝ)^d) ≤ 2*(s:ℝ)*Real.sqrt (b/2^d:ℕ) := by
    calc
      _  ≤  (M:ℝ)*((2:ℝ)^(d+1)*Real.sqrt (b/2^d:ℕ))*(4:ℝ)^d := by
        have hh:=mul_le_mul_of_nonneg_left hsqrt (show (0:ℝ) ≤ M by positivity)
        have hz:=mul_le_mul_of_nonneg_right hh (show (0:ℝ) ≤ (4:ℝ)^d by positivity)
        nlinarith
      _ = 2*((M:ℝ)*(8:ℝ)^d)*Real.sqrt (b/2^d:ℕ) := by
        calc
          _ = (M:ℝ)*Real.sqrt (b/2^d:ℕ)*((2:ℝ)^(d+1)*(4:ℝ)^d) := by ring
          _ = _ := by rw [he];ring
      _  ≤  _ := by nlinarith
  have hden : 0<Real.sqrt (b:ℝ)*(4:ℝ)^d := by positivity
  have hdiv := (div_le_div_iff₀ hsu hden).mpr hc
  convert hdiv using 1
  rw [div_pow,one_pow]
  field_simp

/-- A finite geometric path has a universal bound, independent of depth. -/
theorem geometric_path (depth : ℕ) : (∑d∈Finset.range depth,(1/4:ℝ)^d) ≤ 2 := by
  have haux : ∀n,(∑d∈Finset.range n,(1/4:ℝ)^d)+2*(1/4:ℝ)^n ≤ 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ,pow_succ]
      have hp : (0:ℝ) ≤ (1/4:ℝ)^n := by positivity
      nlinarith
  have hp : (0:ℝ) ≤ (1/4:ℝ)^depth := by positivity
  linarith [haux depth]

/-- Root floor balance from the actual fixed epsilon denominator. -/
theorem root_floor_bound (lam : ℕ) (hlam : epsilonDenominator ≤ lam) :
    lam ≤ 262144*(lam/epsilonDenominator) := by
  have hpos : 0<epsilonDenominator := by norm_num [epsilonDenominator]
  have hf:=Nat.lt_mul_div_succ lam hpos
  have hb : 1 ≤ lam/epsilonDenominator := Nat.div_pos hlam hpos
  norm_num only [epsilonDenominator] at hf hb ⊢
  omega

/-- The literal floor root has the required fixed512 square-root factor. -/
theorem sqrt_root_bound (lam : ℕ) (hlam : epsilonDenominator ≤ lam) :
    Real.sqrt (lam:ℝ) ≤ 512*Real.sqrt (lam/epsilonDenominator:ℕ) := by
  have hb : (lam:ℝ) ≤ 262144*(lam/epsilonDenominator:ℕ) := by exact_mod_cast root_floor_bound lam hlam
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ (lam/epsilonDenominator:ℕ))]
  norm_num
  exact hb

/-- Inactive zero levels contribute exactlyzero, not an undefined reciprocal. -/
noncomputable def term (lam : ℕ) (edges : ℕ→ℕ) (d : ℕ) : ℝ :=
  if levels lam d=0 then 0 else (edges d:ℝ)/Real.sqrt (levels lam d:ℕ)

/-- Actual positive-level path sum, with all floors and fixed constant2048. -/
theorem path_sum_le (s lam depth : ℕ) (edges : ℕ→ℕ)
    (hlam : epsilonDenominator ≤ lam)
    (hpath : ∀d<depth,edges d*8^d ≤ s) :
    (∑d∈Finset.range depth,term lam edges d) ≤ 2048*(s:ℝ)/Real.sqrt (lam:ℝ) := by
  have hb : 0<lam/epsilonDenominator := Nat.div_pos hlam (by norm_num [epsilonDenominator])
  have hsb : 0<Real.sqrt (lam/epsilonDenominator:ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast hb)
  have hlpos : 0<lam := lt_of_lt_of_le (by norm_num [epsilonDenominator]) hlam
  have hsl : 0<Real.sqrt (lam:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hlpos)
  have hterm (d : ℕ) (hd : d∈Finset.range depth) :
      term lam edges d ≤ (2*(s:ℝ)/Real.sqrt (lam/epsilonDenominator:ℕ))*(1/4:ℝ)^d := by
    by_cases hu : levels lam d=0
    · simp only [term,hu,ite_true]
      positivity
    · have hp : 0<(lam/epsilonDenominator)/2^d := by change 0<levels lam d;omega
      rw [term,ite_eq_right hu]
      simpa only [levels] using node_term_le s (lam/epsilonDenominator) d (edges d) hp (hpath d (Finset.mem_range.mp hd))
  have hsum:=Finset.sum_le_sum hterm
  have hg:=geometric_path depth
  have hc : 0 ≤ 2*(s:ℝ)/Real.sqrt (lam/epsilonDenominator:ℕ) := by positivity
  rw [←Finset.mul_sum] at hsum
  have hgeom:=mul_le_mul_of_nonneg_left hg hc
  have hr:=sqrt_root_bound lam hlam
  have hlast : 4*(s:ℝ)/Real.sqrt (lam/epsilonDenominator:ℕ) ≤ 
      2048*(s:ℝ)/Real.sqrt (lam:ℝ) := by
    apply (div_le_div_iff₀ hsb hsl).mpr
    nlinarith
  calc
    _  ≤  (2*(s:ℝ)/Real.sqrt (lam/epsilonDenominator:ℕ))*2 := hsum.trans hgeom
    _ = 4*(s:ℝ)/Real.sqrt (lam/epsilonDenominator:ℕ) := by ring
    _  ≤  _ := hlast

/-- The actual weighted-mode constant48 yields the fixed path exponent98304. -/
theorem mode_path_sum_le (s lam depth : ℕ) (edges : ℕ→ℕ)
    (hlam : epsilonDenominator ≤ lam) (hpath : ∀d<depth,edges d*8^d ≤ s) :
    48*(∑d∈Finset.range depth,term lam edges d) ≤ 98304*(s:ℝ)/Real.sqrt (lam:ℝ) := by
  have h:=mul_le_mul_of_nonneg_left (path_sum_le s lam depth edges hlam hpath)
    (by norm_num : (0:ℝ) ≤ 48)
  convert h using 1;ring

/-- Every defined path term is nonnegative, including inactive zero levels. -/
theorem term_nonneg (lam : ℕ) (edges : ℕ→ℕ) (d : ℕ) : 0 ≤ term lam edges d := by
  unfold term
  split_ifs <;> positivity

/-- Actual schedule activity masks the path without assuming extra analytic bounds. -/
noncomputable def activeTerm (s lam : ℕ) (edges : ℕ→ℕ) (d : ℕ) : ℝ := by
  classical
  exact if Active s lam d (edges d) then term lam edges d else 0

/-- The same fixed constant controls only the actual active schedule nodes. -/
theorem active_path_sum_le (s lam depth : ℕ) (edges : ℕ→ℕ)
    (hlam : epsilonDenominator ≤ lam) (hpath : ∀d<depth,edges d*8^d ≤ s) :
    (∑d∈Finset.range depth,activeTerm s lam edges d) ≤ 2048*(s:ℝ)/Real.sqrt (lam:ℝ) := by
  have h : (∑d∈Finset.range depth,activeTerm s lam edges d) ≤
      ∑d∈Finset.range depth,term lam edges d := by
    apply Finset.sum_le_sum
    intro d _
    unfold activeTerm
    split_ifs
    · exact le_rfl
    · exact term_nonneg lam edges d
  exact h.trans (path_sum_le s lam depth edges hlam hpath)

/-- Actual active weighted-mode path exponent, with the literal factor48. -/
theorem active_mode_path_sum_le (s lam depth : ℕ) (edges : ℕ→ℕ)
    (hlam : epsilonDenominator ≤ lam) (hpath : ∀d<depth,edges d*8^d ≤ s) :
    48*(∑d∈Finset.range depth,activeTerm s lam edges d) ≤ 98304*(s:ℝ)/Real.sqrt (lam:ℝ) := by
  have h:=mul_le_mul_of_nonneg_left (active_path_sum_le s lam depth edges hlam hpath)
    (by norm_num : (0:ℝ) ≤ 48)
  convert h using 1;ring

end RiemannGaussian.SemiprimeD1PathRate
