/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackingReady

/-! # Auxiliary table and rank exponents fit the explicit main scale
The actual rounded degree cap and every fixed logarithmic power are paid at
s/sqrt(clog2(s+2)), rather than merely described as sublinear. This arithmetic
lemma does not identify any retained report with a primitive-machine runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1AuxiliaryRate
open Filter SemiprimeD1PackingReady
open scoped Topology

/-- Every fixed actual ceiling-log power is eventually below the original size. -/
theorem eventually_log_power (k : ℕ) : ∀ᶠ s : ℕ in atTop,(logarithm s)^k ≤ s := by
  have hlog := (tendsto_add_atTop_nat 2).eventually
    (SemiprimeSourceLayoutRate.eventually_clog_power_le_rpow k (1/2) (by norm_num))
  filter_upwards [hlog,eventually_ge_atTop (3:ℕ)] with s hl hs
  rw [←Real.sqrt_eq_rpow] at hl
  have hsR : (3:ℝ) ≤ s := by exact_mod_cast hs
  have hroot : Real.sqrt (s+2:ℕ) ≤ (s:ℝ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    push_cast
    nlinarith [sq_nonneg ((s:ℝ)-2)]
  exact_mod_cast hl.trans hroot

/-- Rounding the actual nine-tenths logarithmic exponent costs a fixed factor. -/
theorem degreeCap_tenth (s : ℕ) (hs : 2 ≤ s) (hl : 2 ≤ logarithm s) :
    (degreeCap s)^10 ≤ 2^27*s^9 := by
  have hp := root_power s hs hl
  have he : ((9*logarithm s+9)/10)*10 ≤ 9*(logarithm s-2)+27 := by omega
  calc
    _ = 2^(((9*logarithm s+9)/10)*10) := by rw [degreeCap,←pow_mul]
    _ ≤ 2^(9*(logarithm s-2)+27) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) he
    _ = 2^27*(2^(logarithm s-2))^9 := by
      rw [pow_add,Nat.mul_comm 9 (logarithm s-2),pow_mul]
      exact Nat.mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 9)

/-- The actual complete-table exponent leaves a full logarithmic reserve. -/
theorem eventually_degree_times_log : ∀ᶠ s : ℕ in atTop,degreeCap s*logarithm s ≤ s := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [eventually_log_power 11,eventually_ge_atTop (2:ℕ),
    ht.eventually (eventually_ge_atTop (2^27:ℕ))] with s hlog hs hl
  have hltwo : 2 ≤ logarithm s := by omega
  have hd := degreeCap_tenth s hs hltwo
  have hreserve : 2^27*(logarithm s)^10 ≤ s := by
    calc
      _ ≤ logarithm s*(logarithm s)^10 := Nat.mul_le_mul_right _ hl
      _ = (logarithm s)^11 := by ring
      _ ≤ s := hlog
  have hpower : (degreeCap s*logarithm s)^10 ≤ s^10 := by
    calc
      _ = (degreeCap s)^10*(logarithm s)^10 := by rw [mul_pow]
      _ ≤ (2^27*s^9)*(logarithm s)^10 := Nat.mul_le_mul_right _ hd
      _ = s^9*(2^27*(logarithm s)^10) := by ring
      _ ≤ s^9*s := Nat.mul_le_mul_left _ hreserve
      _ = s^10 := by ring
  exact (Nat.pow_le_pow_iff_left (by decide : (10:ℕ) ≠ 0)).mp hpower

/-- A fixed cubic logarithmic exponent leaves the same reserve. -/
theorem eventually_log_fourth : ∀ᶠ s : ℕ in atTop,(logarithm s+1)^4 ≤ s := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [eventually_log_power 5,ht.eventually (eventually_ge_atTop (16:ℕ))] with s hp hl
  calc
    _ ≤ (2*logarithm s)^4 := Nat.pow_le_pow_left (by omega) 4
    _ = 16*(logarithm s)^4 := by ring
    _ ≤ logarithm s*(logarithm s)^4 := Nat.mul_le_mul_right _ hl
    _ = (logarithm s)^5 := by ring
    _ ≤ s := hp

/-- Both actual auxiliary exponent types are absorbed at the quantitative
requested scale. No extra logarithmic loss is introduced by this estimate. -/
theorem eventually_auxiliary_rate : ∀ᶠ s : ℕ in atTop,
    ((degreeCap s+(logarithm s+1)^3:ℕ):ℝ) ≤
      2*(s:ℝ)/Real.sqrt (logarithm s:ℕ) := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [eventually_degree_times_log,eventually_log_fourth,
    ht.eventually (eventually_ge_atTop (1:ℕ))] with s hd hp hl
  have hlR : (1:ℝ) ≤ logarithm s := by exact_mod_cast hl
  have hroot : 0 < Real.sqrt (logarithm s:ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : Real.sqrt (logarithm s:ℕ) ≤ (logarithm s:ℝ) := by
    have hh := Real.sq_sqrt (show (0:ℝ) ≤ logarithm s by positivity)
    nlinarith [Real.sqrt_nonneg (logarithm s:ℕ)]
  have hdR : (degreeCap s:ℝ)*(logarithm s:ℝ) ≤ s := by exact_mod_cast hd
  have hpR : ((logarithm s:ℝ)+1)^4 ≤ s := by exact_mod_cast hp
  apply (le_div_iff₀ hroot).mpr
  push_cast
  have hdegree := mul_le_mul_of_nonneg_left hsqrt (show (0:ℝ) ≤ degreeCap s by positivity)
  have hpoly := mul_le_mul_of_nonneg_left (hsqrt.trans (le_add_of_nonneg_right zero_le_one))
    (show (0:ℝ) ≤ ((logarithm s:ℝ)+1)^3 by positivity)
  nlinarith

end RiemannGaussian.SemiprimeD1AuxiliaryRate
