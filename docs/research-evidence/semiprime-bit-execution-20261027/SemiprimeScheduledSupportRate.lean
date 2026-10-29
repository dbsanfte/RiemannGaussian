/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSupportRate
import RiemannGaussian.SemiprimeSourceLayoutRate

/-! # The actual scheduled support traversal is subexponential
This closes the support-count estimate without the unpinned aggregate constant
16435. It is an estimate for the literal callback count, not a machine clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace RiemannGaussian.SemiprimeScheduledSupportRate
open Filter
open scoped Topology
open SemiprimeCounterRate SemiprimeSourceLayoutRate SemiprimeSupportRate

/-- Inclusive support cutoff at the source degree and sample count, using
the public network's proved incidence count 2n. -/
def cutoff (n : ℕ) : ℕ :=
  2*n*scheduledDegree (Nat.clog 2 n)/scheduledPointCount (Nat.clog 2 n)

/-- Floor rounding in Q and ceiling rounding in R retain a vanishing R/Q ratio. -/
theorem degree_point_ratio_bound {lam : ℕ} (hν : 64≤Nat.clog 2 lam) :
    2*(scheduledDegree lam : ℝ)/(scheduledPointCount lam : ℝ)≤
      4096*(Nat.clog 2 lam : ℝ)/Real.sqrt (lam : ℝ) := by
  have hranges := scheduled_parameter_ranges hν
  have hQ : 1 ≤ scheduledPointCount lam := by omega
  have hlam : 1<lam := by
    by_contra h
    have hz := Nat.clog_of_right_le_one (show lam≤1 by omega) 2
    omega
  have hνpos : 0<128*Nat.clog 2 lam := by omega
  have hfloor : lam<(scheduledPointCount lam+1)*(128*Nat.clog 2 lam) := by
    exact (Nat.div_lt_iff_lt_mul hνpos).mp (Nat.lt_succ_self _)
  have hsmall : lam≤256*Nat.clog 2 lam*scheduledPointCount lam := by
    nlinarith
  have hsmallR : (lam : ℝ)≤256*(Nat.clog 2 lam : ℝ)*(scheduledPointCount lam : ℝ) := by
    exact_mod_cast hsmall
  have hroot : (1 : ℝ)≤Real.sqrt (lam : ℝ) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast (show 1≤lam by omega))
  have hceil : scheduledCeilSqrt lam≤Nat.sqrt lam+1 := by
    unfold scheduledCeilSqrt
    split_ifs <;> omega
  have hceilR : (scheduledCeilSqrt lam : ℝ)≤(Nat.sqrt lam : ℝ)+1 := by exact_mod_cast hceil
  have hdeg : (scheduledDegree lam : ℝ)≤8*Real.sqrt (lam : ℝ) := by
    have hnat := Real.nat_sqrt_le_real_sqrt (a := lam)
    simp only [scheduledDegree,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  have hQpos : (0 : ℝ)<scheduledPointCount lam := Nat.cast_pos.mpr (by omega)
  have hspos : (0 : ℝ)<Real.sqrt (lam : ℝ) := by positivity
  apply (div_le_div_iff₀ hQpos hspos).mpr
  have hm := mul_le_mul_of_nonneg_right hdeg hspos.le
  have hs := Real.sq_sqrt (show (0 : ℝ)≤lam by positivity)
  nlinarith

/-- The actual binary ceiling logarithm divided by the real square root tends
to zero; no smooth replacement is silently substituted for the integer ceil. -/
theorem clog_sqrt_ratio_zero :
    Tendsto (fun n : ℕ => (Nat.clog 2 n : ℝ)/Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_neg_atTop (show (0 : ℝ)<1/4 by norm_num)).comp hnat
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hlim
  filter_upwards [eventually_clog_power_le_rpow 1 (1/4) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hn hpos
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hpow : (n : ℝ)^(1/4 : ℝ)/Real.sqrt (n : ℝ)=(n : ℝ)^(-(1/4) : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_sub hnR]
    norm_num
  change (Nat.clog 2 n : ℝ)/Real.sqrt (n : ℝ)≤(n : ℝ)^(-(1/4) : ℝ)
  rw [← hpow]
  apply div_le_div_of_nonneg_right
  · simpa only [pow_one] using hn
  · positivity

/-- The actual public degree/sample ratio tends to zero along the integer schedule. -/
theorem degree_point_ratio_zero :
    Tendsto (fun lam : ℕ => 2*(scheduledDegree lam : ℝ)/(scheduledPointCount lam : ℝ))
      atTop (𝓝 0) := by
  have hlim := clog_sqrt_ratio_zero.const_mul 4096
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall (fun lam => by positivity)) ?_ hlim
  filter_upwards [tendsto_clog_two_atTop.eventually (eventually_ge_atTop 64)] with lam hlam
  simpa only [mul_div_assoc] using degree_point_ratio_bound hlam

/-- Natural floor division cannot increase the normalized support budget. -/
theorem cutoff_ratio_bound (n : ℕ) (hn : 0<n) :
    (cutoff n : ℝ)/(n : ℝ)≤
      2*(scheduledDegree (Nat.clog 2 n) : ℝ)/(scheduledPointCount (Nat.clog 2 n) : ℝ) := by
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hn
  have hd : (cutoff n : ℝ)≤
      ((2*n*scheduledDegree (Nat.clog 2 n) : ℕ) : ℝ)/(scheduledPointCount (Nat.clog 2 n) : ℝ) :=
    Nat.cast_div_le
  apply (div_le_iff₀ hnR).mpr
  convert hd using 1
  push_cast
  ring

/-- The actual inclusive Taylor cutoff is a vanishing fraction of the network. -/
theorem cutoff_ratio_zero : Tendsto (fun n : ℕ => (cutoff n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have hlim := degree_point_ratio_zero.comp tendsto_clog_two_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact cutoff_ratio_bound n (by omega)

/-- Literal source support callbacks satisfy every positive exponential target. -/
theorem scheduled_support_subexponential (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (SemiprimeCounterEnumeration.weightedCount n (cutoff n) : ℝ)≤Real.exp (ε*(n : ℝ)) :=
  weightedCount_subexponential cutoff cutoff_ratio_zero ε hε

end RiemannGaussian.SemiprimeScheduledSupportRate
