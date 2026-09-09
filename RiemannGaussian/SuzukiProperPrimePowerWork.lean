/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiMassLogWork

/-!
# An independent logarithmic bound for proper-prime-power work

The contribution from proper prime powers can be bounded independently of
the signed correlation at ordinary primes. Finite Abel summation transfers
the unconditional Chebyshev square-root bound for `psi - theta` to a
logarithmic bound for the full weighted proper-prime-power mass. Canonical
center localization then bounds the absolute work on this entire part.

The ordinary-prime work remains signed and unchanged. Its required bound,
and hence the global RH goal, remain open.
-/

namespace RiemannGaussian
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology

private def properCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else ArithmeticFunction.vonMangoldt n

private theorem properCoefficient_prefix (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, properCoefficient n) = Chebyshev.psi x - Chebyshev.theta x := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [properCoefficient, hp, ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [properCoefficient, hp]

/-- The literal weighted mass of all proper prime powers up to a real endpoint.
Non-prime-powers carry zero von-Mangoldt weight. -/
def suzukiProperPrimePowerMass (b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
    if n.Prime then 0 else ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- An explicit square-root envelope for the complete proper-prime-power
counting mass, deduced from the existing Chebyshev bounds. -/
theorem chebyshevPsi_sub_theta_le_eighteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 18 * Real.sqrt x := by
  have hroot (n : ℕ) (hn : 2 ≤ n) :
      Chebyshev.psi (x ^ (1 / (n : ℝ))) ≤ 6 * Real.sqrt x := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 1 ≤ x ^ (1 / (n : ℝ)) := Real.one_le_rpow hx (by positivity)
    refine (chebyshevPsi_le_six_mul_self_of_one_le hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hx
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := hroot 2 (by norm_num)
  have h3 := hroot 3 (by norm_num)
  have h5 := hroot 5 (by norm_num)
  simp only [Nat.cast_ofNat, one_div] at h2 h3 h5
  linarith

private theorem integrable_power {b p : ℝ} :
    IntegrableOn (fun x : ℝ => x ^ p) (Icc 1 b) := by
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  exact (Real.continuousAt_rpow_const x p
    (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt

private theorem integrable_deriv_massKernel {b : ℝ} :
    IntegrableOn (deriv suzukiChebyshevMassKernel) (Icc 1 b) := by
  have hi : IntegrableOn (fun x : ℝ => (-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) (Icc 1 b) :=
    (integrable_power (b := b) (p := (-3 / 2 : ℝ))).const_mul (-1 / 2 : ℝ)
  apply hi.congr_fun
  · intro x hx
    exact (deriv_suzukiChebyshevMassKernel (zero_lt_one.trans_le hx.1)).symm
  · exact measurableSet_Icc

/-- Exact finite Abel identity for the proper-prime-power mass, retaining
its endpoint term and the complete `psi - theta` integral. -/
theorem suzukiProperPrimePowerMass_eq_abel {b : ℝ} (hb : 1 ≤ b) :
    suzukiProperPrimePowerMass b =
      b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - Chebyshev.theta b) +
        (1 / 2 : ℝ) * ∫ x in Ioc (1 : ℝ) b,
          x ^ (-3 / 2 : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) := by
  have h := sum_mul_eq_sub_sub_integral_mul properCoefficient
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (f := suzukiChebyshevMassKernel)
    (fun x hx => Real.differentiableAt_rpow_const_of_ne _ (by linarith [hx.1]))
    integrable_deriv_massKernel
  simp_rw [properCoefficient_prefix] at h
  simp only [Nat.floor_one, Chebyshev.psi_one, Chebyshev.theta_one, sub_self,
    mul_zero, sub_zero] at h
  have hsum : (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊, suzukiChebyshevMassKernel n * properCoefficient n) =
      suzukiProperPrimePowerMass b := by
    unfold suzukiProperPrimePowerMass
    apply Finset.sum_congr rfl
    intro n hn
    rw [suzukiChebyshevMassKernel_nat_eq]
    by_cases hp : n.Prime <;> simp [properCoefficient, hp, div_eq_mul_inv, mul_comm]
  rw [hsum] at h
  have hi : (∫ x in Ioc (1 : ℝ) b,
      deriv suzukiChebyshevMassKernel x * (Chebyshev.psi x - Chebyshev.theta x)) =
      (-1 / 2 : ℝ) * ∫ x in Ioc (1 : ℝ) b,
        x ^ (-3 / 2 : ℝ) * (Chebyshev.psi x - Chebyshev.theta x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [deriv_suzukiChebyshevMassKernel (zero_lt_one.trans hx.1)]
    ring
  rw [hi] at h
  unfold suzukiChebyshevMassKernel at h
  linarith

/-- The full weighted mass of proper prime powers grows at most logarithmically,
with explicit constants and no zero hypothesis. -/
theorem suzukiProperPrimePowerMass_le_log {b : ℝ} (hb : 1 ≤ b) :
    suzukiProperPrimePowerMass b ≤ 18 + 9 * Real.log b := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hsqrt {x : ℝ} (hx : 0 < x) (p : ℝ) :
      x ^ p * Real.sqrt x = x ^ (p + 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  have hbnd : b ^ (-1 / 2 : ℝ) * (Chebyshev.psi b - Chebyshev.theta b) ≤ 18 := by
    have h := mul_le_mul_of_nonneg_left (chebyshevPsi_sub_theta_le_eighteen_sqrt hb)
      (Real.rpow_nonneg hb0.le (-1 / 2 : ℝ))
    calc
      _ ≤ b ^ (-1 / 2 : ℝ) * (18 * Real.sqrt b) := h
      _ = 18 := by rw [mul_left_comm, hsqrt hb0]; norm_num
  have hf : IntegrableOn (fun x : ℝ =>
      x ^ (-3 / 2 : ℝ) * (Chebyshev.psi x - Chebyshev.theta x)) (Ioc 1 b) := by
    have hi := integrableOn_mul_sum_Icc properCoefficient
      (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) (integrable_power (p := (-3 / 2 : ℝ)))
    simp_rw [properCoefficient_prefix] at hi
    exact hi.mono_set Ioc_subset_Icc_self
  have hg : IntegrableOn (fun x : ℝ => 18 * x⁻¹) (Ioc 1 b) := by
    have hi : IntegrableOn (fun x : ℝ => x⁻¹) (Icc 1 b) := by
      apply ContinuousOn.integrableOn_Icc
      exact continuousOn_id.inv₀ (fun x hx => (zero_lt_one.trans_le hx.1).ne')
    have hi' : IntegrableOn (fun x : ℝ => 18 * x⁻¹) (Icc 1 b) := hi.const_mul 18
    exact hi'.mono_set Ioc_subset_Icc_self
  have hi : (∫ x in Ioc (1 : ℝ) b, x ^ (-3 / 2 : ℝ) *
      (Chebyshev.psi x - Chebyshev.theta x)) ≤ 18 * Real.log b := by
    have hm := setIntegral_mono_on hf hg measurableSet_Ioc (by
      intro x hx
      have hx0 : 0 < x := zero_lt_one.trans hx.1
      calc
        _ ≤ x ^ (-3 / 2 : ℝ) * (18 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (chebyshevPsi_sub_theta_le_eighteen_sqrt hx.1.le)
            (Real.rpow_nonneg hx0.le _)
        _ = 18 * x⁻¹ := by
          rw [mul_left_comm, hsqrt hx0]
          norm_num [Real.rpow_neg_one])
    have hlog : (∫ x in Ioc (1 : ℝ) b, 18 * x⁻¹) = 18 * Real.log b := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hb,
        integral_inv_of_pos zero_lt_one hb0, div_one]
    rw [hlog] at hm
    exact hm
  rw [suzukiProperPrimePowerMass_eq_abel hb]
  linarith

/-- The unchanged canonical work has magnitude bounded by five times its
actual prime-power atom, using both proved center-localization inequalities. -/
theorem abs_suzukiFirstTailTransportLinearWork_le_weight (count : ℕ) :
    |suzukiFirstTailTransportLinearWork count| ≤ 5 * suzukiPrimeWeight (count + 1) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let n : ℝ := ((count + 3 : ℕ) : ℝ)
  let r := suzukiFirstTailChebyshevCenter count
  have hb : 0 < b := by dsimp [b]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hlog : Real.log b ≤ Real.log n :=
    Real.log_le_log hb (by dsimp [b, n]; push_cast; linarith)
  have hlog' : Real.log n ≤ Real.log b + 1 := by
    calc
      Real.log n ≤ Real.log (2 * b) := Real.log_le_log hn (by
        dsimp [n, b]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) count])
      _ = Real.log 2 + Real.log b := Real.log_mul (by norm_num) hb.ne'
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have hl : Real.log b - 2 ≤ r := log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
  have hu : r < Real.log b + 5 := suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
  have hdisp : |Real.log n - r| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  unfold suzukiFirstTailTransportLinearWork suzukiPrimeLocation
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [abs_mul, abs_of_nonneg (suzukiPrimeWeight_nonnegative _)]
  exact (mul_le_mul_of_nonneg_left hdisp (suzukiPrimeWeight_nonnegative _)).trans_eq (by ring)

/-- Retaining the full mass logarithm changes the uniform atom bound by at
most one further atom, including the complete positive Lerch correction. -/
theorem abs_suzukiFirstTailMassLogWork_le_weight (count : ℕ) :
    |suzukiFirstTailMassLogWork count| ≤ 6 * suzukiPrimeWeight (count + 1) := by
  have hr : 0 < suzukiFirstTailChebyshevCenter count :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
      (log_two_le_suzukiFirstTailChebyshevCenter count)
  have he : Real.exp (-3 * suzukiFirstTailChebyshevCenter count) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have herror : suzukiFirstTailMassLogWorkError count ≤ suzukiPrimeWeight (count + 1) := by
    calc
      _ ≤ (8 / 15 : ℝ) * suzukiPrimeWeight (count + 1) *
          Real.exp (-3 * suzukiFirstTailChebyshevCenter count) := suzukiFirstTailMassLogWorkError_le_exp count
      _ ≤ (8 / 15 : ℝ) * suzukiPrimeWeight (count + 1) * 1 :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) (suzukiPrimeWeight_nonnegative _))
      _ ≤ _ := by linarith [suzukiPrimeWeight_nonnegative (count + 1)]
  have heq : suzukiFirstTailMassLogWork count = suzukiFirstTailTransportLinearWork count -
      suzukiFirstTailMassLogWorkError count := by
    linarith [suzukiFirstTailTransportLinearWork_eq_massLog_add_error count]
  rw [heq]
  have h := abs_sub (suzukiFirstTailTransportLinearWork count) (suzukiFirstTailMassLogWorkError count)
  rw [abs_of_nonneg (suzukiFirstTailMassLogWorkError_bounds count).1] at h
  linarith [abs_suzukiFirstTailTransportLinearWork_le_weight count]

/-- Exact alignment of the original event indexing and the complete weighted
proper-prime-power prefix; no prime-power endpoint is lost. -/
theorem suzukiProperPrimePowerMass_nat_eq (count : ℕ) :
    suzukiProperPrimePowerMass ((count + 2 : ℕ) : ℝ) =
      ∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else suzukiPrimeWeight (j + 1) := by
  have he : suzukiProperPrimePowerMass ((count + 2 : ℕ) : ℝ) =
      ∑ j ∈ Finset.range (count + 1), if (j + 2).Prime then 0 else suzukiPrimeWeight j := by
    unfold suzukiProperPrimePowerMass
    rw [Nat.floor_natCast]
    symm
    apply Finset.sum_bij (fun j _ => j + 2)
    · intro j hj
      simp only [Finset.mem_range, Finset.mem_Ioc] at hj ⊢
      omega
    · intro j hj k hk h
      omega
    · intro n hn
      refine ⟨n - 2, ?_, ?_⟩
      · simp only [Finset.mem_range, Finset.mem_Ioc] at hn ⊢
        omega
      · simp only [Finset.mem_Ioc] at hn
        omega
    · intro j hj
      rfl
  rw [he, Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.prime_two, if_true, add_zero, Nat.add_assoc, Nat.reduceAdd]

private theorem sum_nonprime_abs_le_log (f : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ j, |f j| ≤ C * suzukiPrimeWeight (j + 1)) (count : ℕ) :
    (∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else |f j|) ≤
      C * (18 + 9 * Real.log ((count + 2 : ℕ) : ℝ)) := by
  calc
    _ ≤ ∑ j ∈ Finset.range count,
        C * (if (j + 3).Prime then 0 else suzukiPrimeWeight (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hp : (j + 3).Prime
      · simp [hp]
      · simpa only [if_neg hp] using hf j
    _ = C * suzukiProperPrimePowerMass ((count + 2 : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, suzukiProperPrimePowerMass_nat_eq]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (suzukiProperPrimePowerMass_le_log (by norm_cast; omega)) hC

/-- The complete absolute work over proper prime powers has an independent
logarithmic bound. The ordinary-prime contribution is not estimated here. -/
theorem sum_abs_suzuki_proper_prime_power_linearWork_le_log (count : ℕ) :
    (∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else
      |suzukiFirstTailTransportLinearWork j|) ≤
        90 + 45 * Real.log ((count + 2 : ℕ) : ℝ) := by
  have h := sum_nonprime_abs_le_log suzukiFirstTailTransportLinearWork
    (C := 5) (by norm_num) abs_suzukiFirstTailTransportLinearWork_le_weight count
  linarith

/-- The finite arithmetic mass-log work of every proper prime power has an
independent logarithmic bound, even before cancellation among those events. -/
theorem sum_abs_suzuki_proper_prime_power_massLogWork_le_log (count : ℕ) :
    (∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else
      |suzukiFirstTailMassLogWork j|) ≤
        108 + 54 * Real.log ((count + 2 : ℕ) : ℝ) := by
  have h := sum_nonprime_abs_le_log suzukiFirstTailMassLogWork
    (C := 6) (by norm_num) abs_suzukiFirstTailMassLogWork_le_weight count
  linarith

/-- The signed part of the original work supported on proper prime powers. -/
def suzukiProperPrimePowerWork (count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else suzukiFirstTailTransportLinearWork j

/-- The unchanged signed work on ordinary primes; the entire old mass in
each cell remains present, including all preceding proper prime powers. -/
def suzukiOrdinaryPrimeWork (count : ℕ) : ℝ :=
  ∑ j ∈ Finset.range count, if (j + 3).Prime then suzukiFirstTailTransportLinearWork j else 0

/-- Exact splitting by the new atom's arithmetic support, without deleting
prime powers from the preceding mass or changing any canonical center. -/
theorem suzuki_signed_work_eq_ordinary_add_proper (count : ℕ) :
    (∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) =
      suzukiOrdinaryPrimeWork count + suzukiProperPrimePowerWork count := by
  unfold suzukiOrdinaryPrimeWork suzukiProperPrimePowerWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

/-- A uniform independent bound for the signed proper-prime-power part of
the original work, with its exact logarithmic growth allowance. -/
theorem abs_suzukiProperPrimePowerWork_le_log (count : ℕ) :
    |suzukiProperPrimePowerWork count| ≤ 90 + 45 * Real.log ((count + 2 : ℕ) : ℝ) := by
  unfold suzukiProperPrimePowerWork
  have h := Finset.abs_sum_le_sum_abs
    (fun j => if (j + 3).Prime then (0 : ℝ) else suzukiFirstTailTransportLinearWork j)
    (Finset.range count)
  simp only [apply_ite abs, abs_zero] at h
  exact h.trans (sum_abs_suzuki_proper_prime_power_linearWork_le_log count)

private theorem log_envelope_div_rpow_tendsto_zero (A B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun count : ℕ =>
      (A + B * Real.log ((count + 2 : ℕ) : ℝ)) / ((count + 2 : ℕ) : ℝ) ^ ε)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun count : ℕ => ((count + 2 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hA : Tendsto (fun count : ℕ => A / ((count + 2 : ℕ) : ℝ) ^ ε) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hε).comp hx)
  have hlog : Tendsto (fun count : ℕ =>
      Real.log ((count + 2 : ℕ) : ℝ) / ((count + 2 : ℕ) : ℝ) ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero.comp hx
  convert hA.add (hlog.const_mul B) using 1 <;> simp [add_div, mul_div_assoc]

/-- The entire absolute proper-prime-power work is smaller than every fixed
positive cutoff power. This estimate is unconditional and uses no cancellation. -/
theorem suzuki_proper_prime_power_absoluteWork_div_rpow_tendsto_zero
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun count : ℕ =>
      (∑ j ∈ Finset.range count, if (j + 3).Prime then 0 else
        |suzukiFirstTailTransportLinearWork j|) / ((count + 2 : ℕ) : ℝ) ^ ε)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun count => by positivity))
    (Eventually.of_forall (fun count =>
      div_le_div_of_nonneg_right (sum_abs_suzuki_proper_prime_power_linearWork_le_log count)
        (Real.rpow_nonneg (by positivity) ε)))
    (log_envelope_div_rpow_tendsto_zero 90 45 hε)

/-- Removing the proper-prime-power part changes the original signed work by
`o(N^ε)` for every `ε > 0`. A fixed finite error bound is not asserted. -/
theorem suzukiProperPrimePowerWork_div_rpow_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun count : ℕ =>
      suzukiProperPrimePowerWork count / ((count + 2 : ℕ) : ℝ) ^ ε) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (Eventually.of_forall (fun count => ?_))
    (log_envelope_div_rpow_tendsto_zero 90 45 hε)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (by positivity) ε)]
  exact div_le_div_of_nonneg_right (abs_suzukiProperPrimePowerWork_le_log count)
    (Real.rpow_nonneg (by positivity) ε)

/-- The exact discrepancy after retaining only ordinary-prime events obeys
the same logarithmic envelope. Every preceding prime power remains in the
mass and center used by those ordinary-prime events. -/
theorem abs_suzuki_signed_work_sub_ordinary_le_log (count : ℕ) :
    |(∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j) -
      suzukiOrdinaryPrimeWork count| ≤ 90 + 45 * Real.log ((count + 2 : ℕ) : ℝ) := by
  rw [suzuki_signed_work_eq_ordinary_add_proper, add_sub_cancel_left]
  exact abs_suzukiProperPrimePowerWork_le_log count

/-- A logarithmic lower allowance on the full work follows from a finite
floor on ordinary-prime work. This is an explicit comparison, not an RH
conclusion: a separate analytic allowance theorem is needed to conclude RH. -/
theorem suzuki_signed_work_lower_of_ordinary_lower {count : ℕ} {B : ℝ}
    (hb : -B ≤ suzukiOrdinaryPrimeWork count) :
    -(B + 90 + 45 * Real.log ((count + 2 : ℕ) : ℝ)) ≤
      ∑ j ∈ Finset.range count, suzukiFirstTailTransportLinearWork j := by
  rw [suzuki_signed_work_eq_ordinary_add_proper]
  have h := (abs_le.mp (abs_suzukiProperPrimePowerWork_le_log count)).1
  linarith

end
end RiemannGaussian
