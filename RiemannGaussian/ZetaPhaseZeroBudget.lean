/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseArithmetic
import RiemannGaussian.ZetaPhaseShiftEnvelope

/-!
# The actual signed zero budget of a complete phase family

The constant coefficient pays the real-axis pole and a fixed logarithmic
cost. The nonconstant coefficients pay their total mass and their actual
logarithmic frequency overhead. These are different from the linear cost
used in the earlier phase optimization.

The shifted source inequality retains the complete arithmetic prime work,
the selected zero's multiplicity, and the quadratic nonreal pole allowance.
The statements apply to finite or countably infinite integer-frequency
families with the displayed genuine summability hypotheses.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Total coefficient mass at nonconstant frequencies. -/
def phaseOscillatoryMass (a : ℕ → ℝ) : ℝ := ∑' n : ℕ, a (n + 1)

/-- The actual logarithmic overhead at nonconstant integer frequencies. -/
def phaseLogFrequencyMass (a : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, a (n + 1) * Real.log ((n + 1 : ℕ) : ℝ)

/-- The nonconstant coefficient mass retains its arithmetic sign. -/
theorem phaseOscillatoryMass_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    0 ≤ phaseOscillatoryMass a := tsum_nonneg fun n ↦ ha (n + 1)

/-- A finite logarithmic frequency moment suffices for the actual height
cost. No finite support or linear frequency moment is required. -/
theorem summable_phase_height_of_logFrequency {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hlog : Summable (fun n : ℕ ↦ a n * Real.log n)) (y : ℝ) :
    Summable (fun n : ℕ ↦ a n * localZetaLogHeight ((n : ℝ) * y)) := by
  apply ((hs.mul_right (localZetaLogHeight y + localZetaLogHeight 0)).add hlog).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (ha n) (by linarith [two_lt_localZetaLogHeight ((n : ℝ) * y)]))]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_mul, Real.log_zero, mul_zero, add_zero]
    nlinarith [ha 0, two_lt_localZetaLogHeight y]
  · have h := mul_le_mul_of_nonneg_left
      (localZetaLogHeight_mul_le_add_log (k := (n : ℝ))
        (by exact_mod_cast (show 1 ≤ n by omega)) y) (ha n)
    have h0 := mul_nonneg (ha n)
      (show 0 ≤ localZetaLogHeight 0 by linarith [two_lt_localZetaLogHeight 0])
    linarith

/-- Separate the fixed zero-frequency cost from the actual logarithmic
height growth, keeping the logarithmic frequency overhead. -/
theorem phase_height_le_split_budget {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hlog : Summable (fun n : ℕ ↦ a n * Real.log n)) (y : ℝ)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight ((n : ℝ) * y))) :
    (∑' n : ℕ, a n * localZetaLogHeight ((n : ℝ) * y)) ≤
      a 0 * localZetaLogHeight 0 + phaseOscillatoryMass a * localZetaLogHeight y +
        phaseLogFrequencyMass a := by
  rw [hL.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul]
  have htail := hL.comp_injective (i := fun n : ℕ ↦ n + 1) (fun _ _ h ↦ Nat.add_right_cancel h)
  have hmass := hs.comp_injective (i := fun n : ℕ ↦ n + 1) (fun _ _ h ↦ Nat.add_right_cancel h)
  have hlogs := hlog.comp_injective (i := fun n : ℕ ↦ n + 1) (fun _ _ h ↦ Nat.add_right_cancel h)
  dsimp only [Function.comp_def] at htail hmass hlogs
  have hupper := (hmass.mul_right (localZetaLogHeight y)).add hlogs
  have hb := htail.tsum_le_tsum (fun n ↦ show
      a (n + 1) * localZetaLogHeight (((n + 1 : ℕ) : ℝ) * y) ≤
        a (n + 1) * localZetaLogHeight y + a (n + 1) * Real.log ((n + 1 : ℕ) : ℝ) from by
    have h := mul_le_mul_of_nonneg_left
      (localZetaLogHeight_mul_le_add_log (k := ((n + 1 : ℕ) : ℝ))
        (by exact_mod_cast (show 1 ≤ n + 1 by omega)) y) (ha (n + 1))
    linarith) hupper
  rw [(hmass.mul_right (localZetaLogHeight y)).tsum_add hlogs, tsum_mul_right] at hb
  change _ ≤ phaseOscillatoryMass a * localZetaLogHeight y + phaseLogFrequencyMass a at hb
  linarith

/-- The real pole is paid only by the constant coefficient. The remaining
exact Cauchy terms have a quadratic-height allowance proportional to their
total mass. -/
theorem phase_exactPole_le_split_budget {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {x y : ℝ} (hx : 0 < x) (hy : y ≠ 0) :
    (∑' n : ℕ, a n * (x / (x ^ 2 + ((n : ℝ) * y) ^ 2))) ≤
      a 0 / x + phaseOscillatoryMass a * x / y ^ 2 := by
  have hp := summable_zetaPhase_exactPole (ω := fun n ↦ (n : ℝ)) ha hs hx y
  rw [hp.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hz : a 0 * (x / x ^ 2) = a 0 / x := by field_simp
  rw [hz]
  have hmass := hs.comp_injective (i := fun n : ℕ ↦ n + 1) (fun _ _ h ↦ Nat.add_right_cancel h)
  have htail := hp.comp_injective (i := fun n : ℕ ↦ n + 1) (fun _ _ h ↦ Nat.add_right_cancel h)
  have hupper := hmass.mul_right (x / y ^ 2)
  have hb := htail.tsum_le_tsum (fun n ↦ show
      a (n + 1) * (x / (x ^ 2 + (((n + 1 : ℕ) : ℝ) * y) ^ 2)) ≤
        a (n + 1) * (x / y ^ 2) from by
    apply mul_le_mul_of_nonneg_left _ (ha (n + 1))
    apply div_le_div_of_nonneg_left hx.le (sq_pos_of_ne_zero hy)
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hprod := mul_nonneg (show 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 - 1 by nlinarith)
      (sq_nonneg y)
    nlinarith [sq_nonneg x]) hupper
  rw [tsum_mul_right] at hb
  change _ ≤ phaseOscillatoryMass a * (x / y ^ 2) at hb
  rw [mul_div_assoc]
  linarith

/-- The shifted source from a literal zero is constrained by the complete
prime work, the actual height cost, and the retained quadratic pole error.
No positivity of the phase kernel is needed until the arithmetic work is
used as an independent nonnegative contribution. -/
theorem phase_shifted_source_add_primeWork_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ * (1 - rho.1.re) ≤ 1 / 4)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight ((n : ℝ) * rho.1.im))) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) * (∑' n : ℕ, a n * localZetaLogHeight ((n : ℝ) * rho.1.im)) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hmain := zetaPhase_primeWork_add_localZeros_le
    (ω := fun n ↦ (n : ℝ)) ha hs hx hκsmall rho.1.im hL
  have hz := (summable_zetaPhase_localZeros (ω := fun n ↦ (n : ℝ))
    ha hs hx hκsmall rho.1.im hL).le_tsum 1
      (fun n _ ↦ mul_nonneg (ha n) (localZetaPoleSum_re_nonneg _ hx))
  have hsource := mul_le_mul_of_nonneg_left
    (multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx) (ha 1)
  have hpole := phase_exactPole_le_split_budget ha hs hx
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  simp only [Nat.cast_one, one_mul] at hz
  have hsum : a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d) +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * d) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        448 * ∑' n : ℕ, a n * localZetaLogHeight ((n : ℝ) * rho.1.im) := by
    simp only [zetaPhaseKernel_natCast] at hmain
    rw [show κ * d + 1 - rho.1.re = κ * d + d by dsimp [d]; ring] at hsource
    rw [← mul_div_assoc] at hsource
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  have he1 : d * (a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d)) =
      a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ + 1) := by
    have hk1 : κ + 1 ≠ 0 := by positivity
    field_simp
  have he0 : d * (a 0 / (κ * d)) = a 0 / κ := by field_simp
  simp only [mul_add] at hm
  rw [he1, he0] at hm
  change phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ + d * _ ≤ _
  unfold phaseShiftSource
  dsimp only [d] at hm ⊢
  linear_combination hm

/-- A family-independent constraint on actual zeros: the complete signed
prime work and the multiplicity source share the true mass/logarithmic budget.
Only coefficient summability and a logarithmic moment are required; there
is no prescribed phase count, linear cost, optimizer, or kernel positivity. -/
theorem phase_shifted_source_add_primeWork_le_split_budget {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ ↦ a n * Real.log n))
    (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ * (1 - rho.1.re) ≤ 1 / 4) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) *
        (a 0 * localZetaLogHeight 0 + phaseOscillatoryMass a * localZetaLogHeight rho.1.im +
          phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hL := summable_phase_height_of_logFrequency ha hs hlog rho.1.im
  have h := phase_shifted_source_add_primeWork_le ha hs rho hrho hκ hκsmall hL
  have hheight := mul_le_mul_of_nonneg_left (phase_height_le_split_budget ha hs hlog rho.1.im hL)
    (show 0 ≤ 448 * (1 - rho.1.re) by
      exact mul_nonneg (by norm_num) (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)).le)
  linarith

/-- Every finite prime-phase window at an actual zero is bounded by the
remaining source deficit. This is an independently testable arithmetic
constraint for any admissible family, with all omitted terms proved nonnegative. -/
theorem phase_finite_primeWork_le_zero_defect {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ ↦ a n * Real.log n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t)
    (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ * (1 - rho.1.re) ≤ 1 / 4) (S : Finset ℕ) :
    (1 - rho.1.re) * (∑ m ∈ S,
      zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      448 * (1 - rho.1.re) *
        (a 0 * localZetaLogHeight 0 + phaseOscillatoryMass a * localZetaLogHeight rho.1.im +
          phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 -
        phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have h := phase_shifted_source_add_primeWork_le_split_budget ha hs hlog rho hrho hκ hκsmall
  have hf := zetaPhase_finite_primeWork_le (ω := fun n ↦ (n : ℝ)) ha hs
    (fun t ↦ by simpa only [zetaPhaseKernel_natCast] using hp t)
    (show 1 < 1 + κ * (1 - rho.1.re) by nlinarith [mul_pos hκ hd]) rho.1.im S
  simp only [zetaPhaseKernel_natCast] at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  linarith

end

end RiemannGaussian
