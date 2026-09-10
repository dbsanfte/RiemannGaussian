/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGlobalSignedBudget
import RiemannGaussian.ZetaPhaseZeroBudget

/-!
# Arbitrary phase families and the complete global zero budget

The actual prime work and the full genuine zero mass obey a common
logarithmic allowance for every summable nonnegative phase family with
finite logarithmic height cost. All infinite sums are justified. The exact
Gamma correction remains available alongside its independent upper bound.

Selecting a zero keeps its full analytic multiplicity. Neither a prescribed
frequency count nor a numerical optimizer is needed. These inequalities
reduce the analytic allowance but do not prove the remaining arithmetic
floor needed to exclude every right-half zero.
-/

namespace RiemannGaussian
noncomputable section
open Complex
open scoped Topology

variable {ω : ℕ → ℝ}

private theorem pole_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    x / (x ^ 2 + t ^ 2) ≤ 1 / x := by
  calc
    _ ≤ x / x ^ 2 := div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx)
      (by nlinarith [sq_nonneg t])
    _ = _ := by field_simp

/-- The whole zero mass converges after summing against any admissible
real-frequency family. Its actual sign supplies domination from the
global arithmetic identity, without a local analytic remainder. -/
theorem summable_zetaPhase_globalZeros {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (1 + x + |ω n * y|)))) :
    Summable (fun n : ℕ => a n *
      ∑' rho : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) rho) := by
  let D := (-logDeriv riemannZeta ((1 + x : ℝ) : ℂ)).re
  have hbound (n : ℕ) :
      (∑' rho : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) rho) ≤
          1 / x + D + (1 + Real.log (1 + x + |ω n * y|)) := by
    have h := zeta_global_vertical_budget_le hx (ω n * y)
    have hn := norm_neg_logDeriv_riemannZeta_re_le_real_axis
      (by linarith : 1 < 1 + x) (ω n * y)
    rw [Real.norm_eq_abs] at hn
    have hp := pole_le hx (ω n * y)
    have hd := (abs_le.mp hn).1
    dsimp only [D]
    linarith
  apply ((hs.mul_right (1 / x + D)).add hH).of_norm_bounded
  intro n
  have hZ : 0 ≤ ∑' rho : NontrivialZetaZero,
      zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) rho :=
    tsum_nonneg (fun rho => zetaGlobalPoissonSummand_nonneg (by simp; linarith) rho)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n) hZ)]
  have h := mul_le_mul_of_nonneg_left (hbound n) (ha n)
  nlinarith only [h]

/-- The literal regular Gamma terms also converge for the whole family.
This follows by reassembling the already convergent signed arithmetic,
zero, and pole channels; it does not assume a norm bound for digamma. -/
theorem summable_zetaPhase_globalRegular {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (1 + x + |ω n * y|)))) :
    Summable (fun n : ℕ => a n *
      (zetaGlobalRegularCorrection (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  have hD := summable_zetaPhase_logDeriv (ω := ω) ha hs (by linarith : 1 < 1 + x) y
  have hZ := summable_zetaPhase_globalZeros ha hs hx y hH
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs hx y
  apply ((hD.add hZ).sub hP).congr
  intro n
  have he := zeta_global_real_budget
    (s := ((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) (by simp; linarith)
  have hp : (1 / ((((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) - 1) : ℂ).re =
      x / (x ^ 2 + (ω n * y) ^ 2) := by simp [Complex.normSq_apply, pow_two]
  rw [hp] at he
  linear_combination a n * he

/-- The actual prime work and complete global zero mass have an exact
joint identity for every admissible finite or countably infinite phase
family. The full signed Gamma correction is retained. -/
theorem zetaPhase_primeWork_add_globalZeros_eq {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (1 + x + |ω n * y|)))) :
    (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) rho) =
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * y) ^ 2))) +
        ∑' n : ℕ, a n *
          (zetaGlobalRegularCorrection (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
  rw [(hasSum_zetaPhase_arithmetic (ω := ω) ha hs (by linarith : 1 < 1 + x) y).tsum_eq]
  have hD := summable_zetaPhase_logDeriv (ω := ω) ha hs (by linarith : 1 < 1 + x) y
  have hZ := summable_zetaPhase_globalZeros ha hs hx y hH
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs hx y
  have hR := summable_zetaPhase_globalRegular ha hs hx y hH
  rw [← hD.tsum_add hZ, ← hP.tsum_add hR]
  apply tsum_congr
  intro n
  have he := zeta_global_real_budget
    (s := ((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) (by simp; linarith)
  have hp : (1 / ((((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) - 1) : ℂ).re =
      x / (x ^ 2 + (ω n * y) ^ 2) := by simp [Complex.normSq_apply, pow_two]
  rw [hp] at he
  linear_combination a n * he

/-- The entire prime work and all genuine zero contributions fit inside
the explicit logarithmic allowance, uniformly in the family and without
a small-displacement or selected-zero-location restriction. -/
theorem zetaPhase_primeWork_add_globalZeros_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {x : ℝ} (hx : 0 < x) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (1 + x + |ω n * y|)))) :
    (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaGlobalPoissonSummand (((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) rho) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * y) ^ 2))) +
        ∑' n : ℕ, a n * (1 + Real.log (1 + x + |ω n * y|)) := by
  rw [zetaPhase_primeWork_add_globalZeros_eq ha hs hx y hH]
  refine add_le_add le_rfl ?_
  apply (summable_zetaPhase_globalRegular ha hs hx y hH).tsum_le_tsum _ hH
  intro n
  apply mul_le_mul_of_nonneg_left _ (ha n)
  simpa using re_zetaGlobalRegularCorrection_le
    (s := ((1 + x : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ)) (by simp; linarith)

/-- Each chosen actual zero keeps its full multiplicity in the arbitrary
family inequality. The complete signed prime work remains on the left. -/
theorem zetaPhase_global_multiplicity_add_primeWork_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (r : ℕ) (hr : ω r = 1)
    (rho : NontrivialZetaZero) {x : ℝ} (hx : 0 < x)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (1 + x + |ω n * rho.1.im|)))) :
    a r * (analyticZetaZeroMultiplicity rho : ℝ) / (1 + x - rho.1.re) +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + x) m *
        zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        ∑' n : ℕ, a n * (1 + Real.log (1 + x + |ω n * rho.1.im|)) := by
  have h := zetaPhase_primeWork_add_globalZeros_le ha hs hx rho.1.im hH
  have hsigma : 1 ≤ 1 + x := by linarith
  have hZ := (summable_zetaPhase_globalZeros ha hs hx rho.1.im hH).le_tsum r
    (fun n _ => mul_nonneg (ha n) (tsum_nonneg (fun zeta =>
      zetaGlobalPoissonSummand_nonneg (by simp; linarith) zeta)))
  rw [hr, one_mul] at hZ
  have hsingle := (summable_zetaGlobalPoissonSummand
    (s := ((1 + x : ℝ) : ℂ) + I * rho.1.im) (by simpa using hsigma)).le_tsum rho
      (fun zeta _ => zetaGlobalPoissonSummand_nonneg (by simpa using hsigma) zeta)
  rw [zetaGlobalPoissonSummand_at_ordinate rho hsigma] at hsingle
  have hm := mul_le_mul_of_nonneg_left hsingle (ha r)
  rw [← mul_div_assoc] at hm
  linarith

private theorem nat_height_le {σ : ℝ} (hσ : 1 < σ) (y : ℝ) (n : ℕ) :
    1 + Real.log (σ + |(n : ℝ) * y|) ≤
      1 + Real.log (σ + |y|) + Real.log n := by
  have hσ0 : 0 < σ := by linarith
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_mul, abs_zero, add_zero, Real.log_zero]
    have h := Real.log_le_log hσ0 (show σ ≤ σ + |y| by linarith [abs_nonneg y])
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hn0 : (0 : ℝ) < n := by linarith
    have hprod : σ + |(n : ℝ) * y| ≤ (n : ℝ) * (σ + |y|) := by
      rw [abs_mul, abs_of_pos hn0]
      nlinarith
    have h := Real.log_le_log (by positivity : 0 < σ + |(n : ℝ) * y|) hprod
    rw [Real.log_mul hn0.ne' (by positivity : σ + |y| ≠ 0)] at h
    linarith

/-- Absolute coefficient summability and a logarithmic frequency moment
discharge the global height convergence for every integer-frequency
family, every safe abscissa, and every real ordinate. -/
theorem summable_phase_globalHeight_of_logFrequency {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    Summable (fun n : ℕ => a n * (1 + Real.log (σ + |(n : ℝ) * y|))) := by
  apply ((hs.mul_right (1 + Real.log (σ + |y|))).add hlog).of_norm_bounded
  intro n
  have hh : 0 ≤ 1 + Real.log (σ + |(n : ℝ) * y|) := by
    have hl := Real.log_nonneg (show 1 ≤ σ + |(n : ℝ) * y| by linarith [abs_nonneg ((n : ℝ) * y)])
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha n) hh)]
  have h := mul_le_mul_of_nonneg_left (nat_height_le hσ y n) (ha n)
  nlinarith only [h]

/-- The constant frequency pays only its fixed correction. All other
frequencies pay their total mass and their actual logarithmic overhead.
The bound holds over every finite or infinite admissible family. -/
theorem phase_global_height_le_split_budget {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (∑' n : ℕ, a n * (1 + Real.log (σ + |(n : ℝ) * y|))) ≤
      a 0 * (1 + Real.log σ) +
        phaseOscillatoryMass a * (1 + Real.log (σ + |y|)) + phaseLogFrequencyMass a := by
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog hσ y
  rw [hH.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, abs_zero, add_zero]
  have htail := hH.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  have hmass := hs.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  have hlogs := hlog.comp_injective (i := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)
  dsimp only [Function.comp_def] at htail hmass hlogs
  have hupper := (hmass.mul_right (1 + Real.log (σ + |y|))).add hlogs
  have hb := htail.tsum_le_tsum (fun n => show
      a (n + 1) * (1 + Real.log (σ + |((n + 1 : ℕ) : ℝ) * y|)) ≤
        a (n + 1) * (1 + Real.log (σ + |y|)) + a (n + 1) * Real.log (n + 1 : ℕ) from by
    have h := mul_le_mul_of_nonneg_left (nat_height_le hσ y (n + 1)) (ha (n + 1))
    nlinarith only [h]) hupper
  rw [(hmass.mul_right (1 + Real.log (σ + |y|))).tsum_add hlogs, tsum_mul_right] at hb
  change _ ≤ phaseOscillatoryMass a * (1 + Real.log (σ + |y|)) + phaseLogFrequencyMass a at hb
  linarith

/-- Every actual nontrivial zero satisfies the stronger shifted source
inequality for every admissible integer-frequency family and every positive
shift. The complete arithmetic work and the exact multiplicity remain on
the left; the independent allowance is logarithmic with coefficient one. -/
theorem phase_shifted_source_add_primeWork_le_global {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (∑' n : ℕ, a n *
        (1 + Real.log (1 + κ * (1 - rho.1.re) + |(n : ℝ) * rho.1.im|))) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog
    (by linarith : 1 < 1 + κ * d) rho.1.im
  have hmain := zetaPhase_global_multiplicity_add_primeWork_le
    (ω := fun n => (n : ℝ)) ha hs 1 (by norm_num) rho hx hH
  have hpole := phase_exactPole_le_split_budget ha hs hx
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  rw [show 1 + κ * d - rho.1.re = κ * d + d by dsimp [d]; ring] at hmain
  simp only [zetaPhaseKernel_natCast] at hmain
  have hsum : a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d) +
      (∑' m : ℕ, zetaPhasePrimeWeight (1 + κ * d) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        ∑' n : ℕ, a n * (1 + Real.log (1 + κ * d + |(n : ℝ) * rho.1.im|)) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  have he1 : d * (a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d)) =
      a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ + 1) := by
    have hk1 : κ + 1 ≠ 0 := by positivity
    field_simp
  have he0 : d * (a 0 / (κ * d)) = a 0 / κ := by field_simp
  simp only [mul_add] at hm
  rw [he1, he0] at hm
  unfold phaseShiftSource
  dsimp only [d] at hm ⊢
  simp only [mul_add, mul_one] at hm ⊢
  linear_combination hm

/-- The global source inequality with the constant phase, oscillatory
mass, and logarithmic frequency overhead separated. All convergence
hypotheses are discharged by the stated family moments. -/
theorem phase_shifted_source_add_primeWork_le_global_split {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) *
        (a 0 * (1 + Real.log (1 + κ * (1 - rho.1.re))) +
          phaseOscillatoryMass a * (1 + Real.log (1 + κ * (1 - rho.1.re) + |rho.1.im|)) +
            phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hb := mul_le_mul_of_nonneg_left
    (phase_global_height_le_split_budget ha hs hlog
      (by nlinarith [mul_pos hκ hd] : 1 < 1 + κ * (1 - rho.1.re)) rho.1.im) hd.le
  exact (phase_shifted_source_add_primeWork_le_global ha hs hlog rho hκ).trans
    (add_le_add hb le_rfl)

/-- Any finite arithmetic window at a genuine zero obeys the stronger
global deficit bound. Kernel positivity is used only here to control the
omitted prime powers; the complete signed identity remains available.
No restriction on the selected zero's real part or positive shift is needed. -/
theorem phase_finite_primeWork_le_global_zero_defect {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t)
    (rho : NontrivialZetaZero) {κ : ℝ} (hκ : 0 < κ) (S : Finset ℕ) :
    (1 - rho.1.re) * (∑ m ∈ S,
      zetaPhasePrimeWeight (1 + κ * (1 - rho.1.re)) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) *
        (a 0 * (1 + Real.log (1 + κ * (1 - rho.1.re))) +
          phaseOscillatoryMass a * (1 + Real.log (1 + κ * (1 - rho.1.re) + |rho.1.im|)) +
            phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 -
        phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have h := phase_shifted_source_add_primeWork_le_global_split ha hs hlog rho hκ
  have hf := zetaPhase_finite_primeWork_le (ω := fun n => (n : ℝ)) ha hs
    (fun t => by simpa only [zetaPhaseKernel_natCast] using hp t)
    (show 1 < 1 + κ * (1 - rho.1.re) by nlinarith [mul_pos hκ hd]) rho.1.im S
  simp only [zetaPhaseKernel_natCast] at hf
  have hm := mul_le_mul_of_nonneg_left hf hd.le
  linarith

end
end RiemannGaussian
