import RiemannGaussian.EtaCurrentMidpointBounds

/-!
# Summable arithmetic endpoint bounds for the midpoint correction

Every positive zero coordinate supplies a strict summability margin after
the new endpoint decay is divided by the arithmetic cutoff. Fixed powers
of the actual logarithmic cutoff fit inside that margin. Both completed
channels retain their explicit constants in the combined majorant.
-/

open Complex Filter MeasureTheory Set Topology Asymptotics
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every fixed power of the actual logarithmic cutoff is summable after
division by an arithmetic power strictly greater than one. -/
theorem summable_pairedEtaCurrent_logPower_div_rpow (k : ℕ) {p : ℝ} (hp : 1 < p) :
    Summable (fun N : ℕ ↦ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k / (N + 1 : ℝ) ^ p) := by
  let z : ℕ → ℝ := fun N ↦ Real.exp 1 * (2 * N + 5)
  have hz : Tendsto z atTop atTop :=
    (tendsto_atTop_add_const_right atTop 5
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul_atTop
        (Real.exp_pos 1)
  have hl := ((isLittleO_log_rpow_rpow_atTop (k : ℝ)
    (by linarith : (0 : ℝ) < (p - 1) / 2)).comp_tendsto hz).bound (by norm_num : (0 : ℝ) < 1)
  have hs := ((Real.summable_one_div_nat_add_rpow 1 ((p + 1) / 2)).2 (by linarith)).mul_left
    ((5 * Real.exp 1) ^ ((p - 1) / 2))
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [hl] with N hN
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hzpos : 0 < z N := by dsimp [z]; positivity
  have hlog : Real.log (z N) = 1 + pairedEtaLogTailCutoff (N + 2) := by
    dsimp [z, pairedEtaLogTailCutoff]
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
    push_cast
    congr 2
    ring
  have hpow : (1 + pairedEtaLogTailCutoff (N + 2)) ^ k ≤ (z N) ^ ((p - 1) / 2) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, hlog,
      Real.norm_of_nonneg (by positivity : 0 ≤ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k),
      Real.norm_of_nonneg (Real.rpow_nonneg hzpos.le _), one_mul] using hN
  have hzle : z N ≤ (5 * Real.exp 1) * (N + 1 : ℝ) := by
    dsimp [z]
    have he := Real.exp_pos 1
    have hn := Nat.cast_nonneg (α := ℝ) N
    nlinarith
  have hrpow := Real.rpow_le_rpow hzpos.le hzle (by linarith : (0 : ℝ) ≤ (p - 1) / 2)
  rw [Real.mul_rpow (by positivity) hx.le] at hrpow
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((5 * Real.exp 1) ^ ((p - 1) / 2) * (N + 1 : ℝ) ^ ((p - 1) / 2)) / (N + 1 : ℝ) ^ p :=
      div_le_div_of_nonneg_right (hpow.trans hrpow) (by positivity)
    _ = (5 * Real.exp 1) ^ ((p - 1) / 2) * (1 / (N + 1 : ℝ) ^ ((p + 1) / 2)) := by
      rw [mul_div_assoc, ← Real.rpow_sub hx, show (p - 1) / 2 - p = -((p + 1) / 2) by ring,
        Real.rpow_neg hx.le]
      simp only [one_div]
    _ = _ := by rw [abs_of_pos hx]

/-- Dividing the actual endpoint decay by the cutoff gives a power with
the strictly positive zero coordinate added to one. -/
theorem pairedEtaCurrentMomentDecay_div_le (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) ^ (1 + rho.1.re) := by
  have hx : 0 < (N + 1 : ℝ) := by positivity
  have hq : (N + 1 : ℝ) ≤ ((2 * (N + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * (N + 1) + 1 by omega)
  calc
    _ ≤ (N + 1 : ℝ) ^ (-rho.1.re) / (N + 1 : ℝ) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx hq
        (neg_nonpos.mpr (NontrivialZetaZero.zero_lt_re rho).le)) hx.le
    _ = (N + 1 : ℝ) ^ (-rho.1.re) / (N + 1 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_sub hx, show -rho.1.re - 1 = -(1 + rho.1.re) by ring, Real.rpow_neg hx.le, one_div]

/-- Fixed logarithmic powers preserve summability of the actual endpoint
decay divided by the cutoff, for every actual zero. -/
theorem summable_pairedEtaCurrent_logPower_mul_decay_div (rho : NontrivialZetaZero) (k : ℕ) :
    Summable (fun N : ℕ ↦ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k *
      pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) := by
  have hs := summable_pairedEtaCurrent_logPower_div_rpow k
    (by linarith [NontrivialZetaZero.zero_lt_re rho] : 1 < 1 + rho.1.re)
  apply hs.of_nonneg_of_le
  · intro N
    have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
    have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
    positivity
  · intro N
    have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
    simpa only [← mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left
      (pairedEtaCurrentMomentDecay_div_le rho N)
      (show 0 ≤ (1 + pairedEtaLogTailCutoff (N + 2)) ^ k by positivity)

/-- Both actual completed endpoint channels in the midpoint majorant
remain summable with their explicit constants and logarithmic cutoff. -/
theorem summable_pairedEtaCurrent_midpointEnvelope_log_div (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦ (1 + pairedEtaLogTailCutoff (N + 2)) *
      pairedEtaCurrentMidpointEnvelope rho N / (N + 1 : ℝ)) := by
  apply (((summable_pairedEtaCurrent_logPower_mul_decay_div (NontrivialZetaZero.conjugatePartner rho) 1).mul_left
      (pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) ^ 2)).add
    ((summable_pairedEtaCurrent_logPower_mul_decay_div rho 1).mul_left
      (pairedEtaCurrentMomentConstant rho ^ 2))).congr
  intro N
  unfold pairedEtaCurrentMidpointEnvelope
  simp only [pow_one]
  ring

end

end RiemannGaussian
