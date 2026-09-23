/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCubicBudget

/-!
# A summable reserve in the actual cubic profile

The numerical coefficient forty leaves a strictly positive cubic reserve.
The expanded small-block window and the finite lower-degree range also
pay that reserve. These inequalities retain scale decay for summation,
instead of replacing every original block by the profile maximum.
-/

namespace RiemannGaussian.VinogradovCubicDecay
noncomputable section
open VinogradovCubicBudget
open VinogradovSharperBudget (delta line delta_pos delta_le)

/-- The coefficient forty pays the cubic maximum while retaining an
explicit scale-dependent decay term. -/
theorem cubic_reserve {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) :
    d * v - v ^ 3 / 10368 ≤ 40 * d * Real.sqrt d - v ^ 3 / 2097152 := by
  let a := Real.sqrt (110592 * d / 31)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 110592 * d / 31 := Real.sq_sqrt (by positivity)
  have hs := Real.sqrt_nonneg d
  have hs2 := Real.sq_sqrt hd
  have ha60 : a ≤ 60 * Real.sqrt d := by nlinarith
  have hf := mul_nonneg (sq_nonneg (v - a)) (show 0 ≤ v + 2 * a by positivity)
  have he : (v - a) ^ 2 * (v + 2 * a) = v ^ 3 - 3 * a ^ 2 * v + 2 * a ^ 2 * a := by ring
  rw [he, ha2] at hf
  have hm := mul_le_mul_of_nonneg_left ha60 hd
  have hv3 : 0 ≤ v ^ 3 := pow_nonneg hv _
  nlinarith

/-- The entire small-block interval fits the same decaying profile;
its endpoint is strictly below the retained cubic maximum. -/
theorem small_reserve {n : ℕ} (hn : 48 ≤ n) {v : ℝ}
    (hv : 0 ≤ v) (hvn : v ≤ 2 / (8 * (n : ℝ))) :
    delta n * v ≤ growth n - v ^ 3 / 2097152 := by
  have hnr : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hK : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hvn (delta_pos n).le
  have hp := pow_le_pow_left₀ hv hvn 3
  have he : delta n * (2 / (8 * (n : ℝ))) +
      (2 / (8 * (n : ℝ))) ^ 3 / 2097152 ≤ growth n := by
    rw [growth_eq, delta]
    field_simp
    nlinarith [sq_nonneg ((n : ℝ) - 48), pow_nonneg (show 0 ≤ (n : ℝ) - 48 by linarith) 3]
  linarith

/-- The finite lower-degree range has a fixed spare power after paying
the full target displacement. -/
theorem low_degree_reserve {n k : ℕ} (hn : 48 ≤ n) (hk : 12 ≤ k) (hk' : k < 48) :
    delta n - VinogradovShortResonance.saving k / 4 ≤ -(1 / 33554432 : ℝ) := by
  have hnr : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkr' : (k : ℝ) ≤ 48 := by exact_mod_cast (show k ≤ 48 by omega)
  have hd : delta n ≤ 1 / (4096 * 97 ^ 2 : ℝ) := by
    unfold delta
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hs : (1 / (6400 * 48 ^ 2 : ℝ)) ≤ VinogradovShortResonance.saving k / 4 := by
    rw [VinogradovShortResonance.saving, if_neg (by omega : ¬48 ≤ k), div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg ((k : ℝ) - 48)]
  norm_num at hd hs ⊢
  linarith

/-- The uniform growth envelope retains its actual logarithmic-scale
cubic decay instead of charging every block at the maximum. -/
def envelope (n : ℕ) (t X : ℝ) : ℝ :=
  Real.exp ((growth n - (Real.log X / Real.log t) ^ 3 / 2097152) * Real.log t)

/-- The envelope separates into its height growth and a cubic tail in
the original physical logarithm. -/
theorem envelope_eq (n : ℕ) {t : ℝ} (ht : 1 < t) (X : ℝ) :
    envelope n t X = t ^ growth n *
      Real.exp (-(Real.log X) ^ 3 / (2097152 * (Real.log t) ^ 2)) := by
  rw [envelope, Real.rpow_def_of_pos (by linarith : 0 < t), ← Real.exp_add]
  congr 1
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  field_simp
  ring

/-- A physical scale below a height power retains that power as a bound
for its logarithmic ratio. -/
theorem log_ratio_le {t X a : ℝ} (ht : 1 < t) (hX : 0 < X)
    (h : X ≤ t ^ a) : Real.log X / Real.log t ≤ a := by
  apply (div_le_iff₀ (Real.log_pos ht)).mpr
  have hlog := Real.log_le_log hX h
  rw [Real.log_rpow (by linarith : 0 < t)] at hlog
  exact hlog

/-- An exponent estimate on the retained ratio transports directly to
the actual power, with no loss of logarithmic scale. -/
theorem power_le_envelope (n : ℕ) {t X a : ℝ} (ht : 1 < t) (hX : 0 < X)
    (h : a * (Real.log X / Real.log t) ≤
      growth n - (Real.log X / Real.log t) ^ 3 / 2097152) :
    X ^ a ≤ envelope n t X := by
  rw [Real.rpow_def_of_pos hX]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right h (Real.log_pos ht).le
  have he : (Real.log X / Real.log t) * Real.log t = Real.log X :=
    div_mul_cancel₀ _ (Real.log_pos ht).ne'
  have hm' : a * Real.log X ≤
      (growth n - (Real.log X / Real.log t) ^ 3 / 2097152) * Real.log t := by
    simpa only [mul_assoc, he] using hm
  simpa only [mul_comm] using hm'

/-- A negative physical power pays the retained decay whenever its
reserve dominates the square of the logarithmic ratio. -/
theorem negative_power_le (n : ℕ) {t X a c : ℝ} (ht : 1 < t) (hX : 1 ≤ X)
    (ha : a ≤ -c) (hc : (Real.log X / Real.log t) ^ 2 ≤ 2097152 * c) :
    X ^ a ≤ envelope n t X := by
  have hv : 0 ≤ Real.log X / Real.log t :=
    div_nonneg (Real.log_nonneg hX) (Real.log_pos ht).le
  apply power_le_envelope n ht (by linarith)
  have hm := mul_le_mul_of_nonneg_right ha hv
  have hm' := mul_le_mul_of_nonneg_right hc hv
  nlinarith [growth_pos n]

/-- The original derivative profile factors exactly under a displacement
of its real part. This preserves both complementary derivative terms. -/
theorem profile_shift (q : ℕ) (σ t e : ℝ) {X : ℝ} (hX : 0 < X) :
    DirichletBlockPowerProfile.profile q σ t X =
      X ^ (-e) * DirichletBlockPowerProfile.profile q (σ - e) t X := by
  unfold DirichletBlockPowerProfile.profile
  rw [mul_add]
  congr 1 <;>
    rw [mul_left_comm, ← Real.rpow_add hX] <;>
    congr 2 <;> ring

/-- Every block through the actual cutoff retains cubic decay, including
the small scales, both moment regimes and both long derivative profiles. -/
theorem block_bound (n j : ℕ) (hn : 48 ≤ n) {s : ℂ} (hline : line n ≤ s.re)
    (ht : (VinogradovScaleSelection.heightThreshold (8 * n) : ℝ) ≤ s.im)
    (hX : ((2 ^ j : ℕ) : ℝ) ≤ 4 * s.im) :
    ‖DirichletDyadicBlocks.block s j‖ ≤
      512 * envelope n s.im ((2 ^ j : ℕ) : ℝ) := by
  have hbT : (VinogradovScaleSelection.rootBase (8 * n) : ℝ) ≤
      VinogradovScaleSelection.heightThreshold (8 * n) := by
    exact_mod_cast VinogradovScaleSelection.rootBase_le_heightThreshold (show 1 ≤ 8 * n by omega)
  have hb : (16 : ℝ) ≤ VinogradovScaleSelection.rootBase (8 * n) := by
    exact_mod_cast VinogradovScaleSelection.rootBase_ge_sixteen (8 * n)
  have ht1 : 1 < s.im := by linarith
  have htpos : 0 < s.im := by linarith
  have hXone : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))
  have hXpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hσ : 0 ≤ s.re := by linarith [(VinogradovSharperBudget.line_bounds n).1]
  have hdamp : 1 - s.re ≤ delta n := by dsimp only [line] at hline; linarith
  let v := Real.log ((2 ^ j : ℕ) : ℝ) / Real.log s.im
  have hv : 0 ≤ v := div_nonneg (Real.log_nonneg hXone) (Real.log_pos ht1).le
  have hv2 : v ≤ 2 := by
    apply log_ratio_le ht1 hXpos
    rw [Real.rpow_two]
    nlinarith
  have henv : 0 ≤ envelope n s.im ((2 ^ j : ℕ) : ℝ) := (Real.exp_pos _).le
  by_cases hx : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / (8 * (n : ℝ)))
  · have h := ZetaDyadicPowerBound.trivial_block_bound hσ j
    have he : ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ (-s.re) =
        ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re) := by
      rw [sub_eq_add_neg, Real.rpow_add hXpos, Real.rpow_one]
    rw [he] at h
    have hr := small_reserve hn hv (log_ratio_le ht1 hXpos hx)
    have hm := mul_le_mul_of_nonneg_right hdamp hv
    have hp := power_le_envelope n ht1 hXpos (a := 1 - s.re) (by linarith)
    exact (h.trans hp).trans (by nlinarith)
  · by_cases hx' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (2 / 11 : ℝ)
    · have hlo' : s.im ^ (2 / ((8 * n : ℕ) : ℝ)) ≤ ((2 ^ j : ℕ) : ℝ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using (lt_of_not_ge hx).le
      obtain ⟨k, M, hk, _, hkr, hMX, hXM, hkt, htk⟩ :=
        VinogradovScaleSelection.exists_window_parameters (8 * n) (2 ^ j) (by omega) ht hlo' hx'
      have hblock := VinogradovShortDyadic.dyadic_block_bound k M j hk (by nlinarith) hMX hXM s hσ hkt htk
      have htail := negative_power_le n ht1 hXone (c := 1 / 4) (a := 1 / 2 - s.re)
        (by linarith [delta_le n]) (by nlinarith [sq_nonneg (v - 2)])
      have hlead : ((2 ^ j : ℕ) : ℝ) ^
          (1 - s.re - VinogradovShortResonance.saving k / 4) ≤
          envelope n s.im ((2 ^ j : ℕ) : ℝ) := by
        by_cases hk48 : 48 ≤ k
        · have hM : 16 ≤ M := by nlinarith
          have hp := VinogradovCubicSaving.power_le_cubic_profile hk48 hM hXM
            (show 1 ≤ 2 ^ j from one_le_pow₀ (by norm_num)) ht1 hkt hdamp
          apply hp.trans
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (cubic_reserve (delta_pos n).le hv)
            (Real.log_pos ht1).le
        · apply negative_power_le n ht1 hXone (c := 1 / 33554432)
          · linarith [low_degree_reserve hn hk (by omega)]
          · have hv' : v ≤ 2 / 11 := log_ratio_le ht1 hXpos hx'
            nlinarith [sq_nonneg (v - 2 / 11)]
      nlinarith
    · have hdn : delta n ≤ 1 / 8192 := by
        have hnr : (48 : ℝ) ≤ n := by exact_mod_cast hn
        unfold delta
        apply (div_le_iff₀ (by positivity : 0 < 4096 * (2 * (n : ℝ) + 1) ^ 2)).mpr
        nlinarith
      have hdp : 0 ≤ delta n + 1 / 8192 := by linarith [delta_pos n]
      have hdp' : delta n + 1 / 8192 ≤ 1 / 4096 := by linarith
      have hp := negative_power_le n ht1 hXone (a := -(1 / 8192)) (c := 1 / 8192)
        le_rfl (by nlinarith [sq_nonneg (v - 2)])
      have shifted (q : ℕ) : DirichletBlockPowerProfile.profile q s.re s.im ((2 ^ j : ℕ) : ℝ) ≤
          ((2 ^ j : ℕ) : ℝ) ^ (-(1 / 8192 : ℝ)) *
            DirichletBlockPowerProfile.profile q (1 - (delta n + 1 / 8192)) s.im
              ((2 ^ j : ℕ) : ℝ) := by
        apply (VinogradovLongBlocks.profile_antitone_sigma q htpos.le hXone hline).trans_eq
        rw [profile_shift q (line n) s.im (1 / 8192) hXpos]
        congr 2
        unfold line
        ring
      by_cases hx'' : ((2 ^ j : ℕ) : ℝ) ≤ s.im ^ (1 / 3 : ℝ)
      · have hb := DirichletBlockPowerProfile.bound 4 j hσ htpos
        have hl := VinogradovLongBlocks.sixth_profile_le hdp hdp' ht1.le
          (lt_of_not_ge hx').le hx''
        have hm := mul_le_mul_of_nonneg_left hl
          (Real.rpow_nonneg hXpos.le (-(1 / 8192 : ℝ)))
        nlinarith [shifted 4]
      · have hb := DirichletBlockPowerProfile.bound 2 j hσ htpos
        have hl := VinogradovLongBlocks.fourth_profile_le hdp hdp' ht1.le
          (lt_of_not_ge hx'').le hX
        have hm := mul_le_mul_of_nonneg_left hl
          (Real.rpow_nonneg hXpos.le (-(1 / 8192 : ℝ)))
        nlinarith [shifted 2]

end
end RiemannGaussian.VinogradovCubicDecay
