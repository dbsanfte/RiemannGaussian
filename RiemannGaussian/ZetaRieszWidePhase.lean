/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWideOwnerAudit

/-!
# Signed prime phases on the concrete wide-owner band

The derivative successor is checked with a small auxiliary ceiling; the
actual allocation remains exactly 13N/40 < k <= 27N/40. Completion errors
are paid independently before the hypothetical-zero phase is used.
-/

namespace RiemannGaussian.ZetaRieszWideOwnerAudit
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCompletion ZetaRieszPrimeCompletionRate ZetaRieszCompletionProduct
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaRieszMatchedMiddle ZetaRieszWingReserve

private theorem successor_rate {u : ℝ} (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    completionExponent u (169 / 250) (11 / 8) (27 / 55) (1 + 1 / 262144) ≤
      -(1 / 50000) := by
  have hl : Real.log (radiusCeiling / (27 / 55)) ≤ (184492 / 10000000 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num [radiusCeiling])).mpr
    have h := Real.sum_le_exp_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 184492 / 10000000) 4
    norm_num [Finset.sum_range_succ, radiusCeiling] at h ⊢
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < u / (27 / 55 : ℝ))
    (div_le_div_of_nonneg_right huU (by norm_num : (0 : ℝ) ≤ 27 / 55))
  unfold completionExponent
  linarith

/-- Independent completion, including the polynomial prefix, on the
entire widened band and its derivative successor. -/
theorem eventually_wide_weighted_error {u : ℝ} (hu : 1 / 2 ≤ u) (huU : u ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 4 * k → 250 * k ≤ 169 * N → ∀ y : ℝ,
      ‖(k : ℂ) * ((u : ℂ) ^ k * (finiteMoment (intermediatePrimes u N) k
        (3 / 2 + Complex.I * y) - ordinaryPrimeMoment k (3 / 2 + Complex.I * y)))‖ ≤
        (N + 1 : ℝ) ^ 3 * Real.exp (-(N : ℝ) / 50000) *
          ((∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
            ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) := by
  have hu0 : 0 < u := by linarith
  have hue := huU.trans_lt radius_lt_source
  have hu1 : u < 1 := hue.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlu : Real.log u ≤ -(11 / 16 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu0 hue).le
  filter_upwards [eventually_norm_physicalPrimeTail_of_rate hu0
    (show (0 : ℝ) ≤ 11 / 8 by norm_num) (by norm_num; exact hue)
    (show (0 : ℝ) < 27 / 55 by norm_num) (show (27 / 55 : ℝ) ≤ u by linarith)
    (show (1 : ℝ) < 1 + 1 / 262144 by norm_num) (by norm_num) (successor_rate hu huU),
    ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu0 hu1] with N hhi hNX
  intro k hklo hkhi y
  have hkc : (k : ℝ) ≤ N + 1 := by
    have h : k ≤ N := by omega
    have hc : (k : ℝ) ≤ N := by exact_mod_cast h
    linarith
  have hpow : u ^ k ≤ Real.exp (-(N : ℝ) / 50000) := by
    rw [← Real.exp_log hu0, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) k)
    have hc : (N : ℝ) ≤ 4 * k := by exact_mod_cast hklo
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hlow : ‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ ≤
      (N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 50000) *
        ∑' n, zetaPrimeExpWeight (1025 / 1024) n := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact (mul_le_mul hpow (norm_smallPrimeMoment_le N k y) (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq (by ring)
  have hhigh := hhi k (by
    have hc : 250 * (k : ℝ) ≤ 169 * N := by exact_mod_cast hkhi
    linarith) y
  rw [show -(1 / 50000 : ℝ) * N = -(N : ℝ) / 50000 by ring] at hhigh
  have hZ0 : 0 ≤ ∑' n, zetaPrimeExpWeight (1025 / 1024) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  have hZ1 : 0 ≤ ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [ordinaryPrimeMoment_eq_actual_split u N k y hNX]
  have he (a b c : ℂ) : a - (b + a + c) = -(b + c) := by ring
  rw [he, mul_neg, mul_neg, norm_neg, norm_mul, Complex.norm_natCast, mul_add]
  calc
    _ ≤ (k : ℝ) * (‖(u : ℂ) ^ k * smallPrimeMoment N k y‖ +
        ‖(u : ℂ) ^ k * physicalPrimeTail u N k y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Nat.cast_nonneg _)
    _ ≤ (N + 1 : ℝ) * ((N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 50000) *
        (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
        Real.exp (-(N : ℝ) / 50000) * ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) := by
      exact mul_le_mul hkc (add_le_add hlow hhigh)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ ≤ _ := by
      have h1 : 1 ≤ (N + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
      nlinarith [mul_le_mul_of_nonneg_left h1
        (show 0 ≤ (N + 1 : ℝ) * Real.exp (-(N : ℝ) / 50000) *
          (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) by positivity)]

/-- Every moving order in the checked wider range retains the exact
hypothetical-zero phase. -/
theorem tendsto_wide_weighted_finite (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) (k : ℕ → ℕ)
    (hk : ∀ᶠ N : ℕ in atTop, N ≤ 4 * k N ∧ 250 * k N ≤ 169 * N) :
    Tendsto (fun N => weightedFinite (3 / 2 - rho.1.re) rho.1.im N (k N))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let u := 3 / 2 - rho.1.re
  have hu : 1 / 2 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hk, eventually_ge_atTop (4 * b)] with N hkN hNb
    omega
  let Z := (∑' n, zetaPrimeExpWeight (1025 / 1024) n) +
    ∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 3
    (Real.exp_pos (-(1 / 50000 : ℝ)))
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 50000 : ℝ) < 0))).mul_const Z
  simp only [zero_mul] at ht
  have herr : Tendsto (fun N => (k N : ℂ) * ((u : ℂ) ^ k N *
      (finiteMoment (intermediatePrimes u N) (k N) (3 / 2 + Complex.I * rho.1.im) -
        ordinaryPrimeMoment (k N) (3 / 2 + Complex.I * rho.1.im)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ =>
      (N + 1 : ℝ) ^ 3 * Real.exp (-(1 / 50000 : ℝ)) ^ N * Z) ?_ ht
    filter_upwards [eventually_wide_weighted_error hu huU, hk] with N hN hkN
    have he : Real.exp (-(1 / 50000 : ℝ)) ^ N = Real.exp (-(N : ℝ) / 50000) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact hN (k N) hkN.1 hkN.2 rho.1.im
  have h := ((ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed).comp hkt).add herr
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def, weightedFinite]
  ring

theorem eventually_uniform_wide_phase (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 4 * k → 250 * k ≤ 169 * N →
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k +
        (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if N ≤ 4 * f N ∧ 250 * f N ≤ 169 * N then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop, N ≤ 4 * k N ∧ 250 * k N ≤ 169 * N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    by_cases hf : N ≤ 4 * f N ∧ 250 * f N ≤ 169 * N
    · simpa only [k, if_pos hf] using hf
    · simp only [k, if_neg hf]
      omega
  have h := ((tendsto_wide_weighted_finite rho hrho hexposed huU k hk).add_const
    (analyticZetaZeroMultiplicity rho : ℂ)).norm
  simp only [neg_add_cancel, norm_zero] at h
  filter_upwards [h.eventually (eventually_lt_nhds hε)] with N hN
  intro hlow hhigh
  simpa only [k, if_pos (And.intro hlow hhigh)] using hN.le

private theorem complete_phase_quarter (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 4 * k →
      ‖weightedComplete (3 / 2 - rho.1.re) rho.1.im k +
        (analyticZetaZeroMultiplicity rho : ℂ)‖ ≤ ε := by
  have h := ((ZetaRieszPrimeCompletionPhase.tendsto_weighted_complete rho hrho hexposed).add_const
    (analyticZetaZeroMultiplicity rho : ℂ)).norm
  simp only [neg_add_cancel, norm_zero] at h
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h.eventually (eventually_lt_nhds hε))
  filter_upwards [eventually_ge_atTop (4 * K)] with N hN
  intro k hk
  exact (hK k (by omega)).le

private theorem wide_taper_positive {A B : ℂ} {m r : ℝ}
    (hA : ‖A - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 240)
    (hB : ‖B - (m : ℂ) ^ 2‖ ≤ m ^ 2 / 240)
    (hr : r ≤ 99 / 100) : m ^ 2 / 1000 ≤ (A - (r : ℂ) * B).re := by
  have he : ((m : ℂ) ^ 2).re = m ^ 2 := by simp [pow_two]
  have ha := (Complex.abs_re_le_norm (A - (m : ℂ) ^ 2)).trans hA
  have hb := (Complex.abs_re_le_norm (B - (m : ℂ) ^ 2)).trans hB
  rw [Complex.sub_re, he] at ha hb
  obtain ⟨ha0, _⟩ := abs_le.mp ha
  obtain ⟨hb0, hb1⟩ := abs_le.mp hb
  have hbpos : 0 ≤ B.re := by nlinarith [sq_nonneg m]
  have hprod := mul_le_mul_of_nonneg_right hr hbpos
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [sq_nonneg m]

/-- Every order of the proposed wider companion restores a strictly
positive tapered prime product under the exposed-zero hypothesis. -/
theorem eventually_re_wide_atom (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ ownerOrders N,
      (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / (250 * ((N + 1 : ℕ) : ℝ)) ≤
        ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)) *
          wingAtom (3 / 2 - rho.1.re) rho.1.im N k).re := by
  let u := 3 / 2 - rho.1.re
  let m : ℝ := analyticZetaZeroMultiplicity rho
  have hu : 1 / 2 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  have hm : 0 < m := by
    dsimp only [m]
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hue := huU.trans_lt radius_lt_source
  filter_upwards [eventually_uniform_wide_phase rho hrho hexposed huU
      (ε := m / 1000) (by positivity),
    complete_phase_quarter rho hrho hexposed (ε := m / 1000) (by positivity),
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
      (show (0 : ℝ) ≤ 11 / 16 by norm_num) hue,
    eventually_ge_atTop 2000] with N hf hc hLN hN
  intro k hk
  have hks := (Finset.mem_filter.mp hk).2
  have hk0 : 0 < k := by omega
  have hkM := ownerOrders_le hk
  have hl0 : 0 < N + 1 - k := by omega
  have hklo : N ≤ 4 * k := by omega
  let l := N + 1 - k
  let L := SquarefreeVaughanLogSource.length u N
  let w : ℝ := ((N + 1 : ℕ) : ℝ) / ((k : ℝ) * (l : ℝ))
  have hllo : N ≤ 4 * l := by dsimp [l]; omega
  have hlhi : 250 * (l + 1) ≤ 169 * N := by dsimp [l]; omega
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hLL : (11 / 8 : ℝ) * N ≤ L := by dsimp [L]; nlinarith [hLN]
  have ha := norm_product_sub_square_fine hm.le (hc k hklo) (hf l hllo (by omega))
  have hb := norm_product_sub_square_fine hm.le (hc k hklo) (hf (l + 1) (by omega) hlhi)
  have hr : (l : ℝ) / (u * L) ≤ 99 / 100 := by
    apply (div_le_iff₀ (mul_pos hu0 hL)).mpr
    have hprod := mul_le_mul_of_nonneg_right hu hL.le
    have hlc : 40 * (l : ℝ) ≤ 27 * N + 40 := by
      exact_mod_cast (show 40 * l ≤ 27 * N + 40 by dsimp [l]; omega)
    have hNc : (2000 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hsign := wide_taper_positive ha hb hr
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hprod := mul_le_mul_of_nonneg_left hsign hw
  have hsmall := mul_le_mul_of_nonneg_left (wing_weight_lower N k hk0 hkM hl0)
    (show 0 ≤ m ^ 2 / 1000 by positivity)
  have he : (u : ℂ) ^ (N + 1) * wingAtom u rho.1.im N k =
      (w : ℂ) * (weightedComplete u rho.1.im k * weightedFinite u rho.1.im N l -
        (((l : ℝ) / (u * L)) : ℂ) *
          (weightedComplete u rho.1.im k * weightedFinite u rho.1.im N (l + 1))) := by
    rw [normalized_wingAtom_eq u rho.1.im N k hu0.ne' hk0 hkM hl0]
    simp only [w, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, L, l]
  change m ^ 2 / (250 * ((N + 1 : ℕ) : ℝ)) ≤ _
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have htotal := hsmall.trans (by simpa only [mul_comm] using hprod)
  have hleft : m ^ 2 / 1000 * (4 / ((N + 1 : ℕ) : ℝ)) =
      m ^ 2 / (250 * ((N + 1 : ℕ) : ℝ)) := by ring
  rw [hleft] at htotal
  simpa only [u, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] using htotal

end
end RiemannGaussian.ZetaRieszWideOwnerAudit
