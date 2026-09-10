/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLogWindowLocalization
import RiemannGaussian.ZetaSievedFourierReflection

/-!
# The full sieved zero source in a smaller physical window

The complete signed source survives simultaneous logarithmic-window
restriction, the original cofinal arithmetic sieve, and the retained
Fourier region. Both discarded physical shells and all complementary
Fourier products have independently vanishing error. The original odd
reflection identity applies unchanged inside the smaller window.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian
noncomputable section

/-- The complete physical-shell and complementary-frequency allowance.
No retained arithmetic interaction is part of this explicit error. -/
def zetaLogWindowFourierError (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℝ :=
  zetaLogWindowError p N + 2 * zetaMoebiusLogMajorantMass (9 / 8) *
    zetaQuarterGapError p N y (48 / 49) (14 / 15)

/-- The combined allowance tends to zero before source normalization. -/
theorem tendsto_zetaLogWindowFourierError (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaLogWindowFourierError p N y) atTop (𝓝 0) := by
  unfold zetaLogWindowFourierError
  have h := (tendsto_zetaLogWindowError p).add
    ((tendsto_zetaQuarterGapError p y (by norm_num : (0 : ℝ) ≤ 48 / 49)
      (by norm_num : (0 : ℝ) < 14 / 15) (by norm_num)).const_mul
        (2 * zetaMoebiusLogMajorantMass (9 / 8)))
  simpa only [mul_zero, add_zero] using h

/-- Every dominated complex family is recovered from the original
centered Fourier interaction of its smaller physical window. The bound
controls the whole complementary interaction, including cross terms. -/
theorem norm_zetaArithmeticFilter_sub_window_fourier_le (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ)
    (N : ℕ) (y : ℝ) (hN : 2 ≤ N) :
    ‖zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))‖ ≤
      zetaLogWindowFourierError p N y := by
  have he : zetaArithmeticFilter a p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) =
      (zetaArithmeticFilter a p N (3 / 2 + I * y) -
        zetaArithmeticFilter (zetaLogWindowCoefficient a N) p N (3 / 2 + I * y)) +
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient a N) p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))ᶜ := by
    rw [zetaArithmeticFilter_window_eq_band a p N y (by omega),
      zetaArithmeticBand_eq_centered_parts _ _ _ _
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_zetaArithmeticFilter_sub_window_le a ha p N y)
    (norm_zetaArithmeticCenteredPart_narrow_compl_le _
      (norm_zetaLogWindowCoefficient_le a ha N) p N y hN))

/-- The complete window-and-frequency discrepancy vanishes for every
moving dominated family, uniformly over its changing arithmetic support. -/
theorem tendsto_zetaArithmeticFilter_sub_window_fourier (a : ℕ → ℕ → ℂ)
    (ha : ∀ N n, ‖a N n‖ ≤ zetaMoebiusLogMajorant n) (p : Polynomial ℂ) (y : ℝ) :
    Tendsto (fun N ↦ zetaArithmeticFilter (a N) p N (3 / 2 + I * y) -
      zetaArithmeticCenteredPart (zetaLogWindowCoefficient (a N) N) p N y
        (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))) atTop (𝓝 0) :=
  squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun N hN ↦
    norm_zetaArithmeticFilter_sub_window_fourier_le (a N) (ha N) p N y hN⟩)
    (tendsto_zetaLogWindowFourierError p y)

/-- The actual unchanged sieved coefficients restricted to the proved
window. The original geometric divisor schedule is kept explicitly. -/
def zetaRightHalfWindowCoefficient (rho : NontrivialZetaZero) (N : ℕ) : ℕ → ℂ :=
  zetaLogWindowCoefficient
    (zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfMoebiusSieve rho N)) N

/-- The actual smaller-window coefficients retain their real signs. -/
theorem zetaRightHalfWindowCoefficient_im (rho : NontrivialZetaZero) (N n : ℕ) :
    (zetaRightHalfWindowCoefficient rho N n).im = 0 :=
  zetaLogWindowCoefficient_im _ (zetaMoebiusSievedPrimeCoefficient_im _ _) N n

private theorem log_ten_sevenths_lt : Real.log (10 / 7 : ℝ) < 2 / 5 := by
  have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 7)
  have he : Real.log (10 / 7 : ℝ) = Real.log (5 / 4 : ℝ) + Real.log (8 / 7 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) (by norm_num : (8 / 7 : ℝ) ≠ 0)]
    norm_num
  rw [he]
  norm_num at h1 h2
  linarith

/-- Every retained product lies strictly beyond the square of the
actual moving divisor cutoff. Thus the smaller window also crosses the
entire region in which both factor indices could be below the cutoff. -/
theorem zetaLogWindow_gt_moebiusCutoff_sq (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ zetaLogWindow N) :
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 2 < n := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  have hu : (1 / 2 : ℝ) < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hslo : (7 / 10 : ℝ) ≤ Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have hq0 : 0 ≤ q := by dsimp [q, zetaMoebiusHeadGrowth]; positivity
  have hq : q ^ 2 ≤ (10 / 7 : ℝ) := by
    dsimp [q, zetaMoebiusHeadGrowth]
    rw [inv_pow, Real.sq_sqrt (Real.sqrt_nonneg u), inv_eq_one_div]
    apply (div_le_iff₀ hs).mpr
    nlinarith
  have hD : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N :=
    Nat.floor_le (pow_nonneg hq0 N)
  have hD2 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _) hD 2
  have hp := pow_le_pow_left₀ (sq_nonneg q) hq N
  have heq : (q ^ N) ^ 2 = (q ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [heq] at hD2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrate : (10 / 7 : ℝ) ^ N < Real.exp ((2 / 5 : ℝ) * N) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 10 / 7), ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_right log_ten_sevenths_lt hNr]
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    have h := hn.1
    norm_num at h
    nlinarith
  have hlast := Real.exp_le_exp.mpr hn.1
  rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn0 : (0 : ℝ) < n)] at hlast
  have hf : (zetaMoebiusGeometricCutoff q N : ℝ) ^ 2 < n :=
    (hD2.trans hp).trans_lt (hrate.trans_le hlast)
  exact_mod_cast hf

/-- Every factorization in the retained window has at least one
index above the original divisor cutoff. The whole low-low corner is
excluded, without assuming cancellation or bounding factors separately. -/
theorem zetaLogWindow_factor_gt_moebiusCutoff (rho : NontrivialZetaZero)
    {N a b : ℕ} (hN : 1 ≤ N) (hab : a * b ∈ zetaLogWindow N) :
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N < a ∨
      zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N < b := by
  have h := zetaLogWindow_gt_moebiusCutoff_sq rho hN hab
  by_contra! hn
  have hm := Nat.mul_le_mul hn.1 hn.2
  nlinarith

/-- In the complementary finite-head representation, every cofactor
is strictly above the cutoff. The divisor and cofactor ranges are separated
for every retained product, before any estimate on the signed sum. -/
theorem zetaLogWindow_quotient_gt_moebiusCutoff (rho : NontrivialZetaZero)
    {N n d : ℕ} (hN : 1 ≤ N) (hn : n ∈ zetaLogWindow N) (hd : d ∣ n)
    (hdD : d ≤ zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) :
    zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N < n / d := by
  have hp : d * (n / d) ∈ zetaLogWindow N := by rwa [Nat.mul_div_cancel' hd]
  exact (zetaLogWindow_factor_gt_moebiusCutoff rho hN hp).resolve_left (not_lt.mpr hdD)

/-- On the actual surviving support, the signed coefficient is exactly
the negative finite Möbius head with only large cofactors. This uses complete
divisor cancellation on distinct-prime integers; no sign or phase is bounded. -/
theorem zetaRightHalfWindowCoefficient_eq_neg_prefix (rho : NontrivialZetaZero)
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ zetaLogWindow N)
    (hmix : n.primeFactors.Nontrivial)
    (hsieve : ¬∃ P ∈ zetaRightHalfMoebiusSieve rho N, P ∣ n) :
    zetaRightHalfWindowCoefficient rho N n =
      -(∑ d ∈ Finset.Icc 1
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N),
        if d ∣ n ∧
          zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N < n / d
        then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) := by
  have hn2 : 2 ≤ n := by
    by_contra h
    have he : n = 0 ∨ n = 1 := by omega
    rcases he with rfl | rfl <;> simp at hmix
  have hprime := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn2).mpr hmix
  simp only [zetaRightHalfWindowCoefficient, zetaLogWindowCoefficient, if_pos hn,
    zetaMoebiusSievedPrimeCoefficient, if_pos hsieve,
    zetaMoebiusDistinctPrimeCoefficient, if_pos hmix]
  rw [zetaMoebiusLogTailCoefficient_eq_neg_prefix _ (by omega) hprime]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdvd : d ∣ n
  · rw [if_pos hdvd, if_pos
      ⟨hdvd, zetaLogWindow_quotient_gt_moebiusCutoff rho hN hn hdvd (Finset.mem_Icc.mp hd).2⟩]
  · simp [hdvd]

/-- The selected-zero carrier restricted in physical index and in
frequency, with every original centered phase product still present. -/
def zetaRightHalfWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  zetaArithmeticCenteredPart (zetaRightHalfWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- The actual finite physical expansion retains only the narrower
logarithmic window and the original separated-prime sieve support. No
coefficient, pole-jet phase, or centered Fourier weight is replaced. -/
theorem zetaRightHalfWindowFourierCarrier_eq_physical (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    zetaRightHalfWindowFourierCarrier rho hrho N =
      ∑ n ∈ (zetaPrimeLogBand N).filter (fun n ↦ n ∈ zetaLogWindow N ∧
        n.primeFactors.Nontrivial ∧ ¬∃ P ∈ zetaRightHalfMoebiusSieve rho N, P ∣ n),
        zetaMoebiusLogTailCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n *
          zetaMoebiusCenteredPhysicalWeight (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
            (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N)) n := by
  rw [zetaRightHalfWindowFourierCarrier, zetaArithmeticCenteredPart_eq_physical, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hw : n ∈ zetaLogWindow N <;> by_cases hp : n.primeFactors.Nontrivial <;>
    by_cases hs : ∃ P ∈ zetaRightHalfMoebiusSieve rho N, P ∣ n <;>
      simp [zetaRightHalfWindowCoefficient, zetaLogWindowCoefficient,
        zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hw, hp, hs]

/-- Every hypothetical right-half zero retains its full negative
analytic multiplicity in the smaller physical window. All removed
arithmetic shells and complementary Fourier products have vanishing error. -/
theorem tendsto_zetaRightHalfWindowFourierCarrier (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaRightHalfWindowFourierCarrier rho hrho N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hu).comp (tendsto_add_atTop_nat 1)
  have he := tendsto_zetaArithmeticFilter_sub_window_fourier
    (fun N ↦ zetaMoebiusSievedPrimeCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfMoebiusSieve rho N))
    (fun N ↦ norm_zetaMoebiusSievedPrimeCoefficient_le _ _)
    (zetaRightHalfPoleJetFilter rho hrho) rho.1.im
  have h := (tendsto_zetaRightHalfSievedPrimeTail rho hrho).sub (hp.mul he)
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext N
  dsimp [zetaRightHalfWindowFourierCarrier, zetaRightHalfWindowCoefficient,
    zetaMoebiusSievedPrimeFilter, zetaArithmeticFilter, Function.comp_def]
  ring

/-- The original pole-jet response and smaller-window carrier have
one finite error bound: the proved sieve allowance and the two explicitly
controlled physical and Fourier errors. -/
theorem exists_zetaRightHalfWindowFourier_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaRightHalfWindowFourierCarrier rho hrho N)‖ ≤
        C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfSievedPrimeTail_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let p := zetaRightHalfPoleJetFilter rho hrho
  let a := zetaMoebiusSievedPrimeCoefficient
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfMoebiusSieve rho N)
  let u : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1)
  have hu : ‖u‖ ≤ 1 := by
    have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
    dsimp [u]
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact pow_le_one₀ hu0 (by linarith)
  have he : u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
      zetaRightHalfWindowFourierCarrier rho hrho N) =
      u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
        zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im)) +
      u * (zetaArithmeticFilter a p N (3 / 2 + I * rho.1.im) -
        zetaRightHalfWindowFourierCarrier rho hrho N) := by ring
  change ‖u * (zetaPrimeLogFilter p N (3 / 2 + I * rho.1.im) -
    zetaRightHalfWindowFourierCarrier rho hrho N)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add (hb N)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
  simpa only [one_mul, zetaRightHalfWindowFourierCarrier, zetaRightHalfWindowCoefficient, p, a]
    using norm_zetaArithmeticFilter_sub_window_fourier_le a
    (norm_zetaMoebiusSievedPrimeCoefficient_le _ _) p N rho.1.im hN

/-- Every complete allowance displayed in the selected-zero bound
tends to zero. This includes the original sieve error as well as both
physical shells and the complementary Fourier interaction. -/
theorem tendsto_zetaRightHalfWindowTotalError (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (C : ℝ) :
    Tendsto (fun N ↦ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
      zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im)
      atTop (𝓝 0) := by
  have hu0 : 0 ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs : Real.sqrt (3 / 2 - rho.1.re) < 1 := by
    nlinarith [Real.sq_sqrt hu0, Real.sqrt_nonneg (3 / 2 - rho.1.re)]
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg _) hs).const_mul C
  simpa only [mul_zero, zero_add] using
    hp.add (tendsto_zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) rho.1.im)

/-- The actual odd real reflection work on the smaller physical
window, with the original cyclic reflection and every mixed phase intact. -/
def zetaRightHalfWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℝ :=
  zetaArithmeticReflectionWork (zetaRightHalfWindowCoefficient rho N)
    (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
    (zetaMoebiusResonantModes N (zetaDominatedResonanceThreshold N))

/-- Exact physical parity cancellation commutes with the window and
the sieve. The smaller-window work has the same original normalization. -/
theorem zetaRightHalfWindowFourierCarrier_re_eq_reflection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    (zetaRightHalfWindowFourierCarrier rho hrho N).re =
      -2 * zetaRightHalfWindowReflectionWork rho hrho N :=
  zetaArithmeticCenteredPart_re_eq_reflection _ (zetaRightHalfWindowCoefficient_im rho N)
    _ _ _ _ (zetaMoebiusResonantModes_neg_closed N _)

/-- The full positive multiplicity source survives in the smaller
signed reflection correlation. Its independent strict upper bound is
the remaining obligation; no additional zero is excluded by localization. -/
theorem tendsto_zetaRightHalfWindowReflectionWork (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ (3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
      zetaRightHalfWindowReflectionWork rho hrho N)
      atTop (𝓝 ((analyticZetaZeroMultiplicity rho : ℝ) / 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfWindowFourierCarrier rho hrho)
  simp only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.neg_re, Complex.natCast_re, zetaRightHalfWindowFourierCarrier_re_eq_reflection] at h
  have ht := h.mul_const (-(1 / 2 : ℝ))
  convert ht using 1
  · funext N
    ring
  · congr 1
    ring

/-- The same actual signed scalar has a finite comparison with the
original pole-jet response. Its entire allowance vanishes; localization
requires no pointwise sign or bound on the retained correlation. -/
theorem exists_zetaRightHalfWindowReflection_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      |-(3 / 2 - rho.1.re : ℝ) ^ (N + 1) *
          (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + I * rho.1.im)).re / 2 -
        (3 / 2 - rho.1.re : ℝ) ^ (N + 1) * zetaRightHalfWindowReflectionWork rho hrho N| ≤
        (C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N +
          zetaLogWindowFourierError (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im) / 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfWindowFourier_error_bound rho hrho
  refine ⟨C, hC, fun N hN ↦ ?_⟩
  let L := zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im)
  let u : ℝ := (3 / 2 - rho.1.re) ^ (N + 1)
  let z : ℂ := ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    (L - zetaRightHalfWindowFourierCarrier rho hrho N)
  have hz : z.re = u * (L.re + 2 * zetaRightHalfWindowReflectionWork rho hrho N) := by
    dsimp [z, u]
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
      zetaRightHalfWindowFourierCarrier_re_eq_reflection]
    ring
  change |-u * L.re / 2 - u * zetaRightHalfWindowReflectionWork rho hrho N| ≤ _
  have he : -u * L.re / 2 - u * zetaRightHalfWindowReflectionWork rho hrho N = -z.re / 2 := by
    rw [hz]
    ring
  rw [he, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right ((Complex.abs_re_le_norm z).trans (hb N hN)) (by norm_num)

end
end RiemannGaussian
