/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFourier
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Fixed cofactor arithmetic decay

A prime insertion preserves a fixed nonunit cofactor cost uniformly in the
cutoff. Below a fixed multiple of the original damped squared cutoff, the
full factorial filter has an explicit vanishing allowance. For a squarefree
composite cofactor the complete original-band contribution therefore tends
to zero at the source scale. Prime cofactors and growing cofactors are not
covered by this whole-class decay theorem.
-/

namespace RiemannGaussian.ZetaRieszFixedCofactor
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius Topology
open Filter

/-- The finite absolute logarithmic divisor mass of the fixed cofactor. -/
def divisorLogMass (a : ℕ) : ℝ :=
  ∑ d ∈ a.divisors, |((μ d : ℤ) : ℝ)| * Real.log d

/-- The cofactor cost is nonnegative. -/
theorem divisorLogMass_nonneg (a : ℕ) : 0 ≤ divisorLogMass a :=
  Finset.sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg d)

/-- Subtracting the complete signed mass bounds every cutoff of a fixed
nonunit cofactor by its finite logarithmic divisor mass. -/
theorem abs_riesz_le_divisorLogMass (L : ℝ) {a : ℕ} (ha : a ≠ 1) :
    |VaughanLogAverage.riesz L a| ≤ divisorLogMass a := by
  have hm : (∑ d ∈ a.divisors, ((μ d : ℤ) : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero ha
  have he : VaughanLogAverage.riesz L a =
      ∑ d ∈ a.divisors, ((μ d : ℤ) : ℝ) *
        (max 0 (L - Real.log d) - max 0 L) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, zero_mul,
      sub_zero, VaughanLogAverage.riesz]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  have ht : |max 0 (L - Real.log d) - max 0 L| ≤ Real.log d := by
    rw [max_comm 0 (L - Real.log d), max_comm 0 L]
    simpa only [sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (Real.log_natCast_nonneg d)] using
      abs_max_sub_max_le_abs (L - Real.log d) L 0
  exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)

/-- The large prime acts as an exact difference of two uniformly bounded
cofactor profiles; neither its logarithm nor the cutoff enters the cost. -/
theorem abs_riesz_prime_mul_le_fixed (L : ℝ) {a p : ℕ} (ha : a ≠ 1)
    (hp : p.Prime) (hpa : ¬ p ∣ a) :
    |VaughanLogAverage.riesz L (p * a)| ≤ 2 * divisorLogMass a := by
  rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa]
  exact (abs_sub _ _).trans ((add_le_add (abs_riesz_le_divisorLogMass L ha)
    (abs_riesz_le_divisorLogMass (L - Real.log p) ha)).trans_eq (by ring))

/-- Below a fixed logarithmic enlargement, the actual composite coefficient
has a uniform bound with the common cutoff explicitly retained. -/
theorem norm_coefficient_prime_mul_le {L H c : ℝ} (hL : 0 < L) (hH : 0 < H)
    (hHL : H ≤ L) {a p : ℕ} (ha : a ≠ 1) (hp : p.Prime) (hpa : ¬ p ∣ a)
    (hc : 0 ≤ c) (hclip : Real.log (p * a : ℕ) ≤ L + c) :
    ‖SquarefreeVaughanLogSource.coefficient L (p * a)‖ ≤
      2 * divisorLogMass a * (1 + c / H) := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
      abs_of_nonneg (Real.log_natCast_nonneg _), abs_of_pos hL]
    have hquot : Real.log (p * a : ℕ) / L ≤ 1 + c / H := by
      calc
        _ ≤ (L + c) / L := div_le_div_of_nonneg_right hclip hL.le
        _ = 1 + c / L := by field_simp
        _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left hc hH hHL)
    calc
      _ = |VaughanLogAverage.riesz L (p * a)| * (Real.log (p * a : ℕ) / L) := by ring
      _ ≤ (2 * divisorLogMass a) * (1 + c / H) :=
        mul_le_mul (abs_riesz_prime_mul_le_fixed L ha hp hpa) hquot
          (div_nonneg (Real.log_natCast_nonneg _) hL.le)
          (mul_nonneg (by norm_num) (divisorLogMass_nonneg a))
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (divisorLogMass_nonneg a))
      (by positivity)

/-- Unit exponential tilt keeps every factorial shift of the full filter
and bounds it by an inverse square root, uniformly in the height and order. -/
theorem norm_filter_le_inv_sqrt (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (1 / Real.sqrt n) * ∑ k ∈ P.support, ‖P.coeff k‖ := by
  have hb := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y)
    (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by norm_num : (0 : ℝ) < 1)
  have he : Real.exp (-((1 : ℝ) / 2) * Real.log n) ≤ 1 / Real.sqrt n := by
    simpa only [norm_zetaPrimeFeature, Complex.ofReal_re, zetaPrimeExpWeight] using
      norm_zetaPrimeFeature_le_inv_sqrt (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num) hn
  norm_num at hb
  rw [neg_mul] at he
  exact hb.trans (mul_le_mul_of_nonneg_right he
    (Finset.sum_nonneg fun _ _ => norm_nonneg _))

/-- Any uniformly bounded coefficient on any subset of a finite initial
interval has a square-root filtered mass bound. The chosen support is unchanged. -/
theorem norm_sum_filter_le_sqrt (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (T : Finset ℕ) (X : ℕ) (f : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ n ∈ T, 0 < n ∧ n ≤ X) (hf : ∀ n ∈ T, ‖f n‖ ≤ C) :
    ‖∑ n ∈ T, f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      2 * C * (∑ k ∈ P.support, ‖P.coeff k‖) * Real.sqrt X := by
  let S := ∑ k ∈ P.support, ‖P.coeff k‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ ≤ ∑ n ∈ T, ‖f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ T, C * ((1 / Real.sqrt n) * S) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hf n hn) (norm_filter_le_inv_sqrt P N y (hT n hn).1)
        (norm_nonneg _) hC
    _ = C * S * ∑ n ∈ T, 1 / Real.sqrt n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ C * S * ∑ n ∈ Finset.Icc 1 X, 1 / Real.sqrt n := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hS)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Finset.mem_Icc.mpr (hT n hn)) (fun _ _ _ => by positivity)
    _ ≤ C * S * (2 * Real.sqrt X) :=
      mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le X) (mul_nonneg hC hS)
    _ = _ := by ring

/-- The damped square-root ceiling has an explicit vanishing allowance. -/
theorem normalized_shifted_cutoff_le {u : ℝ} (hu : 0 < u) (N : ℕ) :
    u ^ (N + 1) * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ≤
      u / (N + 1) + 2 * u ^ (N + 1) := by
  have hb := ZetaVaughanCutoffBudget.normalized_budget_dampedCutoff_le hu
    (by positivity : 0 < (N : ℝ) + 1) N
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N) le_rfl le_rfl
  rw [ZetaVaughanCutoffBudget.budget, Real.mul_self_sqrt (by positivity)] at hb
  linarith

/-- The full filtered mass below a fixed multiple of the moving squared
cutoff has an explicit inverse-order plus geometric allowance. -/
theorem norm_sum_filter_square_cutoff_le (P : Polynomial ℂ) (N K : ℕ) (y : ℝ)
    (T : Finset ℕ) (f : ℕ → ℂ) {C u : ℝ} (hC : 0 ≤ C) (hu : 0 < u)
    (hT : ∀ n ∈ T, 0 < n ∧
      n ≤ K * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hf : ∀ n ∈ T, ‖f n‖ ≤ C) :
    ‖(u : ℂ) ^ (N + 1) *
      ∑ n ∈ T, f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
        (2 * C * (∑ k ∈ P.support, ‖P.coeff k‖) * Real.sqrt K) *
          (u / (N + 1) + 2 * u ^ (N + 1)) := by
  have hb := norm_sum_filter_le_sqrt P N y T
    (K * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) f hC hT hf
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
    Real.sqrt_mul (Nat.cast_nonneg K), Real.sqrt_sq (by positivity :
      (0 : ℝ) ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2)] at hb
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) *
        (2 * C * (∑ k ∈ P.support, ‖P.coeff k‖) *
          (Real.sqrt K * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 * C * (∑ k ∈ P.support, ‖P.coeff k‖) * Real.sqrt K) *
        (u ^ (N + 1) * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_shifted_cutoff_le hu N) (by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (Real.sqrt_nonneg K))

/-- The preceding allowance vanishes for every fixed filter and finite
spatial enlargement, uniformly over the supported bounded coefficients. -/
theorem tendsto_sum_filter_square_cutoff (P : Polynomial ℂ) (K : ℕ) (y : ℝ)
    (T : ℕ → Finset ℕ) (f : ℕ → ℕ → ℂ) {C u : ℝ} (hC : 0 ≤ C)
    (hu : 0 < u) (hu1 : u < 1)
    (hT : ∀ N n, n ∈ T N → 0 < n ∧
      n ≤ K * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hf : ∀ N n, n ∈ T N → ‖f N n‖ ≤ C) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ T N, f N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N =>
    norm_sum_filter_square_cutoff_le P N K y (T N) (f N) hC hu (hT N) (hf N))
  have hd := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul u
  have hp := ((tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1).comp
    (tendsto_add_atTop_nat 1)).const_mul 2
  simpa only [mul_zero, zero_add, mul_one_div, Function.comp_def] using
    (hd.add hp).const_mul (2 * C * (∑ k ∈ P.support, ‖P.coeff k‖) * Real.sqrt K)

/-- The canonical logarithmic cutoff stays above a fixed positive length. -/
theorem length_ge_log_four (u : ℝ) (N : ℕ) :
    Real.log 4 ≤ SquarefreeVaughanLogSource.length u N := by
  apply Real.log_le_log (by norm_num)
  have hd := Nat.cast_nonneg (α := ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  nlinarith

/-- A fixed spatial enlargement contributes only its own logarithm to
log n at the original common cutoff. -/
theorem log_le_length_add_log {a n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (u : ℝ) (N : ℕ)
    (hclip : n ≤ a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Real.log n ≤ SquarefreeVaughanLogSource.length u N + Real.log a := by
  have hc : (n : ℝ) ≤ (a : ℝ) *
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2 := by exact_mod_cast hclip
  have hl := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n) hc
  rw [Real.log_mul (by exact_mod_cast ha.ne' : (a : ℝ) ≠ 0) (by positivity)] at hl
  exact hl.trans_eq (add_comm _ _)

/-- The actual one-prime insertion within the moving cutoff, with its
original band and coefficient unchanged. -/
def clippedPrimeBand (a : ℕ) (u : ℝ) (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n =>
    (∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ n = p * a) ∧
      n ≤ a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- An explicit fixed cofactor constant; no large-prime label, order,
frequency, or moving cutoff occurs in it. -/
def clippedCoefficientCost (a : ℕ) : ℝ :=
  2 * divisorLogMass a * (1 + Real.log a / Real.log 4)

/-- The literal Riesz coefficient on this part of the original band is
uniformly bounded by the fixed cofactor constant. -/
theorem norm_clipped_coefficient_le {a : ℕ} (ha : 1 < a) (u : ℝ) (N : ℕ)
    {n : ℕ} (hn : n ∈ clippedPrimeBand a u N) :
    ‖SquarefreeVaughanLogSource.coefficient
      (SquarefreeVaughanLogSource.length u N) n‖ ≤ clippedCoefficientCost a := by
  obtain ⟨hb, ⟨⟨p, hp, hpa, rfl⟩, hc⟩⟩ := Finset.mem_filter.mp hn
  exact norm_coefficient_prime_mul_le (SquarefreeVaughanLogSource.length_pos u N)
    (Real.log_pos (by norm_num)) (length_ge_log_four u N) (by omega) hp hpa
    (Real.log_natCast_nonneg a)
    (log_le_length_add_log (by omega) (Nat.mul_pos hp.pos (by omega)) u N hc)

/-- The original clipped one-large-prime contribution tends to zero
with the full fixed polynomial filter and source normalization. This is an
independent arithmetic estimate, without a zeta-zero assumption. -/
theorem tendsto_actual_clipped_prime_band {a : ℕ} (ha : 1 < a)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ clippedPrimeBand a u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  refine tendsto_sum_filter_square_cutoff P a y (clippedPrimeBand a u)
    (fun N => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (C := clippedCoefficientCost a) ?_ hu hu1 ?_ ?_
  · unfold clippedCoefficientCost
    have hB := divisorLogMass_nonneg a
    have hl := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have ha0 := Real.log_natCast_nonneg a
    positivity
  · intro N n hn
    obtain ⟨hb, _, hc⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1, hc⟩
  · exact fun N n hn => norm_clipped_coefficient_le ha u N hn

/-- No divisor survives a nonpositive logarithmic cutoff. -/
theorem riesz_eq_zero_of_nonpos {L : ℝ} (hL : L ≤ 0) (n : ℕ) :
    VaughanLogAverage.riesz L n = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  rw [max_eq_left (by linarith [Real.log_natCast_nonneg d]), mul_zero]

/-- The complete mass and first moment cancel once the cutoff contains
all divisors of a squarefree nonunit composite. -/
theorem riesz_eq_zero_of_saturated {a : ℕ} (ha : Squarefree a) (ha1 : a ≠ 1)
    (hap : ¬ a.Prime) {L : ℝ} (hL : Real.log a ≤ L) :
    VaughanLogAverage.riesz L a = 0 := by
  have hm : (∑ d ∈ a.divisors, ((μ d : ℤ) : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero ha1
  have hl : (∑ d ∈ a.divisors, ((μ d : ℤ) : ℝ) * Real.log d) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_log_eq_zero ha hap
  calc
    _ = ∑ d ∈ a.divisors, ((μ d : ℤ) : ℝ) * (L - Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [max_eq_right]
      exact sub_nonneg.mpr ((Real.log_le_log (by
        exact_mod_cast Nat.pos_of_mem_divisors hd : (0 : ℝ) < d)
        (by exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero)
          (Nat.dvd_of_mem_divisors hd)))).trans hL)
    _ = 0 := by simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hm, hl, zero_mul, sub_zero]

/-- A composite fixed cofactor has no Riesz carrier once the inserted
prime lies above the common cutoff and the cofactor lies below it. -/
theorem coefficient_prime_mul_eq_zero_of_large {a p : ℕ} (ha : Squarefree a)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a)
    {L : ℝ} (haL : Real.log a ≤ L) (hLp : L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (p * a) = 0 := by
  have hr : VaughanLogAverage.riesz L (p * a) = 0 := by
    rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa,
      riesz_eq_zero_of_saturated ha ha1 hap haL,
      riesz_eq_zero_of_nonpos (sub_nonpos.mpr hLp), sub_zero]
  simp [SquarefreeVaughanLogSource.coefficient, hr]

/-- A prime fixed cofactor leaves an explicit semiprime tail above the
cutoff. The coefficient is not asserted to vanish or to have a small band sum. -/
theorem coefficient_prime_pair_above_cutoff {a p : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hpa : ¬ p ∣ a) {L : ℝ} (haL : Real.log a ≤ L) (hLp : L ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (p * a) =
      ((-Real.log (p * a : ℕ) * Real.log a / L : ℝ) : ℂ) := by
  have hL0 : 0 ≤ L := (Real.log_natCast_nonneg a).trans haL
  have hra : VaughanLogAverage.riesz L a = Real.log a := by
    rw [VaughanLogAverage.riesz, ha.sum_divisors]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one,
      Real.log_one, sub_zero, max_eq_right hL0, one_mul,
      ArithmeticFunction.moebius_apply_prime ha, Int.cast_neg, neg_mul,
      max_eq_right (sub_nonneg.mpr haL)]
    ring
  have hr : VaughanLogAverage.riesz L (p * a) = Real.log a := by
    rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpa, hra,
      riesz_eq_zero_of_nonpos (sub_nonpos.mpr hLp), sub_zero]
  have hsf := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, ha.squarefree⟩
  rw [SquarefreeVaughanLogSource.coefficient,
    if_pos ⟨hsf, Nat.not_prime_mul hp.ne_one ha.ne_one⟩, hr]

/-- Despite its damping, the canonical integer cutoff tends to infinity. -/
theorem tendsto_linearDampedCutoff {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (ZetaVaughanCutoffBudget.linearDampedCutoff u) atTop atTop := by
  have hn := tendsto_self_mul_const_pow_of_lt_one hu.le hu1
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hu.le hu1
  have hd : Tendsto (fun N : ℕ => ((N : ℝ) + 1) * u ^ N) atTop (𝓝 0) := by
    convert hn.add hp using 1
    · funext N; ring
    · simp
  have hpos : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1) * u ^ N ∈ Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun N => by
      change 0 < ((N : ℝ) + 1) * u ^ N
      positivity
  have hi := (tendsto_nhdsWithin_iff.mpr ⟨hd, hpos⟩).inv_tendsto_nhdsGT_zero
  have hq : Tendsto (fun N : ℕ => u⁻¹ ^ N / (N + 1)) atTop atTop := by
    convert hi using 1
    funext N
    simp only [Pi.inv_apply, mul_inv_rev, div_eq_mul_inv, inv_pow]
  exact tendsto_nat_floor_atTop.comp hq

/-- Every fixed cofactor is eventually below the original common
logarithmic cutoff. No zero or prime-distribution assumption is used. -/
theorem tendsto_length {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (SquarefreeVaughanLogSource.length u) atTop atTop := by
  have hd := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_linearDampedCutoff hu hu1)
  have hs : Tendsto (fun N => (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2)
      atTop atTop := tendsto_atTop_mono (fun N => by dsimp; linarith) hd
  have hpow := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hs
  exact Real.tendsto_log_atTop.comp hpow

/-- The original-band labels with one prime multiplying a specified
fixed cofactor. This is not an Euler completion. -/
def primeCofactorBand (a N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n => ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ n = p * a

/-- For a squarefree composite cofactor, the whole original-band
contribution equals its clipped part once the cutoff contains the cofactor. -/
theorem composite_cofactor_band_eq_clipped {a : ℕ} (ha : Squarefree a)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (P : Polynomial ℂ) (y u : ℝ) (N : ℕ)
    (hLa : Real.log a ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ primeCofactorBand a N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ n ∈ clippedPrimeBand a u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  simp only [primeCofactorBand, clippedPrimeBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ n = p * a
  · obtain ⟨p, hpp, hpa, rfl⟩ := hp
    by_cases hc : p * a ≤ a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
    · rw [if_pos ⟨p, hpp, hpa, rfl⟩, if_pos ⟨⟨p, hpp, hpa, rfl⟩, hc⟩]
    · rw [if_pos ⟨p, hpp, hpa, rfl⟩, if_neg (fun h => hc h.2)]
      have hgt : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
        have hnle := Nat.lt_of_not_ge hc
        nlinarith [Nat.pos_of_ne_zero ha.ne_zero]
      have hlp : SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast hgt.le
      rw [coefficient_prime_mul_eq_zero_of_large ha ha1 hap hpp hpa hLa hlp, zero_mul]
  · rw [if_neg hp, if_neg (fun h => hp h.1)]

/-- An entire fixed squarefree composite-cofactor prime class is
arithmetically negligible at the original source scale. The genuine band,
common cutoff, height, and full polynomial filter all remain unchanged. -/
theorem tendsto_actual_composite_cofactor_band {a : ℕ} (ha : Squarefree a)
    (ha1 : a ≠ 1) (hap : ¬ a.Prime) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ primeCofactorBand a N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  have he := (tendsto_length hu hu1).eventually_ge_atTop (Real.log a)
  apply (tendsto_actual_clipped_prime_band (a := a) (by
    have h0 := Nat.pos_of_ne_zero ha.ne_zero
    omega) P y hu hu1).congr'
  filter_upwards [he] with N hN
  rw [composite_cofactor_band_eq_clipped ha ha1 hap P y u N hN]

end
end RiemannGaussian.ZetaRieszFixedCofactor
