import RiemannGaussian.EtaMoebiusTrialRefinement
import RiemannGaussian.EtaMoebiusLogHarmonic

/-!
# Exact arithmetic on the target interval of the Möbius candidate

The actual finite translate sum telescopes on the entire compact target
interval. Its value is the original signed primitive at the exact rounded
physical coordinate. For the logarithmic weights this isolates the
harmonic correction, retaining the finite-grid rounding error explicitly.
-/

open Complex Set
open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem sum_range_tail_difference (A : ℕ → ℝ) (d r : ℕ) :
    (∑ j ∈ Finset.range d, if r ≤ j then A j - A (j + 1) else 0) =
      if r ≤ d then A r - A d else 0 := by
  induction d with
  | zero => by_cases hr : r = 0 <;> simp [hr]
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hr : r ≤ d
    · simp [hr, show r ≤ d + 1 by omega]
    · by_cases hs : r ≤ d + 1
      · have he : r = d + 1 := by omega
        simp [he]
      · simp [hr, hs]

/-- The exact rounded physical coordinate selected by the original finite-grid head sum. -/
def pairedEtaMoebiusTrialHeadCoordinate (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) / (⌊(d : ℝ) / Real.exp t⌋₊ + 1 : ℝ)

/-- On the target interval the entire translated eta indicator reduces to its literal first cell, with the original open left endpoint. -/
theorem pairedEtaTranslatedColour_eq_head_ite {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ Real.log 2) :
    pairedEtaTranslatedColour a t = if a < t then 1 else 0 := by
  by_cases hat : a < t
  · rw [if_pos hat, pairedEtaTranslatedColour, pairedEtaLogIndicator_eq_cellColour (n := 0)]
    · simp [pairedEtaLogCellColour]
    · simp only [pairedEtaLogCell, Nat.cast_zero, zero_add, Real.log_one, mem_Ioc]
      constructor <;> linarith
  · rw [if_neg hat, pairedEtaTranslatedColour, pairedEtaLogIndicator_eq_zero_of_nonpos (by linarith)]

private theorem gridPoint_lt_iff_floor {d : ℕ} (j : Fin d) (t : ℝ) :
    pairedEtaMoebiusTrialGridPoint d (j.1 + 1) < t ↔
      ⌊(d : ℝ) / Real.exp t⌋₊ ≤ j.1 := by
  have hjd := j.isLt
  have hj : (0 : ℝ) < j.1 + 1 := by positivity
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [pairedEtaMoebiusTrialGridPoint_eq_log (by omega) (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.log_lt_iff_lt_exp (div_pos hd hj), div_lt_iff₀ hj]
  have hf : ⌊(d : ℝ) / Real.exp t⌋₊ < j.1 + 1 ↔ (d : ℝ) / Real.exp t < (j.1 + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.floor_lt (n := j.1 + 1) (show 0 ≤ (d : ℝ) / Real.exp t by positivity))
  rw [show (⌊(d : ℝ) / Real.exp t⌋₊ ≤ j.1) ↔ (⌊(d : ℝ) / Real.exp t⌋₊ < j.1 + 1) by omega,
    hf, div_lt_iff₀ (Real.exp_pos t)]
  rw [mul_comm]

/-- The complete coefficient sum against an original causal step telescopes to the exact sampled arithmetic primitive at every time. -/
theorem pairedEtaMoebiusTrialGridStep_sum (d M : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    (∑ j : Fin d, pairedEtaMoebiusTrialCoefficient d M w j *
      (if pairedEtaMoebiusTrialGridPoint d (j.1 + 1) < t then 1 else 0)) =
        pairedEtaMoebiusTrialPrimitive M w (pairedEtaMoebiusTrialHeadCoordinate d t) := by
  let A := fun j : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (j + 1 : ℝ))
  let r := ⌊(d : ℝ) / Real.exp t⌋₊
  have hA : A d = 0 := pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one M w
    ((div_lt_one (by positivity)).mpr (by linarith))
  have hsum := sum_range_tail_difference A d r
  have hAr : (if r ≤ d then A r - A d else 0) = A r := by
    rw [hA, sub_zero]
    split_ifs with hr
    · rfl
    · symm
      apply pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one
      apply (div_lt_one (by positivity)).mpr
      exact_mod_cast (show d < r + 1 by omega)
  rw [hAr] at hsum
  calc
    _ = ∑ j : Fin d, if r ≤ j.1 then A j.1 - A (j.1 + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [gridPoint_lt_iff_floor]
      split_ifs <;> simp [pairedEtaMoebiusTrialCoefficient, A, Nat.cast_add, Nat.cast_one, add_assoc]
      norm_num
    _ = _ := by
      simpa only [← Fin.sum_univ_eq_sum_range, A, r, pairedEtaMoebiusTrialHeadCoordinate] using hsum

/-- The complete original finite-grid combination telescopes to its signed arithmetic primitive throughout the target interval. -/
theorem pairedEtaMoebiusTrialGridCombination_eq_head_primitive (d M : ℕ) (w : ℕ → ℝ)
    {t : ℝ} (ht : t ≤ Real.log 2) :
    pairedEtaMoebiusTrialGridCombination d M w t =
      (pairedEtaMoebiusTrialPrimitive M w (pairedEtaMoebiusTrialHeadCoordinate d t) : ℂ) := by
  rw [← pairedEtaMoebiusTrialGridStep_sum d M w t, Complex.ofReal_sum]
  unfold pairedEtaMoebiusTrialGridCombination pairedEtaTranslatedCombination
  apply Finset.sum_congr rfl
  intro j _
  rw [pairedEtaTranslatedColour_eq_head_ite (pairedEtaMoebiusTrialGridPoint_nonneg _ _) ht,
    Complex.ofReal_mul]

/-- On the positive target interval the rounded coordinate remains above one and strictly below the true physical coordinate. -/
theorem pairedEtaMoebiusTrialHeadCoordinate_bounds {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : 0 < t) : 1 ≤ pairedEtaMoebiusTrialHeadCoordinate d t ∧
      pairedEtaMoebiusTrialHeadCoordinate d t < Real.exp t := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hexp : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hfloor : ⌊(d : ℝ) / Real.exp t⌋₊ < d := by
    apply (Nat.floor_lt (by positivity)).mpr
    exact (div_lt_self hdp hexp)
  have hfl : (d : ℝ) / Real.exp t < (⌊(d : ℝ) / Real.exp t⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  unfold pairedEtaMoebiusTrialHeadCoordinate
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    norm_num only [one_mul]
    exact_mod_cast (show ⌊(d : ℝ) / Real.exp t⌋₊ + 1 ≤ d by omega)
  · apply (div_lt_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ (Real.exp_pos t)).mp hfl
    nlinarith

/-- The arithmetic primitive on the initial unit-to-two interval isolates precisely its original harmonic endpoint correction. -/
theorem pairedEtaMoebiusTrialPrimitive_eq_head {M : ℕ} (hM : 1 < M) {x : ℝ}
    (hx : 1 ≤ x) (hx2 : x < 2) :
    pairedEtaMoebiusTrialPrimitive M (pairedEtaMoebiusTrialLogWeight M) x =
      x * (1 - pairedEtaMoebiusLogHarmonic M) := by
  rw [pairedEtaMoebiusTrialPrimitive_eq_harmonic_difference M _ hx]
  congr 1
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp [hx, pairedEtaMoebiusTrialLogWeight, hM]
  · intro n hn hn1
    have hnx : ¬ (n : ℝ) ≤ x := by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega)
      linarith
    simp [hnx]
  · simp [Finset.mem_Icc, show 1 ≤ M by omega]

/-- The entire actual head combination has a closed signed arithmetic value, including its exact grid rounding. -/
theorem pairedEtaMoebiusTrialGridCombination_eq_head {d M : ℕ} (hd : 0 < d) (hM : 1 < M)
    {t : ℝ} (ht : t ∈ Ioc 0 (Real.log 2)) :
    pairedEtaMoebiusTrialGridCombination d M (pairedEtaMoebiusTrialLogWeight M) t =
      (pairedEtaMoebiusTrialHeadCoordinate d t * (1 - pairedEtaMoebiusLogHarmonic M) : ℝ) := by
  rw [pairedEtaMoebiusTrialGridCombination_eq_head_primitive d M _ ht.2]
  have hb := pairedEtaMoebiusTrialHeadCoordinate_bounds hd ht.1
  have hx2 : pairedEtaMoebiusTrialHeadCoordinate d t < 2 :=
    hb.2.trans_le ((Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by norm_num)))
  rw [pairedEtaMoebiusTrialPrimitive_eq_head hM hb.1 hx2]

/-- The exact rounded head coordinate loses at most the square of the physical coordinate divided by the grid dimension. -/
theorem pairedEtaMoebiusTrialHeadCoordinate_error_le {d : ℕ} (hd : 0 < d) (t : ℝ) :
    Real.exp t - pairedEtaMoebiusTrialHeadCoordinate d t ≤ (Real.exp t) ^ 2 / d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  let b : ℝ := (⌊(d : ℝ) / Real.exp t⌋₊ : ℝ) + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hlo : (d : ℝ) / Real.exp t < b := Nat.lt_floor_add_one _
  have htop : Real.exp t * b - d ≤ Real.exp t := by
    have h := (le_div_iff₀ (Real.exp_pos t)).mp
      (Nat.floor_le (show 0 ≤ (d : ℝ) / Real.exp t by positivity))
    dsimp [b]
    nlinarith
  have hbottom : (d : ℝ) ≤ Real.exp t * b := by
    have h := (div_lt_iff₀ (Real.exp_pos t)).mp hlo
    nlinarith
  change Real.exp t - (d : ℝ) / b ≤ _
  calc
    _ = (Real.exp t * b - d) / b := by field_simp
    _ ≤ Real.exp t / b := div_le_div_of_nonneg_right htop hb.le
    _ ≤ (Real.exp t) ^ 2 / d := by
      apply (div_le_div_iff₀ hb hdp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hbottom (Real.exp_pos t).le]

/-- On the whole compact target interval, the actual finite-grid rounding error is at most `4/d`. -/
theorem abs_exp_sub_pairedEtaMoebiusTrialHeadCoordinate_le {d : ℕ} (hd : 0 < d)
    {t : ℝ} (ht : t ∈ Ioc 0 (Real.log 2)) :
    |Real.exp t - pairedEtaMoebiusTrialHeadCoordinate d t| ≤ 4 / (d : ℝ) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (pairedEtaMoebiusTrialHeadCoordinate_bounds hd ht.1).2.le)]
  apply (pairedEtaMoebiusTrialHeadCoordinate_error_le hd t).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  have hx : Real.exp t ≤ 2 := (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by norm_num))
  nlinarith [Real.exp_pos t]

/-- The exact signed residual separates the genuine arithmetic endpoint error from the actual mesh error. -/
theorem pairedEtaMoebiusTrialHeadResidual_eq {d M : ℕ} (hd : 0 < d) (hM : 1 < M)
    {t : ℝ} (ht : t ∈ Ioc 0 (Real.log 2)) :
    pairedEtaProjectionHead t - pairedEtaMoebiusTrialGridCombination d M (pairedEtaMoebiusTrialLogWeight M) t =
      (Real.exp t * pairedEtaMoebiusLogHarmonic M +
        (Real.exp t - pairedEtaMoebiusTrialHeadCoordinate d t) * (1 - pairedEtaMoebiusLogHarmonic M) : ℝ) := by
  rw [pairedEtaMoebiusTrialGridCombination_eq_head hd hM ht, pairedEtaProjectionHead, indicator_of_mem ht]
  push_cast
  ring

/-- The full original residual on the target interval has a uniform bound in its actual harmonic correction and grid dimension. -/
theorem norm_pairedEtaMoebiusTrialHeadResidual_le {d M : ℕ} (hd : 0 < d) (hM : 1 < M)
    {t : ℝ} (ht : t ∈ Ioc 0 (Real.log 2)) :
    ‖pairedEtaProjectionHead t - pairedEtaMoebiusTrialGridCombination d M (pairedEtaMoebiusTrialLogWeight M) t‖ ≤
      2 * |pairedEtaMoebiusLogHarmonic M| + 4 * |1 - pairedEtaMoebiusLogHarmonic M| / d := by
  rw [pairedEtaMoebiusTrialHeadResidual_eq hd hM ht, Complex.norm_real, Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos t)]
  have hx : Real.exp t ≤ 2 := (Real.exp_le_exp.mpr ht.2).trans_eq (Real.exp_log (by norm_num))
  have hh := mul_le_mul_of_nonneg_right hx (abs_nonneg (pairedEtaMoebiusLogHarmonic M))
  have hg := mul_le_mul_of_nonneg_right (abs_exp_sub_pairedEtaMoebiusTrialHeadCoordinate_le hd ht)
    (abs_nonneg (1 - pairedEtaMoebiusLogHarmonic M))
  convert add_le_add hh hg using 1
  ring

end

end RiemannGaussian
