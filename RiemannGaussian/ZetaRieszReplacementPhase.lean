/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeReplacement

/-!
# The exact phase of a prime replacement

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszReplacementPhase
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open ZetaRieszPrimeReplacement ZetaArithmeticBandCorrelation

/-- Every replacement phase separates exactly from the same complete
polynomial amplitude. Its real coordinate and normalization are unchanged. -/
theorem logAmplitude_add_imag (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (sigma t v : ℝ) :
    logAmplitude L P N (sigma + Complex.I * t) v =
      logAmplitude L P N (sigma : ℂ) v * unitPhase (-t * v) := by
  unfold logAmplitude
  rw [zetaPrimeFilterKernel_add_parameter]
  have he : Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log (Real.exp v) : ℂ)) =
      unitPhase (-t * v) := by
    rw [Real.log_exp]
    unfold unitPhase
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Rotating the full amplitude preserves its exact norm, for every
polynomial and every height, without a size penalty in the ordinate. -/
theorem norm_logAmplitude_add_imag (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (sigma t v : ℝ) :
    ‖logAmplitude L P N (sigma + Complex.I * t) v‖ =
      ‖logAmplitude L P N (sigma : ℂ) v‖ := by
  rw [logAmplitude_add_imag, norm_mul, norm_unitPhase, mul_one]

/-- The exact phase mismatch is a sine of half the relative angle.
Full rotations therefore remain visible to the bound. -/
theorem norm_unitPhase_sub_eq (x y : ℝ) :
    ‖unitPhase x - unitPhase y‖ = 2 * |Real.sin ((x - y) / 2)| := by
  have he : unitPhase x - unitPhase y = unitPhase y * (unitPhase (x - y) - 1) := by
    unfold unitPhase
    rw [mul_sub, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · ring
  rw [he, norm_mul, norm_unitPhase, one_mul, unitPhase,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The actual amplitude mismatch separates its slowly varying
polynomial part from the exact relative phase. Large heights are not
replaced by a monotone linear phase cost. -/
theorem norm_logAmplitude_sub_le_phase (P : Polynomial ℂ) (N : ℕ) (sigma t : ℝ)
    {L r A B x y : ℝ} (hL : 0 < L) (hr : 0 < r) (hrs : r ≤ sigma) (hA : 0 ≤ A)
    (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc A B) :
    ‖logAmplitude L P (N + 1) (sigma + Complex.I * t) y -
      logAmplitude L P (N + 1) (sigma + Complex.I * t) x‖ ≤
      logAmplitudeAllowance L P N (sigma : ℂ) r A B * |y - x| +
        (B / L * logKernelEnvelope P (N + 1) (sigma : ℂ) r A) *
          (2 * |Real.sin (t * (y - x) / 2)|) := by
  rw [logAmplitude_add_imag, logAmplitude_add_imag]
  have he (a b u v : ℂ) : a * u - b * v = (a - b) * u + b * (u - v) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_unitPhase, mul_one, norm_unitPhase_sub_eq]
  have hang : (-t * y - -t * x) / 2 = -(t * (y - x) / 2) := by ring
  rw [hang, Real.sin_neg, abs_neg]
  exact add_le_add (norm_logAmplitude_sub_le P N (sigma : ℂ) hL hr hrs hA hx hy)
    (mul_le_mul_of_nonneg_right
      (norm_logAmplitude_le P (N + 1) (sigma : ℂ) hL hr hrs (hA.trans hx.1) hx.1 hx.2)
      (by positivity))

/-- The exact signed logarithmic difference cancels the common
cofactor before the relative phase is measured. -/
theorem replacement_log_difference {a b q n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hn : 0 < n) :
    Real.log (a * (b * n) : ℕ) - Real.log (q * n : ℕ) =
      Real.log (a * b : ℕ) - Real.log q := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have habR : ((a * b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos ha hb).ne'
  rw [← Nat.mul_assoc a b n]
  simp only [Nat.cast_mul]
  rw [Real.log_mul (by simpa using habR) hnR, Real.log_mul hqR hnR,
    add_sub_add_right_eq_sub]

/-- An explicit replacement cost retains the exact oscillatory chord.
All smooth-amplitude allowances are evaluated on the real spectral line;
height enters only through the original relative sine, with its resonances. -/
def phaseReplacementCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ)
    (a b q n : ℕ) : ℝ :=
  let A := min (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let E := B / L * logKernelEnvelope P (N + 1) (3 / 2 : ℂ) r A
  let D := logAmplitudeAllowance L P N (3 / 2 : ℂ) r A B
  let gap := |Real.log q - Real.log (a * b : ℕ)|
  (E * gap + (D * gap + E * (2 * |Real.sin (t * (Real.log (a * b : ℕ) - Real.log q) / 2)|)) *
    min (Real.log a) (Real.log b)) *
      ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|

/-- A whole pair of original band weights has a phase-sensitive
arithmetic error bound. Squarefree support, complete factorial amplitudes,
actual cutoffs and relative phase are all retained and their bounds proved.
No height-dependent phase cost is linearized in this estimate. -/
theorem norm_bandWeight_replacement_pair_le_phase (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q n : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L)
    (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1))
    (hBandAB : a * (b * n) ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (a * (b * n))‖ ≤
      phaseReplacementCost L P N t r a b q n := by
  let A := min (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let E := B / L * logKernelEnvelope P (N + 1) (3 / 2 : ℂ) r A
  let D := logAmplitudeAllowance L P N (3 / 2 : ℂ) r A B
  let gap := |Real.log q - Real.log (a * b : ℕ)|
  let chord := 2 * |Real.sin (t * (Real.log (a * b : ℕ) - Real.log q) / 2)|
  have hA : 0 ≤ A := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hx : Real.log (q * n : ℕ) ∈ Set.Icc A B := ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : Real.log (a * (b * n) : ℕ) ∈ Set.Icc A B := ⟨min_le_right _ _, le_max_right _ _⟩
  have hrs : r ≤ (3 / 2 : ℂ).re := by norm_num; exact hr3
  have hsupq := prime_mul_composite_support hq hn hn1 hqn
  have hbn' := prime_mul_composite_support hb hn hn1 hbn
  have hb1 : b * n ≠ 1 := by intro he; exact hb.ne_one (mul_eq_one.mp he).1
  have hsupab := prime_mul_composite_support ha hbn'.1 hb1 (not_dvd_prime_mul ha hb hab han)
  have hqeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandQ, hsupq⟩
  have habeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandAB, hsupab⟩
  have hamp : ‖bandAmplitude L P (N + 1) t (q * n)‖ ≤ E := by
    rw [hqeq]
    have he := norm_logAmplitude_add_imag L P (N + 1) (3 / 2) t (Real.log (q * n : ℕ))
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
    rw [he]
    exact norm_logAmplitude_le P (N + 1) (3 / 2 : ℂ)
      (L := L) (r := r) (A := A) (B := B) (v := Real.log (q * n : ℕ))
      hL hr hrs (Real.log_natCast_nonneg (q * n)) hx.1 hx.2
  have hdiff : ‖bandAmplitude L P (N + 1) t (a * (b * n)) -
      bandAmplitude L P (N + 1) t (q * n)‖ ≤ D * gap + E * chord := by
    rw [hqeq, habeq]
    have hh := norm_logAmplitude_sub_le_phase P N (3 / 2) t hL hr hr3 hA hx hy
    rw [replacement_log_difference ha.pos hb.pos hq.pos (Nat.pos_of_ne_zero hn.ne_zero),
      abs_sub_comm (Real.log (a * b : ℕ)) (Real.log q)] at hh
    simpa only [D, E, gap, chord, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  apply (norm_bandWeight_replacement_pair_le L P (N + 1) t
    ha hb hq hab han hbn hqn hn hn1 haL hbL).trans
  change _ ≤ (E * gap + (D * gap + E * chord) * min (Real.log a) (Real.log b)) * _
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
  exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hdiff (le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)))

end
end RiemannGaussian.ZetaRieszReplacementPhase
