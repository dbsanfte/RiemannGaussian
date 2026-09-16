/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMassTransport
import RiemannGaussian.ZetaRieszSharpMatching
import RiemannGaussian.ZetaRieszCosineCarrier

/-!
# Retain the full polynomial direction and arithmetic sign

Every sent pair and remaining original amplitude stays explicit. Complete
fallback coverage controls the final unsent mass, but all fallback chord
costs remain in the whole bound. A source-scale bound for the sent sum and
a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTransportPhase
noncomputable section
open scoped BigOperators Classical
open ZetaRieszMassTransport

/-- A real phase rotation changes only the retained unit direction. -/
theorem ray_mul_unitPhase (z : ℂ) (x : ℝ) :
    ray (z * ZetaArithmeticBandCorrelation.unitPhase x) =
      ray z * ZetaArithmeticBandCorrelation.unitPhase x := by
  simp only [ray, norm_mul, ZetaArithmeticBandCorrelation.norm_unitPhase, mul_one,
    Complex.real_smul]
  ring

/-- Normalizing an already normalized ray makes no change, including zero. -/
theorem ray_ray (z : ℂ) : ray (ray z) = ray z := by
  by_cases hz : z = 0
  · simp [hz, ray]
  · change ‖ray z‖⁻¹ • ray z = ray z
    rw [norm_ray hz]
    simp

/-- Positive rescaling preserves the complete original complex direction. -/
theorem ray_pos_smul {a : ℝ} (ha : 0 < a) (z : ℂ) : ray (a • z) = ray z := by
  simp only [ray, norm_smul, Real.norm_of_nonneg ha.le, mul_inv_rev, smul_smul]
  have h : (‖z‖⁻¹ * a⁻¹) * a = ‖z‖⁻¹ := by rw [mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
  rw [h]

/-- Every nonempty remainder keeps exactly its incoming phase. -/
theorem ray_remainder {a : ℝ} {z : ℂ} (ha : a < ‖z‖) :
    ray (remainder a z) = ray z := by
  rw [remainder, ray_pos_smul (sub_pos.mpr ha), ray_ray]

/-- The full polynomial carrier has its exact zero-height direction and
its literal multiplicative phase, with no derivative allowance. -/
theorem ray_bandWeight (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (n : ℕ) :
    ray (ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 n) *
        ZetaArithmeticBandCorrelation.unitPhase (-t * Real.log n) := by
  rw [ZetaArithmeticBandCorrelation.bandWeight_phase, ray_mul_unitPhase]

/-- The phase cost uses the complete zero-height polynomial directions;
the common logarithmic phase cancels exactly. -/
theorem pairCost_bandWeight_eq_relative (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) (i j : ℕ) :
    pairCost (ZetaRieszConditionedEnergy.bandWeight L P N t i)
      (ZetaRieszConditionedEnergy.bandWeight L P N t j) =
      pairMass (ZetaRieszConditionedEnergy.bandWeight L P N 0 i)
        (ZetaRieszConditionedEnergy.bandWeight L P N 0 j) *
      ‖ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 i) +
        ray (ZetaRieszConditionedEnergy.bandWeight L P N 0 j) *
          ZetaArithmeticBandCorrelation.unitPhase (-t * (Real.log j - Real.log i))‖ := by
  open ZetaArithmeticBandCorrelation in
  have hp (x y : ℝ) : unitPhase y = unitPhase (y - x) * unitPhase x := by
    rw [unitPhase, unitPhase, unitPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm (n : ℕ) : ‖ZetaRieszConditionedEnergy.bandWeight L P N t n‖ =
      ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 n‖ := by
    rw [ZetaArithmeticBandCorrelation.bandWeight_phase, norm_mul,
      ZetaArithmeticBandCorrelation.norm_unitPhase, mul_one]
  unfold pairCost pairMass
  rw [hm i, hm j, ray_bandWeight L P N t i, ray_bandWeight L P N t j]
  rw [hp (-t * Real.log i) (-t * Real.log j)]
  have he : -t * Real.log j - -t * Real.log i = -t * (Real.log j - Real.log i) := by ring
  rw [he, ← mul_assoc, ← add_mul, norm_mul,
    ZetaArithmeticBandCorrelation.norm_unitPhase, mul_one]

/-- The normalized direction of a positive real coefficient is one. -/
theorem ray_real_pos {a : ℝ} (ha : 0 < a) : ray (a : ℂ) = 1 := by
  rw [ray, Complex.norm_real, Real.norm_of_nonneg ha.le, Complex.real_smul,
    ← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one]

/-- Negating a coefficient negates its full normalized direction. -/
theorem ray_neg (z : ℂ) : ray (-z) = -ray z := by
  simp only [ray, norm_neg, smul_neg]

/-- The normalized direction of a negative real coefficient is minus one. -/
theorem ray_real_neg {a : ℝ} (ha : a < 0) : ray (a : ℂ) = -1 := by
  have h := ray_real_pos (neg_pos.mpr ha)
  rw [Complex.ofReal_neg, ray_neg] at h
  exact neg_injective (by simpa using h)

/-- Equal arithmetic signs pay the cosine chord; opposite arithmetic
signs pay the sine chord. Zero mass makes either boundary convention harmless. -/
def signedChord (a b x : ℝ) : ℝ :=
  if 0 ≤ a * b then 2 * |Real.cos (x / 2)| else 2 * |Real.sin (x / 2)|

/-- The actual sent mass has a fully explicit sign-sensitive phase cost.
No amplitude difference or derivative allowance is needed after splitting. -/
theorem pairCost_real_phases (a b x y : ℝ) :
    pairCost ((a : ℂ) * ZetaArithmeticBandCorrelation.unitPhase x)
      ((b : ℂ) * ZetaArithmeticBandCorrelation.unitPhase y) =
      min |a| |b| * signedChord a b (x - y) := by
  have hm (c v : ℝ) : ‖(c : ℂ) * ZetaArithmeticBandCorrelation.unitPhase v‖ = |c| := by
    rw [norm_mul, ZetaArithmeticBandCorrelation.norm_unitPhase, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  unfold pairCost pairMass
  rw [hm a x, hm b y, ray_mul_unitPhase, ray_mul_unitPhase]
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [ray_real_neg ha, ray_real_neg hb, neg_one_mul, neg_one_mul,
        ← neg_add, norm_neg, ZetaRieszOppositePrimes.norm_unitPhase_add_eq]
      rw [signedChord, if_pos (mul_nonneg_of_nonpos_of_nonpos ha.le hb.le)]
    · simp [hb, ray, signedChord]
    · rw [ray_real_neg ha, ray_real_pos hb, neg_one_mul, one_mul]
      have he : -ZetaArithmeticBandCorrelation.unitPhase x + ZetaArithmeticBandCorrelation.unitPhase y =
          -(ZetaArithmeticBandCorrelation.unitPhase x - ZetaArithmeticBandCorrelation.unitPhase y) := by ring
      rw [he, norm_neg, ZetaRieszReplacementPhase.norm_unitPhase_sub_eq,
        signedChord, if_neg (not_le.mpr (mul_neg_of_neg_of_pos ha hb))]
  · simp [ha, ray, signedChord]
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [ray_real_pos ha, ray_real_neg hb, one_mul, neg_one_mul, ← sub_eq_add_neg,
        ZetaRieszReplacementPhase.norm_unitPhase_sub_eq,
        signedChord, if_neg (not_le.mpr (mul_neg_of_pos_of_neg ha hb))]
    · simp [hb, ray, signedChord]
    · rw [ray_real_pos ha, ray_real_pos hb, one_mul, one_mul,
        ZetaRieszOppositePrimes.norm_unitPhase_add_eq,
        signedChord, if_pos (mul_nonneg ha.le hb.le)]

/-- The literal unfiltered zero-height weight, including the original
support, Riesz sign and positive factorial envelope. -/
def realBandOne (L : ℝ) (N n : ℕ) : ℝ :=
  if n ∈ zetaPrimeLogBand N then (SquarefreeVaughanLogSource.coefficient L n).re *
    (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial)
  else 0

/-- The zero-height constant-filter band weight is exactly real. -/
theorem bandWeight_one_zero (L : ℝ) (N n : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L 1 N 0 n = (realBandOne L N n : ℂ) := by
  unfold ZetaRieszConditionedEnergy.bandWeight realBandOne
  split_ifs with hn
  · apply Complex.ext
    · simpa only [Complex.ofReal_re, zero_mul, Real.cos_zero, mul_one] using
        ZetaRieszCosineCarrier.re_coefficient_filter_one L 0 N n
    · rw [Complex.mul_im, ZetaRieszCosineCarrier.coefficient_im_eq_zero,
        zero_mul, add_zero]
      have hk : (zetaPrimeFilterKernel 1 N (3 / 2 + Complex.I * ((0 : ℝ) : ℂ)) n).im = 0 := by
        simp only [zetaPrimeFilterKernel, ZetaRieszCosineCarrier.factorialPolynomial_one,
          Complex.ofReal_zero, mul_zero, add_zero]
        have hx : -(3 / 2 : ℂ) * (Real.log (n : ℝ) : ℂ) =
            ((-(3 / 2 : ℝ) * Real.log n : ℝ) : ℂ) := by push_cast; rfl
        rw [hx, ← Complex.ofReal_exp]
        have hp : (Real.log (n : ℝ) : ℂ) ^ N / (N.factorial : ℂ) =
            (((Real.log (n : ℝ)) ^ N / N.factorial : ℝ) : ℂ) := by push_cast; rfl
        rw [hp, ← Complex.ofReal_mul, Complex.ofReal_im]
      rw [hk, mul_zero, Complex.ofReal_im]
  · rfl

/-- Every unfiltered original atom retains its exact signed real mass
and multiplicative phase. This is a complex identity, not a real projection. -/
theorem bandWeight_one_eq_signed_phase (L : ℝ) (N : ℕ) (t : ℝ) (n : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L 1 N t n =
      (realBandOne L N n : ℂ) * ZetaArithmeticBandCorrelation.unitPhase (-t * Real.log n) := by
  rw [ZetaArithmeticBandCorrelation.bandWeight_phase, bandWeight_one_zero]

/-- The full actual unfiltered pair cost distinguishes arithmetic sign
from the multiplicative phase, with no amplitude-mismatch allowance. -/
theorem pairCost_bandWeight_one (L : ℝ) (N : ℕ) (t : ℝ) (i j : ℕ) :
    pairCost (ZetaRieszConditionedEnergy.bandWeight L 1 N t i)
      (ZetaRieszConditionedEnergy.bandWeight L 1 N t j) =
      min |realBandOne L N i| |realBandOne L N j| *
        signedChord (realBandOne L N i) (realBandOne L N j)
          (-t * (Real.log i - Real.log j)) := by
  rw [bandWeight_one_eq_signed_phase L N t i, bandWeight_one_eq_signed_phase L N t j,
    pairCost_real_phases]
  congr 2
  ring

end
end RiemannGaussian.ZetaRieszTransportPhase
