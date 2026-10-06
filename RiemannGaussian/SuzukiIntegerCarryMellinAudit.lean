/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiIntegerCarry
import RiemannGaussian.EtaAlternatingReal
import Mathlib.MeasureTheory.Group.Integral

/-!
# Spectral sensitivity of integer-carry tests

Binary carry is the parity of a quotient. Its logarithmic Mellin cells are
the translated eta cells `(log((2n+1)/2), log((2n+2)/2)]`. The endpoints
used for the integral do not alter the exact integer-quotient convention
of `SuzukiIntegerCarry`; the two real-colour conventions differ only at
cell endpoints.

The full integral-cell transform contains zeta as a factor. Consequently
every genuine zeta zero is invisible to this leading power-mode test.
This limits the *linear Mellin test*, not the full force of integer
factorization or the possibility of using nonlinear arithmetic constraints.
-/

namespace RiemannGaussian.SuzukiIntegerCarryMellinAudit
noncomputable section
open Complex MeasureTheory
open scoped Interval

/-- The literal left-closed quotient colour in the logarithmic variable.
Its convention is kept distinct from the eta measure at cell endpoints. -/
def carryLogColour (t : ℝ) : ℝ :=
  if Even (⌊2 * Real.exp t⌋ : ℤ) then 0 else 1

/-- The real colour gives the exact integer carry at every positive
rational quotient, including all discontinuity endpoints. -/
theorem carryLogColour_log_quotient {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    carryLogColour (Real.log ((N : ℝ) / d)) = (SuzukiIntegerCarry.carry N d : ℝ) := by
  have hq : 0 < (N : ℝ) / d := by positivity
  have hfloor : (⌊2 * ((N : ℝ) / d)⌋ : ℤ) = (((2 * N) / d : ℕ) : ℤ) := by
    rw [show 2 * ((N : ℝ) / d) = ((2 * N : ℕ) : ℝ) / d by push_cast; ring,
      Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  rw [carryLogColour, Real.exp_log hq, hfloor]
  simp only [Int.even_coe_nat, Nat.even_iff, ← SuzukiIntegerCarry.carry_eq_mod_two]
  rcases SuzukiIntegerCarry.carry_eq_zero_or_one N d with h | h <;> simp [h]

private theorem logIndicator_eq_colour_all (t : ℝ) :
    pairedEtaLogIndicator t = etaUnitIntervalColour (Real.exp t) := by
  by_cases ht : 0 < t
  · exact pairedEtaLogIndicator_eq_unitIntervalColour_exp ht
  · have he : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr (le_of_not_gt ht)
    have hc : (⌈Real.exp t⌉ : ℤ) = 1 :=
      Int.ceil_eq_iff.mpr (by constructor; simpa using Real.exp_pos t; simpa using he)
    have hnot : t ∉ pairedEtaLogSupport := fun h => ht (pairedEtaLogSupport_subset_Ioi_zero h)
    simp [pairedEtaLogIndicator, etaUnitIntervalColour, hc, hnot]

/-- Only the countable half-integer cell endpoints separate floor-carry
and eta conventions. This equality is used for integrals, never for a
literal prime sum at a discontinuity. -/
theorem carryLogColour_ae_eq_eta :
    carryLogColour =ᵐ[volume] fun t => pairedEtaLogIndicator (t + Real.log 2) := by
  let boundary : Set ℝ := Set.range (fun n : ℤ => Real.log (n : ℝ) - Real.log 2)
  have hb : volume boundary = 0 := (Set.countable_range _).measure_zero volume
  have hae : ∀ᵐ t : ℝ ∂volume, t ∉ boundary := by
    rw [ae_iff]
    simpa using hb
  filter_upwards [hae] with t ht
  have hnot : 2 * Real.exp t ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨n, hn⟩
    have hl : Real.log (n : ℝ) = Real.log 2 + t := by
      rw [hn, Real.log_mul (by norm_num) (Real.exp_pos t).ne', Real.log_exp]
    exact ht ⟨n, by linarith⟩
  have hc := (Int.ceil_eq_floor_add_one_iff_notMem (2 * Real.exp t)).mpr hnot
  rw [logIndicator_eq_colour_all, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    mul_comm (Real.exp t) 2]
  unfold carryLogColour etaUnitIntervalColour
  by_cases h : Even (⌊2 * Real.exp t⌋ : ℤ) <;> simp [hc, h]

private theorem exp_sub_log_two (s : ℂ) (t : ℝ) :
    Complex.exp (-s * ((t - Real.log 2 : ℝ) : ℂ)) =
      (2 : ℂ) ^ s * Complex.exp (-s * t) := by
  have hlog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), hlog, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem exp_mul_logIndicator_eq_indicator (s : ℂ) (t : ℝ) :
    Complex.exp (-s * t) * (pairedEtaLogIndicator t : ℂ) =
      pairedEtaLogSupport.indicator (fun t => Complex.exp (-s * t)) t := by
  by_cases ht : t ∈ pairedEtaLogSupport <;> simp [pairedEtaLogIndicator, ht]

/-- The actual quotient-colour transform is genuinely integrable on the
whole positive spectral half-plane, with no boundary term suppressed. -/
theorem integrable_exp_mul_carryLogColour {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * t) * (carryLogColour t : ℂ)) := by
  have heta : Integrable (fun t : ℝ => Complex.exp (-s * t) *
      (pairedEtaLogIndicator t : ℂ)) := by
    simp_rw [exp_mul_logIndicator_eq_indicator]
    exact (integrable_indicator_iff measurableSet_pairedEtaLogSupport).mpr
      (integrable_exp_neg_mul_pairedEtaLogMeasure hs)
  have hshift : Integrable (fun t : ℝ => Complex.exp (-s * ((t - Real.log 2 : ℝ) : ℂ)) *
      (pairedEtaLogIndicator t : ℂ)) := by
    simp_rw [exp_sub_log_two, mul_assoc]
    exact heta.const_mul _
  have h := hshift.comp_add_right (Real.log 2)
  simp only [add_sub_cancel_right] at h
  exact h.congr (carryLogColour_ae_eq_eta.mono (fun t ht => by
    dsimp only at ht ⊢
    rw [ht]))

/-- An exact logarithmic Mellin cell of the binary quotient colour. -/
def carryCellTransform (s : ℂ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (Real.log (2 * n + 1 : ℕ) - Real.log 2)..
    (Real.log (2 * n + 2 : ℕ) - Real.log 2), Complex.exp (-s * t)

/-- The complete carry transform is a sum of its actual logarithmic cells,
not the value of a guessed formal symbol. -/
def carryTransform (s : ℂ) : ℂ := ∑' n : ℕ, carryCellTransform s n

/-- Translation of the exact eta cells supplies the carry-cell transform. -/
theorem carryCellTransform_eq_eta (s : ℂ) (n : ℕ) :
    carryCellTransform s n = (2 : ℂ) ^ s * pairedEtaLaplaceInterval s n := by
  unfold carryCellTransform pairedEtaLaplaceInterval
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [← intervalIntegral.integral_comp_sub_right]
  simp_rw [exp_sub_log_two]
  exact intervalIntegral.integral_const_mul _ _

/-- The whole cell series is absolutely convergent in the positive
half-plane, as required for a genuine Mellin test of a power mode. -/
theorem summable_carryCellTransform {s : ℂ} (hs : 0 < s.re) :
    Summable (carryCellTransform s) := by
  exact ((summable_pairedEtaLaplaceInterval hs).mul_left ((2 : ℂ) ^ s)).congr
    (fun n => (carryCellTransform_eq_eta s n).symm)

/-- The exact full transform is the eta core with its scaling factor. -/
theorem carryTransform_eq_eta {s : ℂ} (hs : 0 < s.re) :
    carryTransform s = (2 : ℂ) ^ s * (pairedEtaCore s / s) := by
  unfold carryTransform
  simp_rw [carryCellTransform_eq_eta]
  rw [(summable_pairedEtaLaplaceInterval hs).tsum_mul_left]
  change (2 : ℂ) ^ s * pairedEtaLaplacePartition s = _
  rw [← integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hs,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div hs]

/-- The full cell series is exactly the integral of the literal floor
colour. The countable endpoint change is paid by its proved null measure. -/
theorem carryTransform_eq_actual_colour_integral {s : ℂ} (hs : 0 < s.re) :
    carryTransform s =
      ∫ t : ℝ, Complex.exp (-s * t) * (carryLogColour t : ℂ) := by
  rw [carryTransform_eq_eta hs]
  rw [integral_congr_ae (carryLogColour_ae_eq_eta.mono (fun t ht => by rw [ht]))]
  rw [← integral_sub_right_eq_self
    (fun t : ℝ => Complex.exp (-s * t) * (pairedEtaLogIndicator (t + Real.log 2) : ℂ))
    (Real.log 2)]
  simp only [sub_add_cancel]
  simp_rw [exp_sub_log_two, mul_assoc]
  rw [integral_const_mul]
  simp_rw [exp_mul_logIndicator_eq_indicator]
  rw [integral_indicator measurableSet_pairedEtaLogSupport]
  change (2 : ℂ) ^ s * (pairedEtaCore s / s) =
    (2 : ℂ) ^ s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_pairedEtaCore_div hs]

/-- Its zeta factor is exact throughout the positive half-plane away
from the removable pole parameter. This is the sensitivity preflight. -/
theorem carryTransform_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    carryTransform s = ((2 : ℂ) ^ s - 2) * riemannZeta s / s := by
  rw [carryTransform_eq_eta hs, pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1]
  have hi : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    simp
  calc
    _ = ((2 : ℂ) ^ s - 2 * ((2 : ℂ) ^ s * (2 : ℂ) ^ (-s))) * riemannZeta s / s := by
      ring
    _ = _ := by rw [hi]; ring

/-- A hypothetical actual zero has no leading carry power-mode response.
Thus the signed carry estimate cannot exclude it by this linear test. -/
theorem carryTransform_eq_zero_of_zeta_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) : carryTransform s = 0 := by
  rw [carryTransform_eq_zeta hs hs1, hzero, mul_zero, zero_div]

/-- The full logarithmic power mode is tested by the same exact carry
transform. Its scale is retained before evaluating any real part or norm. -/
theorem integrable_power_mode_carry_response {s : ℂ} (hs : 0 < s.re) (T : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (s * t) * (carryLogColour (T - t) : ℂ)) := by
  have h := ((integrable_exp_mul_carryLogColour hs).const_mul
    (Complex.exp (s * T))).comp_sub_left T
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  have he : Complex.exp (s * T) * Complex.exp (-s * ((T - t : ℝ) : ℂ)) =
      Complex.exp (s * t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only
  rw [← mul_assoc, he]

/-- This equality is between genuinely integrable full power-mode
responses; no formal symbol or nonintegrable Bochner zero is used. -/
theorem power_mode_carry_response {s : ℂ} (hs : 0 < s.re) (T : ℝ) :
    (∫ t : ℝ, Complex.exp (s * t) * (carryLogColour (T - t) : ℂ)) =
      Complex.exp (s * T) * carryTransform s := by
  have h := integral_sub_left_eq_self
    (fun t : ℝ => Complex.exp (s * ((T - t : ℝ) : ℂ)) * (carryLogColour t : ℂ)) volume T
  have hi (t : ℝ) : T - (T - t) = t := by ring
  simp_rw [hi] at h
  rw [h, carryTransform_eq_actual_colour_integral hs]
  have he (t : ℝ) : Complex.exp (s * ((T - t : ℝ) : ℂ)) =
      Complex.exp (s * T) * Complex.exp (-s * t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he, mul_assoc]
  exact integral_const_mul _ _

/-- If a genuine zero exists, its complete coherent power component is
annihilated at every scale by this linear arithmetic-carry test. -/
theorem power_mode_carry_response_eq_zero_of_zeta_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) (T : ℝ) :
    (∫ t : ℝ, Complex.exp (s * t) * (carryLogColour (T - t) : ℂ)) = 0 := by
  rw [power_mode_carry_response hs, carryTransform_eq_zero_of_zeta_zero hs hs1 hzero, mul_zero]

/-- Finite combinations of dilated carry tests retain the same blind
spot. This statement does not assume that an off-line zero exists. -/
theorem finite_scaled_carry_tests_eq_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) (S : Finset ℕ)
    (scale coefficient : ℕ → ℂ) :
    (∑ j ∈ S, coefficient j * scale j ^ s * carryTransform s) = 0 := by
  simp [carryTransform_eq_zero_of_zeta_zero hs hs1 hzero]

end
end RiemannGaussian.SuzukiIntegerCarryMellinAudit
