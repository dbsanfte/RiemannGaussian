import RiemannGaussian.EtaAlternatingReal
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Wallis constant of the actual eta overlap

The triangular period average has an explicit inverse-square integral.
Integrating consecutive ascending and descending cells leaves a telescoping
rational endpoint and the logarithm of a finite Wallis product.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal Interval Topology BigOperators

namespace RiemannGaussian

noncomputable section

/-- Integer shifts retain the alternating slope of the overlap profile. -/
theorem etaOverlapProfile_nat_add (n : ℕ) (x : ℝ) :
    etaOverlapProfile ((n : ℝ) + x) =
      if Even n then etaOverlapProfile x else 1 - etaOverlapProfile x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ) + x = ((n : ℝ) + x) + 1 by push_cast; ring,
        etaOverlapProfile_add_one, ih]
      by_cases hn : Even n <;> simp [Nat.even_add_one, hn]

/-- The exact affine overlap on each positive unit cell. -/
theorem etaOverlapProfile_eq_on_nat_cell {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    etaOverlapProfile x = if Even n then x - n else n + 1 - x := by
  have h : x - n ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [show x = (n : ℝ) + (x - n) by ring, etaOverlapProfile_nat_add, etaOverlapProfile_eq_self h]
  split_ifs <;> ring

/-- Elementary inverse-square integration of an affine cell profile. -/
theorem integral_affine_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c d : ℝ) :
    (∫ x in a..b, (c * x + d) / x ^ 2) =
      c * Real.log (b / a) + d * (a⁻¹ - b⁻¹) := by
  have hb : 0 < b := ha.trans_le hab
  have hnonzero (x : ℝ) (hx : x ∈ uIcc a b) : x ≠ 0 := by
    rw [uIcc_of_le hab] at hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hi : IntervalIntegrable (fun x : ℝ ↦ (c * x + d) / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuous_const.mul continuous_id).add continuous_const).continuousOn.div
      (continuous_id.pow 2).continuousOn (fun x hx ↦ pow_ne_zero _ (hnonzero x hx))
  have hderiv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ ↦ c * Real.log x - d / x) ((c * x + d) / x ^ 2) x := by
    convert ((Real.hasDerivAt_log (hnonzero x hx)).const_mul c).sub
      ((hasDerivAt_const x d).div (hasDerivAt_id x) (hnonzero x hx)) using 1 <;>
      first | rfl | (simp only [id_eq]; field_simp [hnonzero x hx]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi,
    Real.log_div hb.ne' ha.ne']
  ring

/-- The triangular profile divided by the squared coordinate is integrable
on every finite interval bounded away from zero. -/
theorem intervalIntegrable_etaOverlapProfile_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ ↦ etaOverlapProfile x / x ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuous_etaOverlapProfile.continuousOn.div (continuous_id.pow 2).continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact pow_ne_zero _ (ne_of_gt (ha.trans_le hx.1))

/-- Exact integration across one descending and one ascending eta cell. -/
theorem integral_etaOverlapProfile_div_sq_pair (n : ℕ) :
    (∫ x in (2 * (n : ℝ) + 1)..(2 * n + 3), etaOverlapProfile x / x ^ 2) =
      (2 * (n : ℝ) + 1)⁻¹ - (2 * (n : ℝ) + 3)⁻¹ -
        Real.log ((2 * n + 2) / (2 * n + 1) * ((2 * n + 2) / (2 * n + 3))) := by
  have hodd : (∫ x in (2 * (n : ℝ) + 1)..(2 * n + 2), etaOverlapProfile x / x ^ 2) =
      -Real.log ((2 * n + 2) / (2 * n + 1)) + (2 * n + 2) * ((2 * (n : ℝ) + 1)⁻¹ - (2 * (n : ℝ) + 2)⁻¹) := by
    calc
      _ = ∫ x in (2 * (n : ℝ) + 1)..(2 * n + 2), ((-1 : ℝ) * x + (2 * n + 2)) / x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        have hcell : x ∈ Icc (((2 * n + 1 : ℕ) : ℝ)) (((2 * n + 1 : ℕ) : ℝ) + 1) := by
          norm_num at hx ⊢
          constructor <;> linarith [hx.1, hx.2]
        dsimp only
        rw [etaOverlapProfile_eq_on_nat_cell hcell]
        norm_num
        congr 1
        ring
      _ = _ := by
        rw [integral_affine_div_sq (by positivity : 0 < 2 * (n : ℝ) + 1)
          (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * n + 2)]
        ring
  have heven : (∫ x in (2 * (n : ℝ) + 2)..(2 * n + 3), etaOverlapProfile x / x ^ 2) =
      Real.log ((2 * n + 3) / (2 * n + 2)) - (2 * n + 2) * ((2 * (n : ℝ) + 2)⁻¹ - (2 * (n : ℝ) + 3)⁻¹) := by
    calc
      _ = ∫ x in (2 * (n : ℝ) + 2)..(2 * n + 3), ((1 : ℝ) * x + -(2 * n + 2)) / x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith)] at hx
        have hcell : x ∈ Icc (((2 * n + 2 : ℕ) : ℝ)) (((2 * n + 2 : ℕ) : ℝ) + 1) := by
          norm_num at hx ⊢
          constructor <;> linarith [hx.1, hx.2]
        dsimp only
        rw [etaOverlapProfile_eq_on_nat_cell hcell]
        simp only [show Even (2 * n + 2) from (even_two_mul n).add (by decide), if_pos,
          Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, one_mul, sub_eq_add_neg]
      _ = _ := by
        rw [integral_affine_div_sq (by positivity : 0 < 2 * (n : ℝ) + 2)
          (by linarith : 2 * (n : ℝ) + 2 ≤ 2 * n + 3)]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_etaOverlapProfile_div_sq (by positivity : 0 < 2 * (n : ℝ) + 1) (by linarith))
    (intervalIntegrable_etaOverlapProfile_div_sq (by positivity : 0 < 2 * (n : ℝ) + 2) (by linarith)),
    hodd, heven,
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  field_simp
  ring

/-- The finite inverse-square integral is exactly a Wallis product and its
remaining rational endpoint. -/
theorem integral_etaOverlapProfile_div_sq_wallis (n : ℕ) :
    (∫ x in (1 : ℝ)..(2 * n + 1), etaOverlapProfile x / x ^ 2) =
      1 - (2 * (n : ℝ) + 1)⁻¹ - Real.log (Real.Wallis.W n) := by
  induction n with
  | zero => simp [Real.Wallis.W]
  | succ n ih =>
      rw [show 2 * ((n + 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 3 by push_cast; ring]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_etaOverlapProfile_div_sq zero_lt_one
          (by linarith [Nat.cast_nonneg (α := ℝ) n]))
        (intervalIntegrable_etaOverlapProfile_div_sq (by positivity : 0 < 2 * (n : ℝ) + 1)
          (by linarith : 2 * (n : ℝ) + 1 ≤ 2 * n + 3)),
        ih, integral_etaOverlapProfile_div_sq_pair, Real.Wallis.W_succ,
        Real.log_mul (Real.Wallis.W_pos n).ne' (by positivity)]
      ring

/-- The actual overlap profile has an integrable inverse-square tail at
every strictly positive lower endpoint. -/
theorem integrableOn_etaOverlapProfile_div_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ etaOverlapProfile x / x ^ 2) (Ioi a) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
  apply hi.mono' ((continuous_etaOverlapProfile.measurable.div
    (continuous_id.pow 2).measurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := ha.trans hx
  change ‖etaOverlapProfile x / x ^ 2‖ ≤ x ^ (-2 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (etaOverlapProfile_nonneg x) (sq_nonneg x)),
    Real.rpow_neg hxpos.le, Real.rpow_two, ← one_div]
  exact div_le_div_of_nonneg_right (etaOverlapProfile_le_one x) (sq_nonneg x)

/-- The Wallis constant is the exact infinite inverse-square tail of the
triangular eta overlap. -/
theorem integral_Ioi_etaOverlapProfile_div_sq :
    (∫ x in Ioi (1 : ℝ), etaOverlapProfile x / x ^ 2) = 1 - Real.log (Real.pi / 2) := by
  have ht : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hi := intervalIntegral_tendsto_integral_Ioi (1 : ℝ)
    (integrableOn_etaOverlapProfile_div_sq zero_lt_one) ht
  have hw : Tendsto (fun n : ℕ ↦ 1 - (2 * (n : ℝ) + 1)⁻¹ - Real.log (Real.Wallis.W n))
      atTop (𝓝 (1 - Real.log (Real.pi / 2))) := by
    simpa using (tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp ht)).sub
      ((Real.continuousAt_log (by positivity : Real.pi / 2 ≠ 0)).tendsto.comp
        Real.Wallis.tendsto_W_nhds_pi_div_two)
  simp_rw [integral_etaOverlapProfile_div_sq_wallis] at hi
  exact tendsto_nhds_unique hi hw

/-- Below the first corner the triangular overlap has an exact logarithmic
primitive. This is the term that cancels the finite arithmetic cutoff. -/
theorem integral_etaOverlapProfile_div_sq_to_one {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in a..1, etaOverlapProfile x / x ^ 2) = -Real.log a := by
  calc
    _ = ∫ x in a..1, ((1 : ℝ) * x + 0) / x ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha1] at hx
      dsimp only
      rw [etaOverlapProfile_eq_self ⟨ha.le.trans hx.1, hx.2⟩]
      simp
    _ = _ := by
      rw [integral_affine_div_sq ha ha1, Real.log_div one_ne_zero ha.ne']
      simp

/-- The exact averaged tail at every lower cutoff between zero and one. -/
theorem integral_Ioi_etaOverlapProfile_div_sq_of_le_one {a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in Ioi a, etaOverlapProfile x / x ^ 2) =
      1 - Real.log (Real.pi / 2) - Real.log a := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_etaOverlapProfile_div_sq ha) ha1
  rw [integral_Ioi_etaOverlapProfile_div_sq, integral_etaOverlapProfile_div_sq_to_one ha ha1] at h
  linarith

end

end RiemannGaussian
