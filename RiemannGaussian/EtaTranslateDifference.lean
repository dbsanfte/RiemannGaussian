import RiemannGaussian.EtaTranslatedResidual
import RiemannGaussian.EtaSupportGapGaussian

/-!
# Complete critical square distance between actual eta translates

The original support-mismatch theorem controls perturbations of the actual
translate grid. The complete half-line distance retains its exact initial
interval term and the original arithmetic mismatch. No finite tail is
discarded in the resulting logarithmic modulus.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The entire critical square distance between two actual eta colours. -/
def pairedEtaTranslateDifferenceEnergy (a b : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) *
    (pairedEtaTranslatedColour a t - pairedEtaTranslatedColour b t) ^ 2

/-- The actual two-colour square difference is bounded by one at every time. -/
theorem pairedEtaTranslatedColour_sub_sq_le_one (a b t : ℝ) :
    (pairedEtaTranslatedColour a t - pairedEtaTranslatedColour b t) ^ 2 ≤ 1 := by
  rcases pairedEtaTranslatedColour_eq_zero_or_one a t with ha | ha <;>
    rcases pairedEtaTranslatedColour_eq_zero_or_one b t with hb | hb <;> simp [ha, hb]

/-- The complete translated square difference is integrable on every right half-line. -/
theorem integrableOn_pairedEtaTranslateDifference (a b T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      (pairedEtaTranslatedColour a t - pairedEtaTranslatedColour b t) ^ 2) (Ioi T) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi T) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
  apply hi.mul_bdd (((measurable_pairedEtaTranslatedColour a).sub
    (measurable_pairedEtaTranslatedColour b)).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pairedEtaTranslatedColour_sub_sq_le_one a b t

/-- The full critical distance is nonnegative. -/
theorem pairedEtaTranslateDifferenceEnergy_nonneg (a b : ℝ) :
    0 ≤ pairedEtaTranslateDifferenceEnergy a b := integral_nonneg (fun _ ↦ by positivity)

/-- Interchanging the two actual translates preserves the full square distance. -/
theorem pairedEtaTranslateDifferenceEnergy_symm (a b : ℝ) :
    pairedEtaTranslateDifferenceEnergy a b = pairedEtaTranslateDifferenceEnergy b a := by
  unfold pairedEtaTranslateDifferenceEnergy
  congr 1
  ext t
  rw [sub_sq_comm]

/-- A common nonnegative delay retains the exact exponential factor in the complete critical distance. -/
theorem pairedEtaTranslateDifferenceEnergy_add {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    pairedEtaTranslateDifferenceEnergy a (a + r) =
      Real.exp (-a) * pairedEtaTranslateDifferenceEnergy 0 r := by
  let f := fun t : ℝ ↦ Real.exp (-t) *
    (pairedEtaTranslatedColour a t - pairedEtaTranslatedColour (a + r) t) ^ 2
  have hpre : (∫ t : ℝ in Ioc 0 a, f t) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have h₁ : pairedEtaTranslatedColour a t = 0 :=
      pairedEtaLogIndicator_eq_zero_of_nonpos (sub_nonpos.mpr ht.2)
    have h₂ : pairedEtaTranslatedColour (a + r) t = 0 :=
      pairedEtaLogIndicator_eq_zero_of_nonpos (sub_nonpos.mpr (by linarith [ht.2]))
    simp [f, h₁, h₂]
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_pairedEtaTranslateDifference a (a + r) 0)
    (integrableOn_pairedEtaTranslateDifference a (a + r) a)
  rw [intervalIntegral.integral_of_le ha, hpre, zero_add] at hsplit
  change (∫ t : ℝ in Ioi 0, f t) = _
  rw [← hsplit, integral_Ioi_eq_integral_add_left]
  have heq : (fun t : ℝ ↦ f (a + t)) = fun t : ℝ ↦ Real.exp (-a) *
      (Real.exp (-t) * (pairedEtaTranslatedColour 0 t - pairedEtaTranslatedColour r t) ^ 2) := by
    funext t
    simp [f, pairedEtaTranslatedColour, Real.exp_add]
    ring
  rw [heq, integral_const_mul]
  rfl

/-- The exact first-interval contribution and full arithmetic mismatch account for the entire translate distance. -/
theorem pairedEtaTranslateDifferenceEnergy_zero_eq {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ Real.log 2) :
    pairedEtaTranslateDifferenceEnergy 0 r =
      1 - Real.exp (-r) + Real.exp (-r) * pairedEtaMismatch (1 / 2) r := by
  let f := fun t : ℝ ↦ Real.exp (-t) *
    (pairedEtaTranslatedColour 0 t - pairedEtaTranslatedColour r t) ^ 2
  have hpre : (∫ t : ℝ in Ioc 0 r, f t) = 1 - Real.exp (-r) := by
    have hpoint : (∫ t : ℝ in Ioc 0 r, f t) = ∫ t : ℝ in Ioc 0 r, Real.exp (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have hcell : t ∈ pairedEtaLogCell 0 := by
        simpa [pairedEtaLogCell] using (show t ∈ Ioc 0 (Real.log 2) from ⟨ht.1, ht.2.trans hrL⟩)
      have h₁ : pairedEtaTranslatedColour 0 t = 1 := by
        simpa [pairedEtaTranslatedColour, pairedEtaLogCellColour] using pairedEtaLogIndicator_eq_cellColour hcell
      have h₂ : pairedEtaTranslatedColour r t = 0 :=
        pairedEtaLogIndicator_eq_zero_of_nonpos (sub_nonpos.mpr ht.2)
      simp [f, h₁, h₂]
    rw [hpoint, ← intervalIntegral.integral_of_le hr]
    have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
      simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    rw [← intervalIntegral.integral_Ioi_sub_Ioi hi hr]
    have hmass (T : ℝ) : (∫ t : ℝ in Ioi T, Real.exp (-t)) = Real.exp (-T) := by
      simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) T
    rw [hmass, hmass]
    simp
  have htail : (∫ t : ℝ in Ioi r, f t) = Real.exp (-r) * pairedEtaMismatch (1 / 2) r := by
    rw [integral_Ioi_eq_integral_add_left]
    have heq : (fun t : ℝ ↦ f (r + t)) = fun t : ℝ ↦
        Real.exp (-r) * (pairedEtaLogShiftMismatch r t * Real.exp (-t)) := by
      funext t
      simp [f, pairedEtaTranslatedColour, pairedEtaLogShiftMismatch, Real.exp_add, add_comm r t]
      ring
    rw [heq, integral_const_mul]
    congr 1
    simp [pairedEtaMismatch]
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_pairedEtaTranslateDifference 0 r 0)
    (integrableOn_pairedEtaTranslateDifference 0 r r)
  rw [intervalIntegral.integral_of_le hr, hpre, htail] at hsplit
  exact hsplit.symm

/-- Small nonnegative shifts have a complete logarithmic critical-square modulus, including the initial support interval. -/
theorem pairedEtaTranslateDifferenceEnergy_zero_le {r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 8) :
    pairedEtaTranslateDifferenceEnergy 0 r ≤ r * Real.log (1 / r) + 6 * r := by
  have hrL : r ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [pairedEtaTranslateDifferenceEnergy_zero_eq hr.le hrL]
  have hfirst : 1 - Real.exp (-r) ≤ r := by linarith [Real.add_one_le_exp (-r)]
  have he : Real.exp (-r) ≤ 1 := (Real.exp_le_one_iff).mpr (by linarith)
  have hM := (abs_le.mp (pairedEtaMismatch_critical_error_le hr hrsmall)).2
  have hmul := mul_le_of_le_one_left (pairedEtaMismatch_nonneg (1 / 2) r) he
  linarith

/-- A square-root envelope for the logarithmic modulus permits uniform control of a whole grid cell. -/
theorem pairedEtaTranslateDifferenceEnergy_zero_le_sqrt {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 8) :
    pairedEtaTranslateDifferenceEnergy 0 r ≤ 8 * Real.sqrt r := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [pairedEtaTranslateDifferenceEnergy]
  have hrone : r ≤ 1 := by linarith
  have hlog := Real.abs_log_mul_self_rpow_lt r (1 / 2) hrpos hrone (by norm_num)
  rw [← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (Real.sqrt_nonneg r)] at hlog
  norm_num only [one_div_div, div_one] at hlog
  have hm := mul_le_mul_of_nonneg_right hlog.le (Real.sqrt_nonneg r)
  rw [mul_assoc, Real.mul_self_sqrt hr] at hm
  have hlogbound : r * Real.log (1 / r) ≤ 2 * Real.sqrt r := by
    rw [one_div, Real.log_inv]
    exact (mul_le_mul_of_nonneg_left (neg_le_abs (Real.log r)) hr).trans
      (by simpa only [mul_comm r] using hm)
  have hroot : r ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r, mul_nonneg hr (sub_nonneg.mpr hrone)]
  exact (pairedEtaTranslateDifferenceEnergy_zero_le hrpos hrsmall).trans (by linarith)

/-- The complete square distance is uniformly small inside every short nonnegative translate cell. -/
theorem pairedEtaTranslateDifferenceEnergy_le_sqrt {a b r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hrsmall : r ≤ 1 / 8) (hab : |a - b| ≤ r) :
    pairedEtaTranslateDifferenceEnergy a b ≤ 8 * Real.sqrt r := by
  have hordered {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hgap : v - u ≤ r) :
      pairedEtaTranslateDifferenceEnergy u v ≤ 8 * Real.sqrt r := by
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv
    rw [show v = u + (v - u) by ring, pairedEtaTranslateDifferenceEnergy_add hu hd]
    have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ pairedEtaTranslateDifferenceEnergy 0 (v - u) :=
        mul_le_of_le_one_left (pairedEtaTranslateDifferenceEnergy_nonneg 0 _) he
      _ ≤ 8 * Real.sqrt (v - u) := pairedEtaTranslateDifferenceEnergy_zero_le_sqrt hd (hgap.trans hrsmall)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgap) (by norm_num)
  rcases le_total a b with h | h
  · apply hordered ha h
    simpa only [abs_of_nonpos (sub_nonpos.mpr h), neg_sub] using hab
  · rw [pairedEtaTranslateDifferenceEnergy_symm]
    apply hordered hb h
    simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using hab

end

end RiemannGaussian
