/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszShiftedExterior

/-!
# The exact marked-order fraction pays a smaller shifted gap

The literal rectangle has `21*N <= 40*j`. Keeping this information changes
the sign of the coupled rate at radius `5001/10000`. The previous half-order
estimate does not decay there. The selected resonance remains unpaid.
-/

namespace RiemannGaussian.ZetaRieszSharpShifted
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszExposedModeCoupling ZetaRieszOrderedEulerBound
open ZetaRieszMarkedEuler ZetaRieszMarkedPrimeCompletion ZetaRieszMarkedLogDerivative
open ZetaRieszGlobalHorizontal ZetaRieszShiftedExterior

/-- This radius is below the earlier `1001/2000` denominator threshold. -/
def sharpRadius : ℝ := 5001/10000

theorem sharpRadius_pos : 0 < sharpRadius := by norm_num [sharpRadius]

/-- A rational geometric rate for the whole coupled factorial term. -/
def sharpRate : ℝ := 999999/1000000

theorem sharpRate_bounds : 0 < sharpRate ∧ sharpRate < 1 := by
  norm_num [sharpRate]

/-- An exact rational check using all forty parts of the marked order. -/
theorem sharp_rate_check :
    (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)^40*
      (safeRadius/sharpRadius)^21 ≤ sharpRate^40 := by
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius,sharpRadius,sharpRate]

/-- At this same radius the old half-order envelope genuinely grows.
This statement concerns the envelope, not the signed arithmetic response. -/
theorem half_order_rate_gt_one :
    1 < (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)^2*
      (safeRadius/sharpRadius) := by
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius,sharpRadius]

/-- The original marked and complementary orders are estimated together.
No prime range, low cofactor order, Fourier phase or rectangle is changed. -/
theorem sharp_order_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {N j h : ℕ} (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
    u^(N+1)*sharpRadius⁻¹^j*safeRadius⁻¹^(N+1-j) ≤
      2*sharpRate^N := by
  have hn : 21*N ≤ 40*j := (Finset.mem_filter.mp hh).2.2.1
  have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  let a : ℝ := ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius
  let b : ℝ := safeRadius/sharpRadius
  have ha0 : 0 ≤ a := by norm_num [a,ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius]
  have ha2 : a ≤ 2 := by norm_num [a,ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius]
  have hb0 : 0 ≤ b := by norm_num [b,safeRadius,sharpRadius]
  have hb1 : b ≤ 1 := by norm_num [b,safeRadius,sharpRadius]
  have hrate : a^40*b^21 ≤ sharpRate^40 := sharp_rate_check
  have hp : (a^(N+1)*b^j)^40 ≤ (a*sharpRate^N)^40 := by
    calc
      _ = a^40*(a^40)^N*b^(40*j) := by
        simp only [mul_pow,← pow_mul]
        rw [show (N+1)*40 = 40+40*N by omega,pow_add,Nat.mul_comm j 40]
      _ ≤ a^40*(a^40)^N*b^(21*N) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hb0 hb1 hn) (by positivity)
      _ = a^40*(a^40*b^21)^N := by
        simp only [mul_pow,← pow_mul]
        ring
      _ ≤ a^40*(sharpRate^40)^N := by gcongr
      _ = _ := by
        rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm 40 N]
  have hroot : a^(N+1)*b^j ≤ a*sharpRate^N := by
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity [sharpRate_bounds.1])
      (by decide : 40 ≠ 0)).mp hp
  have he : ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
      sharpRadius⁻¹^j*safeRadius⁻¹^(N+1-j) = a^(N+1)*b^j := by
    have hsum : j+(N+1-j)=N+1 := Nat.add_sub_of_le hjN
    have hpow := congrArg (fun n : ℕ => safeRadius^n) hsum
    rw [pow_add] at hpow
    dsimp [a,b]
    simp only [div_pow,inv_pow]
    field_simp [safeRadius_pos.ne']
    rw [← hpow]
    ring
  calc
    _ ≤ ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
        sharpRadius⁻¹^j*safeRadius⁻¹^(N+1-j) := by
      have hR := safeRadius_pos
      have hS : 0 < sharpRadius := by norm_num [sharpRadius]
      gcongr
    _ = a^(N+1)*b^j := he
    _ ≤ a*sharpRate^N := hroot
    _ ≤ 2*sharpRate^N := mul_le_mul_of_nonneg_right ha2 (pow_nonneg sharpRate_bounds.1.le _)

/-- Two inverse powers are reserved for summing the entire zero divisor. -/
theorem sharp_inverse_power_weighted {a : ℂ} (ha : sharpRadius ≤ ‖a‖)
    {j : ℕ} (hj : 2 ≤ j) :
    ‖a⁻¹‖^j ≤ sharpRadius⁻¹^j/‖a‖^2 := by
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num [sharpRadius] : 0 < sharpRadius) ha
  have hi : ‖a⁻¹‖ ≤ sharpRadius⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ ha0 (by norm_num [sharpRadius])).mpr ha
  have he : j = (j-2)+2 := by omega
  calc
    _ = ‖a⁻¹‖^(j-2)*‖a⁻¹‖^2 := by rw [← pow_add,← he]
    _ ≤ sharpRadius⁻¹^(j-2)*‖a⁻¹‖^2 := by gcongr
    _ ≤ sharpRadius⁻¹^j*‖a⁻¹‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num [sharpRadius] : (1 : ℝ) ≤ sharpRadius⁻¹) (by omega : j-2 ≤ j))
        (sq_nonneg _)
    _ = _ := by simp only [norm_inv,inv_pow,div_eq_mul_inv]

/-- The precise rectangle price, keeping the previous finite cardinality. -/
def sharpOrderBudget (N : ℕ) : ℝ := ((N : ℝ)+2)^2*sharpRate^N

theorem sharpOrderBudget_nonneg (N : ℕ) : 0 ≤ sharpOrderBudget N := by
  unfold sharpOrderBudget
  positivity [sharpRate_bounds.1]

/-- Only newly payable shifted terms are selected. The previous exterior
is explicitly excluded, so this payment is disjoint from the old one. -/
def Additional (z : ℂ) (xi : ℝ) : Prop :=
  (1/2000 : ℝ) ≤ |xi| ∧ sharpRadius ≤ ‖Complex.I*xi-z‖ ∧ ¬Exterior z xi

/-- The original shifted mark, with its summable mode weight retained. -/
theorem sharp_shiftedMark_bound {z : ℂ} {xi : ℝ}
    (he : sharpRadius ≤ ‖Complex.I*xi-z‖) {j : ℕ} (hj : 2 ≤ j) :
    ‖shiftedMark z j xi‖ ≤ sharpRadius⁻¹^j/‖Complex.I*xi-z‖^2 := by
  rw [shiftedMark,norm_div,Complex.norm_natCast]
  apply (div_le_self (norm_nonneg _) (by exact_mod_cast (show 1 ≤ j by omega))).trans
  rw [norm_pow]
  exact sharp_inverse_power_weighted he hj

/-- Projection selects a literal part of the previously retained symbol. -/
def additionalSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  if Additional z xi then shiftedSymbol z A N y xi else 0

/-- Both original Riesz phases use their own signed-frequency selection. -/
def additionalPair (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*additionalSymbol z A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*additionalSymbol z A N y (-xi)

/-- The original cofactor/order correlation supplies a geometric rate
on every retained exterior term, including right-edge modes. -/
theorem sharp_shiftedSymbol_bound {z : ℂ} (_hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (he : Additional z xi) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*shiftedSymbol z A N y xi‖ ≤
      largeCost*sharpOrderBudget N/‖Complex.I*xi-z‖^2 := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      2*mass (3/2-safeRadius) := by
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  unfold shiftedSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := largeCost*sharpRate^N/‖Complex.I*xi-z‖^2)
    (by positivity [largeCost_nonneg,sharpRate_bounds.1]) ?_).trans_eq (by unfold sharpOrderBudget; ring)
  intro j hj h hh
  have hm := sharp_shiftedMark_bound he.2.1 (marked_order_two hh)
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi
    (fun _ => 2) (fun _ => by norm_num) (fun p => ZetaRieszMainFrequency.phase_le_two p xi)
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity [safeRadius_pos]))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity [sharpRadius_pos]))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*sharpRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)/‖Complex.I*xi-z‖^2) := by ring
    _ ≤ (2*sharpRate^N)*
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)/‖Complex.I*xi-z‖^2) :=
      mul_le_mul_of_nonneg_right (sharp_order_bound hu hU hj hh)
        (by positivity [mass_nonneg (3/2-safeRadius)])
    _ = _ := by unfold largeCost; ring

/-- The full exterior symbol has a summable, distance-weighted frequency
profile. The central band is exactly zero in this isolated component. -/
theorem additionalSymbol_profile {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*additionalSymbol z A N y xi/(xi : ℂ)^2‖ ≤
      (8000010*largeCost*sharpOrderBudget N/‖z‖^2)*
        ((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by
  by_cases he : Additional z xi
  · rw [additionalSymbol,if_pos he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply (div_le_div_of_nonneg_right (sharp_shiftedSymbol_bound hz A h16 N y he hu hU) (sq_nonneg xi)).trans
    calc
      _ = (largeCost*sharpOrderBudget N)*(1/(‖Complex.I*xi-z‖^2*xi^2)) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (kernel_overlap_half hz he.1)
          (mul_nonneg largeCost_nonneg (sharpOrderBudget_nonneg N))
        exact h.trans_eq (by ring)
  · simp only [additionalSymbol,if_neg he,mul_zero,zero_div,norm_zero]
    positivity [largeCost_nonneg,sharpOrderBudget_nonneg N,sharpRate_bounds.1]

/-- Both phases are estimated only on their respective nonresonant
regions. The residual signed pair is not replaced by a Fourier norm. -/
theorem additionalPair_profile {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(additionalPair z A N y L xi/(xi : ℂ)^2)‖ ≤
      (exteriorConstant*sharpOrderBudget N/‖z‖^2)*distanceProfile z xi := by
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*
      (Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*additionalSymbol z A N y t)/(t : ℂ)^2‖ =
        ‖(u : ℂ)^(N+1)*additionalSymbol z A N y t/(t : ℂ)^2‖ := by
    rw [mul_left_comm,mul_div_assoc,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  unfold additionalPair
  rw [← mul_div_assoc,mul_add,add_div]
  apply (norm_add_le _ _).trans
  have hm : ((-xi : ℝ) : ℂ)^2 = (xi : ℂ)^2 := by push_cast; ring
  rw [he,← hm,he]
  have hsum := add_le_add (additionalSymbol_profile hz A h16 N y xi hu hU)
    (additionalSymbol_profile hz A h16 N y (-xi) hu hU)
  simp only [hm] at hsum ⊢
  apply hsum.trans
  simp only [neg_sq]
  rw [show (-xi-z.im)^2 = (xi-(-z.im))^2 by ring]
  unfold exteriorConstant distanceProfile
  have hp : 0 ≤ (8000010*largeCost*sharpOrderBudget N/‖z‖^2)*
      ((1+(xi-z.im)^2)⁻¹+(1+(xi-(-z.im))^2)⁻¹) := by
    positivity [largeCost_nonneg,sharpOrderBudget_nonneg N,sharpRate_bounds.1]
  ring_nf at hp ⊢
  linarith

theorem measurable_additionalSymbol (z : ℂ) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ) :
    Measurable (fun xi : ℝ => additionalSymbol z A N y xi) := by
  have hm : Measurable (fun xi : ℝ => shiftedSymbol z A N y xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Measurable.mul _ (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
    unfold shiftedMark
    fun_prop
  have hE : MeasurableSet {xi : ℝ | Additional z xi} := by
    apply MeasurableSet.inter
    · exact (isClosed_le continuous_const continuous_abs).measurableSet
    · apply MeasurableSet.inter
      · exact (isClosed_le continuous_const
          (show Continuous (fun xi : ℝ => ‖Complex.I*xi-z‖) by fun_prop)).measurableSet
      · apply MeasurableSet.compl
        exact ((isClosed_le continuous_const continuous_abs).measurableSet.inter
          (isClosed_le continuous_const (continuous_id.sub continuous_const).abs).measurableSet)
  exact hm.ite hE measurable_const

theorem measurable_additionalPair (z : ℂ) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => additionalPair z A N y L xi/(xi : ℂ)^2) := by
  have hm := measurable_additionalSymbol z A h16 N y
  have hn := hm.comp measurable_neg
  unfold additionalPair
  fun_prop

/-- The hard exterior projection has an ordinary absolutely integrable
response. There is no boundary completion error. -/
theorem integrable_additionalPair {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(additionalPair z A N y L xi/(xi : ℂ)^2)) (Ioi 0) := by
  apply ((integrable_distanceProfile z).integrableOn.const_mul
    (exteriorConstant*sharpOrderBudget N/‖z‖^2)).mono'
  · exact ((measurable_additionalPair z A h16 N y L).const_mul _).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => additionalPair_profile hz A h16 N y L xi hu hU)

/-- An L1 estimate strong enough to sum every genuine zero before
performing the original frequency integral. -/
theorem integral_norm_additionalPair_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (∫ xi : ℝ in Ioi 0, ‖(u : ℂ)^(N+1)*(additionalPair z A N y L xi/(xi : ℂ)^2)‖) ≤
      (3*Real.pi*exteriorConstant)*sharpOrderBudget N/‖z‖^2 := by
  have h := integral_mono_ae (integrable_additionalPair hz A h16 N y L hu hU).norm
    ((integrable_distanceProfile z).integrableOn.const_mul (exteriorConstant*sharpOrderBudget N/‖z‖^2))
    (Eventually.of_forall (fun xi => additionalPair_profile hz A h16 N y L xi hu hU))
  rw [integral_const_mul] at h
  have hp : (∫ xi : ℝ in Ioi 0, distanceProfile z xi) ≤ 3*Real.pi :=
    (setIntegral_le_integral (integrable_distanceProfile z)
      (Eventually.of_forall (distanceProfile_nonneg z))).trans_eq (integral_distanceProfile z)
  exact h.trans ((mul_le_mul_of_nonneg_left hp
    (by positivity [exteriorConstant_nonneg,sharpOrderBudget_nonneg N])).trans_eq (by ring))

/-- The exterior part of one genuine shifted principal part. -/
def additionalResponse (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, additionalPair z A N y L xi/(xi : ℂ)^2

/-- A genuine geometric payment for a shifted pole or zero mode outside
its resonance, with the original factorial weights still coupled. -/
theorem additionalResponse_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*additionalResponse z A N y L‖ ≤
      exteriorResponseConstant*((N : ℝ)+2)^3*sharpRate^N/‖z‖^2 := by
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold additionalResponse
  rw [mul_left_comm,← integral_const_mul,norm_mul]
  apply (mul_le_mul hpref ((norm_integral_le_integral_norm _).trans
    (integral_norm_additionalPair_bound hz A h16 N y L hu hU)) (norm_nonneg _) (by positivity)).trans
  calc
    _ ≤ ((N : ℝ)+2)*((3*Real.pi*exteriorConstant)*sharpOrderBudget N/‖z‖^2) := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (by positivity [exteriorConstant_nonneg,sharpOrderBudget_nonneg N])
    _ = _ := by unfold exteriorResponseConstant sharpOrderBudget; ring

/-- The nonresonant shifted right-edge part of the genuine divisor,
inside the original paired symbol and factorial rectangle. -/
def edgeAdditionalPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
    (analyticZetaZeroMultiplicity tau : ℂ)*additionalPair (modeLocation y tau) A N y L xi else 0

/-- The full frequency integral of that actual global principal part. -/
def edgeAdditionalResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, edgeAdditionalPair A N y L xi/(xi : ℂ)^2

/-- The coupled zero series has summable full-frequency L1 norms. -/
theorem edgeAdditionalPair_L1 (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    let F := (fun tau : NontrivialZetaZero => fun xi : ℝ =>
      if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*
          (additionalPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0)
    (∀ tau, IntegrableOn (F tau) (Ioi 0)) ∧
      Summable (fun tau => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (additionalPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  have hi (tau : NontrivialZetaZero) : IntegrableOn (F tau) (Ioi 0) := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · simpa only [IntegrableOn,F,if_pos ht,mul_left_comm] using
        (integrable_additionalPair (modeLocation_half y tau) A h16 N y L hu hU).const_mul
          (analyticZetaZeroMultiplicity tau : ℂ)
    · simp only [F,if_neg ht]
      exact integrableOn_zero
  have hn (tau : NontrivialZetaZero) :
      (∫ xi : ℝ in Ioi 0, ‖F tau xi‖) ≤
        (exteriorResponseConstant*sharpOrderBudget N)*zeroWeight y tau := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · have he (xi : ℝ) : ‖F tau xi‖ = (analyticZetaZeroMultiplicity tau : ℝ)*
          ‖(u : ℂ)^(N+1)*(additionalPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)‖ := by
        dsimp only [F]
        rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      simp_rw [he]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left
        (integral_norm_additionalPair_bound (modeLocation_half y tau) A h16 N y L hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq
          (by unfold exteriorResponseConstant zeroWeight; ring)
    · simp only [F,if_neg ht,norm_zero,integral_zero]
      positivity [exteriorResponseConstant_nonneg,sharpOrderBudget_nonneg N,zeroWeight_nonneg y tau]
  have hsum : Summable (fun tau : NontrivialZetaZero => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) :=
    ((summable_zeroWeight y).mul_left (exteriorResponseConstant*sharpOrderBudget N)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  exact ⟨hi,hsum⟩

/-- Absolute integrability of the coupled response licenses summing
the genuine zero divisor inside the Fourier integral. This is not an
inverse of a global infinite zero product. -/
theorem hasSum_edgeAdditionalResponse (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    HasSum (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        additionalResponse (modeLocation y tau) A N y L) else 0)
      ((u : ℂ)^(N+1)*edgeAdditionalResponse A N y L) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (additionalPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  obtain ⟨hi,hsum⟩ := edgeAdditionalPair_L1 A h16 N y L hu hU
  have hs := (hasSum_integral_of_summable_integral_norm hi hsum).mul_left
    (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ)))
  have hs' : HasSum (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        additionalResponse (modeLocation y tau) A N y L) else 0)
      (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0, ∑' tau, F tau xi) := by
    apply hs.congr_fun
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · simp only [if_pos ht,integral_const_mul,additionalResponse]
      ring
    · simp only [if_neg ht,integral_zero,mul_zero]
  have he (xi : ℝ) : (∑' tau, F tau xi) =
      (u : ℂ)^(N+1)*(edgeAdditionalPair A N y L xi/(xi : ℂ)^2) := by
    rw [edgeAdditionalPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re <;> simp [F,ht,mul_div_assoc]
  convert hs' using 1
  simp_rw [he,integral_const_mul]
  unfold edgeAdditionalResponse
  ring

/-- The global paired principal part is genuinely integrable, not an
arbitrary value assigned to a divergent integral. -/
theorem integrable_edgeAdditionalPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => edgeAdditionalPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  obtain ⟨hi,hs⟩ := edgeAdditionalPair_L1 A h16 N y L (u := 1/2) (by norm_num)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have h := integrable_complex_tsum hi hs
  have he (xi : ℝ) :
      (∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
        (((1/2 : ℝ) : ℂ)^(N+1))*((analyticZetaZeroMultiplicity tau : ℂ)*
          (additionalPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0) =
      (((1/2 : ℝ) : ℂ)^(N+1))*(edgeAdditionalPair A N y L xi/(xi : ℂ)^2) := by
    rw [edgeAdditionalPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re <;> simp [ht,mul_div_assoc]
  simp_rw [he] at h
  exact (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ)))
    (isUnit_iff_ne_zero.mpr (pow_ne_zero (N+1) (by norm_num : ((1/2 : ℝ) : ℂ) ≠ 0))) _).mp h

/-- The entire right-edge exterior zero sector has an explicit geometric
bound with its true multiplicity-weighted zero count already paid. -/
theorem edgeAdditionalResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {L u : ℝ} (hL : 1 ≤ L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*edgeAdditionalResponse A N y L‖ ≤
      (exteriorResponseConstant*zeroMass y)*((N : ℝ)+2)^3*sharpRate^N := by
  have hs := hasSum_edgeAdditionalResponse A h16 N y L hu hU
  have hb (tau : NontrivialZetaZero) :
      ‖if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*additionalResponse (modeLocation y tau) A N y L) else 0‖ ≤
      (exteriorResponseConstant*((N : ℝ)+2)^3*sharpRate^N)*zeroWeight y tau := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left
        (additionalResponse_bound (modeLocation_half y tau) A h16 N y hL hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq (by unfold zeroWeight; ring)
    · simp only [if_neg ht,norm_zero]
      positivity [exteriorResponseConstant_nonneg,zeroWeight_nonneg y tau,sharpRate_bounds.1]
  rw [← hs.tsum_eq]
  apply (norm_tsum_le_tsum_norm hs.summable.norm).trans
  apply (hs.summable.norm.tsum_le_tsum hb
    ((summable_zeroWeight y).mul_left (exteriorResponseConstant*((N : ℝ)+2)^3*sharpRate^N))).trans_eq
  rw [tsum_mul_left]
  unfold zeroMass
  ring




/-- A point cannot be charged to both the old exterior and this new payment. -/
theorem additional_disjoint {z : ℂ} {xi : ℝ} (h : Additional z xi) : ¬Exterior z xi := h.2.2

/-- The remaining principal part retains its sign and its unshifted term. -/
def sharpDifference (z : ℂ) (j : ℕ) (xi : ℝ) : ℂ :=
  retainedDifference z j xi+(if Additional z xi then shiftedMark z j xi else 0)

/-- The newly paid term is literally part of the previous retained mark. -/
theorem sharpDifference_eq (z : ℂ) (j : ℕ) (xi : ℝ) :
    sharpDifference z j xi = shiftedMark z j 0-
      (if Exterior z xi ∨ Additional z xi then 0 else shiftedMark z j xi) := by
  by_cases he : Exterior z xi
  · have ha : ¬Additional z xi := fun h => additional_disjoint h he
    simp [sharpDifference,retainedDifference,he,ha]
  · by_cases ha : Additional z xi <;>
      simp [sharpDifference,retainedDifference,he,ha]

/-- Only a small shifted denominator or the untouched central band can
remain. This is not a support claim for the unshifted term. -/
theorem sharp_shift_support {z : ℂ} {j : ℕ} {xi : ℝ}
    (h : sharpDifference z j xi ≠ shiftedMark z j 0) :
    |xi| < (1/2000 : ℝ) ∨ ‖Complex.I*xi-z‖ < sharpRadius := by
  by_contra hn
  have hx : (1/2000 : ℝ) ≤ |xi| := not_lt.mp (not_or.mp hn).1
  have hr : sharpRadius ≤ ‖Complex.I*xi-z‖ := not_lt.mp (not_or.mp hn).2
  have he : Exterior z xi ∨ Additional z xi := by
    by_cases he : Exterior z xi
    · exact Or.inl he
    · exact Or.inr ⟨hx,hr,he⟩
  exact h (by rw [sharpDifference_eq,if_pos he,sub_zero])

/-- Outside the central band, the remaining shifted zero must have
real part greater than 0.9999 and lie in a narrower ordinate interval. -/
theorem sharp_shift_geometry {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) {j : ℕ} {xi : ℝ}
    (h : sharpDifference z j xi ≠ shiftedMark z j 0) :
    |xi| < (1/2000 : ℝ) ∨
      (-(5001/10000 : ℝ) < z.re ∧ |xi-z.im| < (101/10000 : ℝ)) := by
  rcases sharp_shift_support h with hx | hr
  · exact Or.inl hx
  right
  have hsq : ‖Complex.I*(xi : ℂ)-z‖^2 = z.re^2+(xi-z.im)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have hre := Complex.abs_re_le_norm (Complex.I*(xi : ℂ)-z)
  have he : (Complex.I*(xi : ℂ)-z).re = -z.re := by simp
  rw [he,abs_of_nonneg (by linarith)] at hre
  have hr0 := norm_nonneg (Complex.I*(xi : ℂ)-z)
  norm_num only [sharpRadius] at hr
  refine ⟨by linarith,?_⟩
  nlinarith [sq_abs (xi-z.im),abs_nonneg (xi-z.im)]

/-- A genuine extra slice: the old vertical exclusion fails here,
while the exact rectangle rate applies. No existence of such a zero is asserted. -/
theorem additional_nonempty_example :
    Additional (-(5001/10000 : ℂ)) (1/1000) := by
  have hs : sharpRadius ≤ ‖Complex.I*((1/1000 : ℝ) : ℂ)-(-(5001/10000 : ℂ))‖ := by
    have h := Complex.abs_re_le_norm
      (Complex.I*((1/1000 : ℝ) : ℂ)-(-(5001/10000 : ℂ)))
    norm_num [sharpRadius] at h ⊢
    exact h
  refine ⟨by norm_num,hs,?_⟩
  norm_num [Exterior]

/-- The selected center is never included in either norm payment. -/
theorem selected_center_retained (u : ℝ) :
    ¬Exterior (-(u : ℂ)) 0 ∧ ¬Additional (-(u : ℂ)) 0 := by
  norm_num [Exterior,Additional]

/-- Subtract only the disjoint newly controlled shifted terms from the
existing signed pole/right-edge response. -/
def sharpMain (u y : ℝ) (N : ℕ) : ℂ :=
  resonantMain u y N+
    additionalResponse (poleLocation y) (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)-
    edgeAdditionalResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)

/-- This is the cost of an actual change to the retained signed main,
with the original rough prime support and moving physical length. -/
theorem resonant_sharp_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(sharpMain u y N-resonantMain u y N)‖ ≤
      paymentConstant y*((N : ℝ)+2)^3*sharpRate^N := by
  have he : sharpMain u y N-resonantMain u y N =
      additionalResponse (poleLocation y) (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N)-
      edgeAdditionalResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N) := by unfold sharpMain; ring
  rw [he,mul_sub]
  apply (norm_sub_le _ _).trans
  exact (add_le_add
    (additionalResponse_bound (poleLocation_half y) _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU)
    (edgeAdditionalResponse_bound _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU)).trans_eq (by unfold paymentConstant; ring)

/-- Both signed comparisons improve on the whole sum, with an arbitrary
unchanged complement. No independent bound for either remainder is assumed. -/
theorem joint_sharp_bounds {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) (rest : ℂ) :
    ((u : ℂ)^(N+1)*(sharpMain u y N+rest)).re-
        paymentConstant y*((N : ℝ)+2)^3*sharpRate^N ≤
      ((u : ℂ)^(N+1)*(resonantMain u y N+rest)).re ∧
    ((u : ℂ)^(N+1)*(resonantMain u y N+rest)).re ≤
      ((u : ℂ)^(N+1)*(sharpMain u y N+rest)).re+
        paymentConstant y*((N : ℝ)+2)^3*sharpRate^N := by
  have h := (Complex.abs_re_le_norm _).trans (resonant_sharp_bound hu hU y N)
  have he : ((u : ℂ)^(N+1)*(sharpMain u y N-resonantMain u y N)).re =
      ((u : ℂ)^(N+1)*(sharpMain u y N+rest)).re-
        ((u : ℂ)^(N+1)*(resonantMain u y N+rest)).re := by
    rw [← Complex.sub_re]
    congr 1
    ring
  rw [he] at h
  exact ⟨by linarith [(abs_le.mp h).2],by linarith [(abs_le.mp h).1]⟩

private theorem tendsto_sharp_cubic_rate :
    Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*sharpRate^N) atTop (nhds 0) := by
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 sharpRate_bounds.1.le sharpRate_bounds.2
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 sharpRate_bounds.1.le sharpRate_bounds.2
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 sharpRate_bounds.1.le sharpRate_bounds.2
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 sharpRate_bounds.1.le sharpRate_bounds.2
  convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
  · ext N; simp only [pow_zero,pow_one]; ring
  · norm_num

/-- The literal packet retains its source after the new exterior
payments. This theorem does not bound the surviving signed resonances. -/
theorem tendsto_sharp_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (sharpMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have he : Tendsto (fun N => (u : ℂ)^(N+1)*
      (sharpMain u y N-resonantMain u y N)) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => paymentConstant y*(((N : ℝ)+2)^3*sharpRate^N))
    · intro N
      simpa only [mul_assoc] using resonant_sharp_bound (by linarith : 0 ≤ u) hU y N
    · simpa only [mul_zero] using tendsto_sharp_cubic_rate.const_mul (paymentConstant y)
  have h := (ZetaRieszShiftedExterior.tendsto_resonant_sub_current hu hU y).add
    (he.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [add_zero] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def]
  ring


/-- Earlier payments remain available at their stronger rates. Combining
them with this disjoint extra slice gives one vanishing current-main error. -/
theorem logMain_sharp_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-sharpMain u y N)‖ ≤
      (ZetaRieszGlobalHorizontal.responseConstant*zeroMass y+
        Real.pi*(couplingConstant+couplingMassConstant)+2*paymentConstant y)*
        ((N : ℝ)+2)^3*sharpRate^N := by
  have he : logMain u y N-sharpMain u y N =
      (logMain u y N-resonantMain u y N)-(sharpMain u y N-resonantMain u y N) := by ring
  rw [he,mul_sub]
  apply (norm_sub_le _ _).trans
  have h0 := logMain_resonant_bound hu hU y hN
  have h1 := resonant_sharp_bound hu hU y N
  have hq : (9999/10000 : ℝ)^N ≤ sharpRate^N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num [sharpRate]) _
  have hP : 0 ≤ paymentConstant y := by
    unfold paymentConstant
    positivity [exteriorResponseConstant_nonneg,zeroMass_nonneg y]
  have hc : 0 ≤ (ZetaRieszGlobalHorizontal.responseConstant*zeroMass y+
      Real.pi*(couplingConstant+couplingMassConstant)+paymentConstant y)*((N : ℝ)+2)^3 := by
    positivity [ZetaRieszGlobalHorizontal.responseConstant_nonneg,zeroMass_nonneg y,
      couplingConstant_nonneg,couplingMassConstant_nonneg]
  exact (add_le_add (h0.trans (mul_le_mul_of_nonneg_left hq hc)) h1).trans_eq (by ring)

end
end RiemannGaussian.ZetaRieszSharpShifted
