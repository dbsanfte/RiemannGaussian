/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnshiftedLogPayment
import RiemannGaussian.ZetaRieszShiftedZeroModes

/-!
# Summable horizontal-mode payment

The inverse-square distance weight is retained through the coupled Fourier
integral. It permits summation over genuine zeros, rather than replacing
the whole divisor by a fixed finite list. The right-edge resonance stays
outside this payment.
-/

namespace RiemannGaussian.ZetaRieszGlobalHorizontal
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszExposedModeCoupling ZetaRieszOrderedEulerBound
open ZetaRieszMarkedEuler ZetaRieszMarkedPrimeCompletion ZetaRieszMarkedLogDerivative

/-- The same rational effective radius as the existing coupled estimate. -/
abbrev modeRadius : ℝ := 1001/2000

/-- The inverse-node difference retains the true distance to the mode. -/
theorem inverse_difference_small {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    {xi : ℝ} (hxi : |xi| ≤ 1) :
    ‖(-z)⁻¹-(Complex.I*xi-z)⁻¹‖ ≤ 3*|xi|/‖z‖^2 := by
  have hr := horizontal_radius hz xi
  have hz0 : 0 < ‖z‖ := by linarith [hr.1]
  have ha0 : -z ≠ 0 := neg_ne_zero.mpr (norm_pos_iff.mp hz0)
  have hb0 : Complex.I*(xi : ℂ)-z ≠ 0 := norm_pos_iff.mp (by linarith [hr.2])
  have ht : ‖z‖ ≤ ‖Complex.I*(xi : ℂ)-z‖+|xi| := by
    have ht := norm_sub_le (Complex.I*(xi : ℂ)-z) (Complex.I*(xi : ℂ))
    simpa only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using ht
  have hb : ‖z‖ ≤ 3*‖Complex.I*(xi : ℂ)-z‖ := by linarith [hr.2]
  rw [inv_sub_inv ha0 hb0,norm_div,norm_mul,norm_neg,
    show Complex.I*(xi : ℂ)-z-(-z)=Complex.I*(xi : ℂ) by ring,
    norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_div_iff₀ (by positivity [norm_pos_iff.mpr hb0]) (by positivity [hr.1])).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg xi) (norm_nonneg z))]

/-- At small frequencies both the Fourier zero and the inverse-square
mode weight survive. -/
theorem modeDifference_small_weighted {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    {xi : ℝ} (hxi : |xi| ≤ 1) {j : ℕ} (hj : 0 < j) :
    ‖modeDifference z j xi‖ ≤ (3*|xi|/‖z‖^2)*modeRadius⁻¹^j := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hr := horizontal_radius hz xi
  have ha : ‖(-z)⁻¹‖ ≤ modeRadius⁻¹ := by
    rw [norm_inv,norm_neg]
    exact (inv_le_inv₀ (by linarith [hr.1]) (by norm_num)).mpr hr.1
  have hb : ‖(Complex.I*(xi : ℂ)-z)⁻¹‖ ≤ modeRadius⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (by linarith [hr.2]) (by norm_num)).mpr hr.2
  have h := (power_difference _ _ (by norm_num : 0 ≤ modeRadius⁻¹) ha hb k).trans
    (mul_le_mul_of_nonneg_left (inverse_difference_small hz hxi) (by positivity))
  unfold modeDifference
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) (k+1))).trans
  have hk : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    _ = (3*|xi|/‖z‖^2)*modeRadius⁻¹^k := by field_simp
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ modeRadius⁻¹) (by omega : k ≤ k+1))
        (by positivity)

/-- Two inverse powers are reserved for summing the entire zero divisor. -/
theorem inverse_power_weighted {a : ℂ} (ha : modeRadius ≤ ‖a‖)
    {j : ℕ} (hj : 2 ≤ j) :
    ‖a⁻¹‖^j ≤ modeRadius⁻¹^j/‖a‖^2 := by
  have ha0 : 0 < ‖a‖ := lt_of_lt_of_le (by norm_num : 0 < modeRadius) ha
  have hi : ‖a⁻¹‖ ≤ modeRadius⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ ha0 (by norm_num)).mpr ha
  have he : j = (j-2)+2 := by omega
  calc
    _ = ‖a⁻¹‖^(j-2)*‖a⁻¹‖^2 := by rw [← pow_add,← he]
    _ ≤ modeRadius⁻¹^(j-2)*‖a⁻¹‖^2 := by gcongr
    _ ≤ modeRadius⁻¹^j*‖a⁻¹‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ modeRadius⁻¹) (by omega : j-2 ≤ j))
        (sq_nonneg _)
    _ = _ := by simp only [norm_inv,inv_pow,div_eq_mul_inv]

/-- The large-frequency estimate retains a separate summable kernel
at the original and translated ordinates. -/
theorem modeDifference_large_weighted {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    ‖modeDifference z j xi‖ ≤ modeRadius⁻¹^j*(1/‖z‖^2+1/‖Complex.I*xi-z‖^2) := by
  have hr := horizontal_radius hz xi
  unfold modeDifference
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_self (norm_nonneg _) (by exact_mod_cast (show 1 ≤ j by omega))).trans
  apply (norm_sub_le _ _).trans
  simp only [norm_pow]
  exact (add_le_add
    (inverse_power_weighted (by simpa only [norm_neg] using hr.1) hj)
    (inverse_power_weighted hr.2 hj)).trans_eq (by simp only [norm_neg]; ring)

/-- The shifted Cauchy kernel has a uniform real majorant. -/
theorem shifted_inverse_square {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ)) (xi : ℝ) :
    1/‖Complex.I*xi-z‖^2 ≤ 4*(1+(xi-z.im)^2)⁻¹ := by
  have hsq : ‖Complex.I*(xi : ℂ)-z‖^2 = z.re^2+(xi-z.im)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have hp : 0 < ‖Complex.I*(xi : ℂ)-z‖^2 := by rw [hsq]; nlinarith [sq_nonneg (xi-z.im)]
  rw [show 4*(1+(xi-z.im)^2)⁻¹ = 4/(1+(xi-z.im)^2) by rw [div_eq_mul_inv]]
  apply (div_le_div_iff₀ hp (by positivity)).mpr
  rw [hsq]
  nlinarith [sq_nonneg (xi-z.im)]

/-- The distance weight is recovered even when the translated kernel
resonates at a distant ordinate. -/
theorem kernel_overlap {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    {xi : ℝ} (hxi : 1 ≤ |xi|) :
    (1/‖z‖^2+1/‖Complex.I*xi-z‖^2)/xi^2 ≤
      (8/‖z‖^2)*((1+xi^2)⁻¹+1/‖Complex.I*xi-z‖^2) := by
  have hr := horizontal_radius hz xi
  have hz0 : 0 < ‖z‖^2 := by positivity [hr.1]
  have hd0 : 0 < ‖Complex.I*(xi : ℂ)-z‖^2 := by positivity [hr.2]
  have hx : 1 ≤ xi^2 := by nlinarith [sq_abs xi]
  have hzn : ‖z‖ ≠ 0 := ne_of_gt (by linarith [hr.1])
  have hdn : ‖Complex.I*(xi : ℂ)-z‖ ≠ 0 := ne_of_gt (by linarith [hr.2])
  have hxn : xi ≠ 0 := by intro h; norm_num [h] at hxi
  have ht : ‖z‖ ≤ ‖Complex.I*(xi : ℂ)-z‖+|xi| := by
    have ht := norm_sub_le (Complex.I*(xi : ℂ)-z) (Complex.I*(xi : ℂ))
    simpa only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using ht
  have ht2 : ‖z‖^2 ≤ 2*‖Complex.I*(xi : ℂ)-z‖^2+2*xi^2 := by
    have hs := mul_self_le_mul_self (norm_nonneg z) ht
    nlinarith [sq_nonneg (‖Complex.I*(xi : ℂ)-z‖-|xi|),sq_abs xi]
  have hp : (‖Complex.I*(xi : ℂ)-z‖^2+‖z‖^2)*(1+xi^2) ≤
      8*xi^2*(‖Complex.I*(xi : ℂ)-z‖^2+1+xi^2) := by
    nlinarith [mul_le_mul_of_nonneg_right ht2 (show 0 ≤ 1+xi^2 by positivity),
      mul_nonneg (sub_nonneg.mpr hx) hd0.le]
  have hleft : (1/‖z‖^2+1/‖Complex.I*xi-z‖^2)/xi^2 =
      (‖Complex.I*xi-z‖^2+‖z‖^2)/(‖z‖^2*‖Complex.I*xi-z‖^2*xi^2) := by
    field_simp [hzn,hdn,hxn]
  have hright : (8/‖z‖^2)*((1+xi^2)⁻¹+1/‖Complex.I*xi-z‖^2) =
      (8*(‖Complex.I*xi-z‖^2+1+xi^2))/(‖z‖^2*‖Complex.I*xi-z‖^2*(1+xi^2)) := by
    field_simp [hzn,hdn,hxn]
    ring
  rw [hleft,hright]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  convert mul_le_mul_of_nonneg_left hp (mul_nonneg hz0.le hd0.le) using 1 <;> ring

/-- The original rectangle already excludes the two problematic marked
orders; no allocation is newly discarded. -/
theorem marked_order_two {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) : 2 ≤ j := by
  have hb := (Finset.mem_filter.mp hh).2
  omega

/-- Fixed small-frequency cost, independent of the chosen zero. -/
def smallCost : ℝ := 6*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)

/-- Fixed large-frequency cost, independent of the chosen zero. -/
def largeCost : ℝ := 4*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)

theorem smallCost_nonneg : 0 ≤ smallCost := by
  unfold smallCost
  positivity [logMass_nonneg (by norm_num [safeRadius] : (1 : ℝ) < 3/2-safeRadius)]

theorem largeCost_nonneg : 0 ≤ largeCost := by
  unfold largeCost
  positivity [mass_nonneg (3/2-safeRadius)]

/-- The original geometric joint-order budget, including the rectangle's
finite cardinality. -/
def orderBudget (N : ℕ) : ℝ := ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N

theorem orderBudget_nonneg (N : ℕ) : 0 ≤ orderBudget N := by unfold orderBudget; positivity

/-- The actual coupled symbol retains the mode-distance weight near
the Fourier origin. -/
theorem modeSymbol_small_weighted {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (hxi : |xi| ≤ 1) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*modeSymbol z A N y xi‖ ≤
      smallCost*orderBudget N*xi^2/‖z‖^2 := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r)) ≤
      |xi| *logMass (3/2-safeRadius) := by
    simp_rw [show ∀ r : ℕ, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r) =
      |xi| *(Real.log r*zetaPrimeExpWeight (3/2-safeRadius) r) from fun r => by ring]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_logMass_le A hs) (abs_nonneg xi)
  unfold modeSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := smallCost*(9999/10000 : ℝ)^N*xi^2/‖z‖^2)
    (by positivity [smallCost_nonneg]) ?_).trans_eq (by unfold orderBudget; ring)
  intro j hj h hh
  have hm := modeDifference_small_weighted hz hxi (marked_order_pos hh)
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi
    (fun p => |xi| *Real.log p) (fun p => mul_nonneg (abs_nonneg xi) (Real.log_natCast_nonneg p))
    (fun p => ZetaRieszMainFrequency.phase_le_log p xi)
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity [safeRadius_pos]))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*modeRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*
        (3*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)*xi^2/‖z‖^2) := by
      rw [← sq_abs xi]; ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*
        (3*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)*xi^2/‖z‖^2) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh)
        (by positivity [logMass_nonneg hs])
    _ = _ := by unfold smallCost; ring

/-- The full cofactor total order is retained in the large-frequency
estimate, including the translated inverse-square kernel. -/
theorem modeSymbol_large_weighted {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*modeSymbol z A N y xi‖ ≤
      largeCost*orderBudget N*(1/‖z‖^2+1/‖Complex.I*xi-z‖^2) := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      mass (3/2-safeRadius)*2 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num)
  unfold modeSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := largeCost*(9999/10000 : ℝ)^N*(1/‖z‖^2+1/‖Complex.I*xi-z‖^2))
    (by positivity [largeCost_nonneg]) ?_).trans_eq (by unfold orderBudget; ring)
  intro j hj h hh
  have hm := modeDifference_large_weighted hz xi (marked_order_two hh)
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi
    (fun _ => 2) (fun _ => by norm_num) (fun p => ZetaRieszMainFrequency.phase_le_two p xi)
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity [safeRadius_pos]))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*modeRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)*
          (1/‖z‖^2+1/‖Complex.I*xi-z‖^2)) := by ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)*
          (1/‖z‖^2+1/‖Complex.I*xi-z‖^2)) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh)
        (by positivity [mass_nonneg (3/2-safeRadius)])
    _ = _ := by unfold largeCost; ring

/-- A single translated Cauchy profile controls the two frequency
regimes with the inverse-square distance intact. -/
theorem scalar_profile {z v : ℂ} (hz : z.re ≤ -(501/1000 : ℝ)) (xi : ℝ)
    {S B : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hs : |xi| ≤ 1 → ‖v‖ ≤ S*xi^2/‖z‖^2)
    (hb : ‖v‖ ≤ B*(1/‖z‖^2+1/‖Complex.I*xi-z‖^2)) :
    ‖v/(xi : ℂ)^2‖ ≤ ((2*S+32*B)/‖z‖^2)*
      ((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by
  by_cases hx0 : xi = 0
  · simp only [hx0,Complex.ofReal_zero,zero_pow (by decide : 2 ≠ 0),div_zero,norm_zero]
    positivity
  have hx2 : 0 < xi^2 := sq_pos_of_ne_zero hx0
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  by_cases hx : |xi| ≤ 1
  · have hxq : xi^2 ≤ 1 := by nlinarith [sq_abs xi,abs_nonneg xi]
    have hh : 1 ≤ 2*(1+xi^2)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ (by positivity)).mpr (by linarith)
    apply (div_le_div_of_nonneg_right (hs hx) hx2.le).trans
    rw [show (S*xi^2/‖z‖^2)/xi^2 = S/‖z‖^2 by field_simp]
    calc
      _ = (S/‖z‖^2)*1 := by ring
      _ ≤ (2*S/‖z‖^2)*(1+xi^2)⁻¹ :=
        (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ S/‖z‖^2)).trans_eq (by ring)
      _ ≤ _ := by
        have hc : 2*S/‖z‖^2 ≤ (2*S+32*B)/‖z‖^2 :=
          div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
        have hp : (1+xi^2)⁻¹ ≤ (1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹ :=
          le_add_of_nonneg_right (by positivity)
        exact mul_le_mul hc hp (by positivity) (by positivity)
  · apply (div_le_div_of_nonneg_right hb hx2.le).trans
    calc
      _ = B*((1/‖z‖^2+1/‖Complex.I*xi-z‖^2)/xi^2) := by ring
      _ ≤ B*((8/‖z‖^2)*((1+xi^2)⁻¹+1/‖Complex.I*xi-z‖^2)) :=
        mul_le_mul_of_nonneg_left (kernel_overlap hz (le_of_not_ge hx)) hB
      _ ≤ B*((8/‖z‖^2)*((1+xi^2)⁻¹+4*(1+(xi-z.im)^2)⁻¹)) := by
        gcongr
        exact shifted_inverse_square hz xi
      _ ≤ (32*B/‖z‖^2)*((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by
        have hp : 0 ≤ (B/‖z‖^2)*(1+xi^2)⁻¹ := by positivity
        ring_nf at hp ⊢
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)) (by positivity)

/-- The distance-weighted frequency envelope, with both signs retained. -/
def distanceProfile (z : ℂ) (xi : ℝ) : ℝ :=
  (1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹+(1+(xi-(-z.im))^2)⁻¹

theorem distanceProfile_nonneg (z : ℂ) (xi : ℝ) : 0 ≤ distanceProfile z xi := by
  unfold distanceProfile
  positivity

theorem integrable_distanceProfile (z : ℂ) : Integrable (distanceProfile z) :=
  (integrable_inv_one_add_sq.add (integrable_inv_one_add_sq.comp_sub_right z.im)).add
    (integrable_inv_one_add_sq.comp_sub_right (-z.im))

/-- Translations of the Cauchy envelope have exactly the same total mass. -/
theorem integral_distanceProfile (z : ℂ) : ∫ xi : ℝ, distanceProfile z xi = 3*Real.pi := by
  have h01 : Integrable (fun xi : ℝ => (1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) :=
    integrable_inv_one_add_sq.add (integrable_inv_one_add_sq.comp_sub_right z.im)
  unfold distanceProfile
  rw [integral_add h01
    (integrable_inv_one_add_sq.comp_sub_right (-z.im)),
    integral_add integrable_inv_one_add_sq (integrable_inv_one_add_sq.comp_sub_right z.im),
    integral_sub_right_eq_self (fun x : ℝ => (1+x^2)⁻¹) z.im,
    integral_sub_right_eq_self (fun x : ℝ => (1+x^2)⁻¹) (-z.im),integral_univ_inv_one_add_sq]
  ring

/-- Constant for the entire paired, coupled frequency profile. -/
def kernelConstant : ℝ := 4*smallCost+64*largeCost

theorem kernelConstant_nonneg : 0 ≤ kernelConstant := by
  unfold kernelConstant
  positivity [smallCost_nonneg,largeCost_nonneg]

/-- The actual marked principal part now has an integrable envelope
whose total mass is summable over every genuine zero in the sector. -/
theorem modePair_weighted_profile {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(modePair z A N y L xi/(xi : ℂ)^2)‖ ≤
      (kernelConstant*orderBudget N/‖z‖^2)*distanceProfile z xi := by
  have hb (t : ℝ) : ‖(u : ℂ)^(N+1)*modeSymbol z A N y t/(t : ℂ)^2‖ ≤
      ((2*smallCost+32*largeCost)*orderBudget N/‖z‖^2)*
        ((1+t^2)⁻¹+(1+(t-z.im)^2)⁻¹) := by
    exact (scalar_profile hz t
      (mul_nonneg smallCost_nonneg (orderBudget_nonneg N))
      (mul_nonneg largeCost_nonneg (orderBudget_nonneg N))
      (fun ht => modeSymbol_small_weighted hz A h16 N y ht hu hU)
      (modeSymbol_large_weighted hz A h16 N y t hu hU)).trans_eq (by ring)
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*
      (Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*modeSymbol z A N y t)/(t : ℂ)^2‖ =
        ‖(u : ℂ)^(N+1)*modeSymbol z A N y t/(t : ℂ)^2‖ := by
    rw [mul_left_comm,mul_div_assoc,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  unfold modePair
  rw [← mul_div_assoc,mul_add,add_div]
  apply (norm_add_le _ _).trans
  have hm : ((-xi : ℝ) : ℂ)^2 = (xi : ℂ)^2 := by push_cast; ring
  rw [he,← hm,he]
  have hsum := add_le_add (hb xi) (hb (-xi))
  simp only [hm] at hsum ⊢
  apply hsum.trans
  simp only [neg_sq]
  have hsq : (-xi-z.im)^2 = (xi-(-z.im))^2 := by ring
  rw [hsq]
  unfold kernelConstant distanceProfile
  have hp : 0 ≤ ((2*smallCost+32*largeCost)*orderBudget N/‖z‖^2)*
      ((1+(xi-z.im)^2)⁻¹+(1+(xi-(-z.im))^2)⁻¹) := by
    positivity [smallCost_nonneg,largeCost_nonneg,orderBudget_nonneg N]
  ring_nf at hp ⊢
  linarith

/-- The full integral of the norm, not merely the norm of the integral,
has a summable inverse-square cost. This licenses the global exchange. -/
theorem integral_norm_modePair_bound {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (∫ xi : ℝ in Ioi 0, ‖(u : ℂ)^(N+1)*(modePair z A N y L xi/(xi : ℂ)^2)‖) ≤
      (3*Real.pi*kernelConstant)*orderBudget N/‖z‖^2 := by
  have h := integral_mono_ae (integrable_horizontal_pair hz A h16 N y L hu hU).norm
    ((integrable_distanceProfile z).integrableOn.const_mul (kernelConstant*orderBudget N/‖z‖^2))
    (Eventually.of_forall (fun xi => modePair_weighted_profile hz A h16 N y L xi hu hU))
  rw [integral_const_mul] at h
  have hp : (∫ xi : ℝ in Ioi 0, distanceProfile z xi) ≤ 3*Real.pi :=
    (setIntegral_le_integral (integrable_distanceProfile z)
      (Eventually.of_forall (distanceProfile_nonneg z))).trans_eq (integral_distanceProfile z)
  exact h.trans ((mul_le_mul_of_nonneg_left hp
    (by positivity [kernelConstant_nonneg,orderBudget_nonneg N])).trans_eq (by ring))

/-- The complete frequency integral costs the same fixed constant at
every mode ordinate. The distance weight carries the global zero count. -/
def responseConstant : ℝ := 3*Real.pi*kernelConstant

theorem responseConstant_nonneg : 0 ≤ responseConstant := by
  unfold responseConstant
  positivity [kernelConstant_nonneg]

/-- Quantitative payment for the actual Riesz response, with the new
inverse-square factor available before the divisor is summed. -/
theorem horizontalResponse_weighted_bound {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*horizontalResponse z A N y L‖ ≤
      responseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N/‖z‖^2 := by
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold horizontalResponse
  rw [mul_left_comm,← integral_const_mul,norm_mul]
  apply (mul_le_mul hpref ((norm_integral_le_integral_norm _).trans
    (integral_norm_modePair_bound hz A h16 N y L hu hU)) (norm_nonneg _) (by positivity)).trans
  calc
    _ ≤ ((N : ℝ)+2)*((3*Real.pi*kernelConstant)*orderBudget N/‖z‖^2) := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (by positivity [kernelConstant_nonneg,orderBudget_nonneg N])
    _ = _ := by unfold responseConstant orderBudget; ring

/-- Every mode is the coordinate of a genuine zero at the actual center. -/
def modeLocation (y : ℝ) (tau : NontrivialZetaZero) : ℂ := tau.1-(3/2+Complex.I*y)

theorem modeLocation_horizontal (y : ℝ) {tau : NontrivialZetaZero}
    (htau : tau.1.re ≤ (999/1000 : ℝ)) : (modeLocation y tau).re ≤ -(501/1000 : ℝ) := by
  simp only [modeLocation,Complex.sub_re]
  norm_num
  linarith

/-- The actual multiplicity-weighted distance budget. -/
def zeroWeight (y : ℝ) (tau : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity tau : ℝ)/‖modeLocation y tau‖^2

theorem zeroWeight_nonneg (y : ℝ) (tau : NontrivialZetaZero) : 0 ≤ zeroWeight y tau := by
  unfold zeroWeight
  positivity

/-- The complete zero divisor has a finite budget at every fixed height. -/
theorem summable_zeroWeight (y : ℝ) : Summable (zeroWeight y) := by
  change Summable (fun tau : NontrivialZetaZero =>
    (analyticZetaZeroMultiplicity tau : ℝ)/‖modeLocation y tau‖^2)
  simpa only [modeLocation,ZetaRieszShiftedCenter.center,norm_sub_rev] using
    ZetaRieszShiftedCenter.summable_center_inverse_square y

/-- A finite height-dependent constant, including all analytic multiplicities. -/
def zeroMass (y : ℝ) : ℝ := ∑' tau, zeroWeight y tau

theorem zeroMass_nonneg (y : ℝ) : 0 ≤ zeroMass y := tsum_nonneg (zeroWeight_nonneg y)

/-- The complete horizontally separated part of the genuine divisor,
inside the original paired symbol and factorial rectangle. -/
def globalPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
    (analyticZetaZeroMultiplicity tau : ℂ)*modePair (modeLocation y tau) A N y L xi else 0

/-- The full frequency integral of that actual global principal part. -/
def globalResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, globalPair A N y L xi/(xi : ℂ)^2

/-- The coupled zero series has summable full-frequency L1 norms. -/
theorem globalPair_L1 (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    let F := (fun tau : NontrivialZetaZero => fun xi : ℝ =>
      if tau.1.re ≤ (999/1000 : ℝ) then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*
          (modePair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0)
    (∀ tau, IntegrableOn (F tau) (Ioi 0)) ∧
      Summable (fun tau => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if tau.1.re ≤ (999/1000 : ℝ) then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (modePair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  have hi (tau : NontrivialZetaZero) : IntegrableOn (F tau) (Ioi 0) := by
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · simpa only [IntegrableOn,F,if_pos ht,mul_left_comm] using
        (integrable_horizontal_pair (modeLocation_horizontal y ht) A h16 N y L hu hU).const_mul
          (analyticZetaZeroMultiplicity tau : ℂ)
    · simp only [F,if_neg ht]
      exact integrableOn_zero
  have hn (tau : NontrivialZetaZero) :
      (∫ xi : ℝ in Ioi 0, ‖F tau xi‖) ≤
        (responseConstant*orderBudget N)*zeroWeight y tau := by
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · have he (xi : ℝ) : ‖F tau xi‖ = (analyticZetaZeroMultiplicity tau : ℝ)*
          ‖(u : ℂ)^(N+1)*(modePair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)‖ := by
        dsimp only [F]
        rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      simp_rw [he]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left
        (integral_norm_modePair_bound (modeLocation_horizontal y ht) A h16 N y L hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq
          (by unfold responseConstant zeroWeight; ring)
    · simp only [F,if_neg ht,norm_zero,integral_zero]
      positivity [responseConstant_nonneg,orderBudget_nonneg N,zeroWeight_nonneg y tau]
  have hsum : Summable (fun tau : NontrivialZetaZero => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) :=
    ((summable_zeroWeight y).mul_left (responseConstant*orderBudget N)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  exact ⟨hi,hsum⟩

/-- Absolute integrability of the coupled response licenses summing
the genuine zero divisor inside the Fourier integral. This is not an
inverse of a global infinite zero product. -/
theorem hasSum_globalResponse (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    HasSum (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        horizontalResponse (modeLocation y tau) A N y L) else 0)
      ((u : ℂ)^(N+1)*globalResponse A N y L) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if tau.1.re ≤ (999/1000 : ℝ) then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (modePair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  obtain ⟨hi,hsum⟩ := globalPair_L1 A h16 N y L hu hU
  have hs := (hasSum_integral_of_summable_integral_norm hi hsum).mul_left
    (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ)))
  have hs' : HasSum (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        horizontalResponse (modeLocation y tau) A N y L) else 0)
      (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0, ∑' tau, F tau xi) := by
    apply hs.congr_fun
    intro tau
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · simp only [if_pos ht,integral_const_mul,horizontalResponse]
      ring
    · simp only [if_neg ht,integral_zero,mul_zero]
  have he (xi : ℝ) : (∑' tau, F tau xi) =
      (u : ℂ)^(N+1)*(globalPair A N y L xi/(xi : ℂ)^2) := by
    rw [globalPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ) <;> simp [F,ht,mul_div_assoc]
  convert hs' using 1
  simp_rw [he,integral_const_mul]
  unfold globalResponse
  ring

/-- Summable L1 norms justify an actual complex series inside a real integral. -/
theorem integrable_complex_tsum {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℂ} {μ : Measure ℝ} (hi : ∀ i, Integrable (F i) μ)
    (hs : Summable (fun i => ∫ xi, ‖F i xi‖ ∂μ)) :
    Integrable (fun xi => ∑' i, F i xi) μ := by
  refine ⟨(AEMeasurable.tsum (fun i => (hi i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)]
  have he (i : ι) : ∫⁻ xi, ‖F i xi‖ₑ ∂μ = ‖∫ xi, ‖F i xi‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi i).norm,ENNReal.coe_nnreal_eq,coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun xi => norm_nonneg (F i xi)))]
    simp only [coe_nnnorm]
  simp_rw [he]
  exact (ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hs.abs).lt_top

/-- The global paired principal part is genuinely integrable, not an
arbitrary value assigned to a divergent integral. -/
theorem integrable_globalPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => globalPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  obtain ⟨hi,hs⟩ := globalPair_L1 A h16 N y L (u := 1/2) (by norm_num)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have h := integrable_complex_tsum hi hs
  have he (xi : ℝ) :
      (∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
        (((1/2 : ℝ) : ℂ)^(N+1))*((analyticZetaZeroMultiplicity tau : ℂ)*
          (modePair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0) =
      (((1/2 : ℝ) : ℂ)^(N+1))*(globalPair A N y L xi/(xi : ℂ)^2) := by
    rw [globalPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ) <;> simp [ht,mul_div_assoc]
  simp_rw [he] at h
  exact (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ)))
    (isUnit_iff_ne_zero.mpr (pow_ne_zero (N+1) (by norm_num : ((1/2 : ℝ) : ℂ) ≠ 0))) _).mp h

/-- The entire infinite horizontal zero sector has an explicit geometric
bound with its true multiplicity-weighted zero count already paid. -/
theorem globalResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {L u : ℝ} (hL : 1 ≤ L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*globalResponse A N y L‖ ≤
      (responseConstant*zeroMass y)*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have hs := hasSum_globalResponse A h16 N y L hu hU
  have hb (tau : NontrivialZetaZero) :
      ‖if tau.1.re ≤ (999/1000 : ℝ) then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*horizontalResponse (modeLocation y tau) A N y L) else 0‖ ≤
      (responseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N)*zeroWeight y tau := by
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left
        (horizontalResponse_weighted_bound (modeLocation_horizontal y ht) A h16 N y hL hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq (by unfold zeroWeight; ring)
    · simp only [if_neg ht,norm_zero]
      positivity [responseConstant_nonneg,zeroWeight_nonneg y tau]
  rw [← hs.tsum_eq]
  apply (norm_tsum_le_tsum_norm hs.summable.norm).trans
  apply (hs.summable.norm.tsum_le_tsum hb
    ((summable_zeroWeight y).mul_left (responseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))).trans_eq
  rw [tsum_mul_left]
  unfold zeroMass
  ring


/-- The global derivative identity uses genuine zero modes with their
actual multiplicities. Orders at least two are automatic on the marked
rectangle, not an extra allocation restriction. -/
theorem hasSum_xiDifference (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    HasSum (fun tau : NontrivialZetaZero => (analyticZetaZeroMultiplicity tau : ℂ)*
      modeDifference (modeLocation y tau) j xi)
      ((signedTaylorMoment (j-1) (logDeriv riemannXi) (3/2+Complex.I*y)-
        signedTaylorMoment (j-1) (logDeriv riemannXi) (3/2+Complex.I*y+Complex.I*xi))/(j : ℂ)) := by
  have h := ((ZetaRieszShiftedCenter.hasSum_global_zero_moment y (j-1) (by omega)).sub
    (ZetaRieszShiftedCenter.hasSum_global_zero_moment (y+xi) (j-1) (by omega))).div_const (j : ℂ)
  have he : ZetaRieszShiftedCenter.center (y+xi) = 3/2+Complex.I*y+Complex.I*xi := by
    unfold ZetaRieszShiftedCenter.center
    push_cast
    ring
  rw [he] at h
  apply h.congr_fun
  intro tau
  simp only [modeDifference,modeLocation,ZetaRieszShiftedCenter.center,
    show j-1+1=j by omega]
  rw [show -(tau.1-(3/2+Complex.I*(y : ℂ))) = 3/2+Complex.I*y-tau.1 by ring,
    show Complex.I*(xi : ℂ)-(tau.1-(3/2+Complex.I*y)) =
      3/2+Complex.I*y+Complex.I*xi-tau.1 by ring]
  ring

/-- Only the genuinely right-edge zero divisor is retained here. -/
def edgeDifference (y xi : ℝ) (j : ℕ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then 0 else
    (analyticZetaZeroMultiplicity tau : ℂ)*modeDifference (modeLocation y tau) j xi

/-- The complementary principal part whose full-axis integral is paid. -/
def horizontalDifference (y xi : ℝ) (j : ℕ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
    (analyticZetaZeroMultiplicity tau : ℂ)*modeDifference (modeLocation y tau) j xi else 0

theorem summable_horizontalDifference (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    Summable (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then
      (analyticZetaZeroMultiplicity tau : ℂ)*modeDifference (modeLocation y tau) j xi else 0) := by
  exact (hasSum_xiDifference y xi hj).summable.indicator {tau | tau.1.re ≤ (999/1000 : ℝ)}

/-- Exact signed global zero split, with no analytic remainder or
unaccounted infinite-divisor limit. -/
theorem xiDifference_split (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    (signedTaylorMoment (j-1) (logDeriv riemannXi) (3/2+Complex.I*y)-
      signedTaylorMoment (j-1) (logDeriv riemannXi) (3/2+Complex.I*y+Complex.I*xi))/(j : ℂ) =
        horizontalDifference y xi j+edgeDifference y xi j := by
  have hh := summable_horizontalDifference y xi hj
  have he : Summable (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then 0 else
      (analyticZetaZeroMultiplicity tau : ℂ)*modeDifference (modeLocation y tau) j xi) := by
    apply (hasSum_xiDifference y xi hj).summable.norm.of_norm_bounded
    intro tau
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · simp only [if_pos ht,norm_zero]
      exact norm_nonneg _
    · simp only [if_neg ht,le_refl]
  rw [horizontalDifference,edgeDifference,← hh.tsum_add he,← (hasSum_xiDifference y xi hj).tsum_eq]
  apply tsum_congr
  intro tau
  split_ifs <;> simp

/-- The sum over zero modes is exchanged only with the original finite
factorial rectangle, whose cofactor is retained exactly. -/
theorem hasSum_horizontalSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    HasSum (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then
      (analyticZetaZeroMultiplicity tau : ℂ)*modeSymbol (modeLocation y tau) A N y xi else 0)
      (∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        horizontalDifference y xi j*cofactor A N j h (3/2+Complex.I*y) xi) := by
  have hs := hasSum_sum (fun j (_hj : j ∈ Finset.range (N+2)) =>
    hasSum_sum (fun h (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) =>
      (summable_horizontalDifference y xi (marked_order_two hh)).hasSum.mul_right
        (cofactor A N j h (3/2+Complex.I*y) xi)))
  apply hs.congr_fun
  intro tau
  by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
  · simp only [if_pos ht,modeSymbol,Finset.mul_sum,mul_assoc]
  · simp only [if_neg ht,zero_mul,Finset.sum_const_zero]

/-- The surviving symbol contains the original pole and the unpaid
right-edge zero divisor. The Gamma correction is left explicit. -/
def retainedSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ZetaRieszCompletionPayment.completionSymbol A N (3/2+Complex.I*y) xi+
    ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
      (modeDifference (1-(3/2+Complex.I*y)) j xi-edgeDifference y xi j)*
        cofactor A N j h (3/2+Complex.I*y) xi

/-- The paid global zero sector has its genuine negative residue sign
in the logarithmic derivative. No source is silently removed. -/
theorem logSymbol_split (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    logSymbol A N (3/2+Complex.I*y) xi = retainedSymbol A N y xi-
      ∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
        (analyticZetaZeroMultiplicity tau : ℂ)*modeSymbol (modeLocation y tau) A N y xi else 0 := by
  rw [(hasSum_horizontalSymbol A N y xi).tsum_eq,retainedSymbol]
  have hs := ZetaRieszCompletionPayment.logSymbol_sub_completionSymbol A N
    (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re) xi
  have he : (∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
      (modeDifference (1-(3/2+Complex.I*y)) j xi-edgeDifference y xi j)*
        cofactor A N j h (3/2+Complex.I*y) xi) -
      (∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        horizontalDifference y xi j*cofactor A N j h (3/2+Complex.I*y) xi) =
      logSymbol A N (3/2+Complex.I*y) xi-
        ZetaRieszCompletionPayment.completionSymbol A N (3/2+Complex.I*y) xi := by
    rw [hs,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    rw [xiDifference_split y xi (marked_order_two hh)]
    ring
  linear_combination -he

/-- The global sum retains both original Fourier phases. -/
theorem globalPair_eq (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) :
    globalPair A N y L xi =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*
        (∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
          (analyticZetaZeroMultiplicity tau : ℂ)*modeSymbol (modeLocation y tau) A N y xi else 0)+
      Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*
        (∑' tau : NontrivialZetaZero, if tau.1.re ≤ (999/1000 : ℝ) then
          (analyticZetaZeroMultiplicity tau : ℂ)*modeSymbol (modeLocation y tau) A N y (-xi) else 0) := by
  have hs := ((hasSum_horizontalSymbol A N y xi).summable.hasSum.mul_left
    (Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I))).add
    ((hasSum_horizontalSymbol A N y (-xi)).summable.hasSum.mul_left
      (Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)))
  rw [globalPair,← hs.tsum_eq]
  apply tsum_congr
  intro tau
  by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
  · simp only [if_pos ht,modePair]; ring
  · simp only [if_neg ht,mul_zero,add_zero]

/-- The same integral, after the actual globally summable zero sector
is removed, with its original retained symbol. -/
theorem logResponse_add_globalResponse (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p) (y L : ℝ) :
    logResponse A N (3/2+Complex.I*y) L+globalResponse A N y L =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0,
          (Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*retainedSymbol A N y xi+
            Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*retainedSymbol A N y (-xi))/(xi : ℂ)^2 := by
  have hi := ZetaRieszUnshiftedLogPayment.integrable_logPair A hA h16 N hhead hgap y L
  have hg := integrable_globalPair A h16 N y L
  have he (xi : ℝ) : logPair A N (3/2+Complex.I*y) L xi+globalPair A N y L xi =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*retainedSymbol A N y xi+
        Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*retainedSymbol A N y (-xi) := by
    rw [logPair,logSymbol_split,logSymbol_split,globalPair_eq]
    ring
  unfold logResponse globalResponse
  rw [← mul_add,← integral_add hi hg]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro xi _hxi
  dsimp only
  rw [← add_div,he]

/-- The selected zero is strictly outside the paid global divisor. -/
theorem selected_not_horizontal (rho : NontrivialZetaZero)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ¬rho.1.re ≤ (999/1000 : ℝ) := by
  unfold ZetaRieszWideOwnerAudit.radiusCeiling at hU
  linarith

private theorem tendsto_cubic_rate :
    Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N) atTop (nhds 0) := by
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
  · ext N; simp only [pow_zero,pow_one]; ring
  · norm_num

/-- The entire zero sector is paid, including its shifted resonances at
arbitrarily large frequency. The height-dependent zero budget is fixed. -/
theorem tendsto_globalResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p) (y : ℝ) (L u : ℕ → ℝ)
    (hL : ∀ N, 1 ≤ L N) (hu : ∀ N, 0 ≤ u N)
    (hU : ∀ N, u N ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u N : ℂ)^(N+1)*globalResponse (A N) N y (L N))
      atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (responseConstant*zeroMass y)*
    (((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))
  · intro N
    simpa only [mul_assoc] using globalResponse_bound (A N) (h16 N) N y (hL N) (hu N) (hU N)
  · simpa only [mul_zero] using tendsto_cubic_rate.const_mul (responseConstant*zeroMass y)

/-- Subtract the actual negative global zero component from the literal
logarithmic-derivative main; all unpaid terms stay signed. -/
def reducedMain (u y : ℝ) (N : ℕ) : ℂ :=
  logMain u y N+globalResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
    (SquarefreeVaughanLogSource.length u N)

theorem logMain_reduced_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-reducedMain u y N)‖ ≤
      (responseConstant*zeroMass y)*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  simpa only [reducedMain,sub_add_cancel_left,mul_neg,norm_neg] using
    globalResponse_bound (ZetaRieszRoughEulerTransfer.roughPrimes u N)
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU

/-- The infinite-sector payment retains the unchanged literal packet,
its finite masks and every earlier paid error. This is not a whole-sum
floor, ceiling or zero exclusion. -/
theorem tendsto_reduced_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (reducedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have he := tendsto_globalResponse (fun N => ZetaRieszRoughEulerTransfer.roughPrimes u N)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) y
    (SquarefreeVaughanLogSource.length u) (fun _ => u)
    (ZetaRieszHeadOrders.one_le_length u) (fun _ => by linarith) (fun _ => hU)
  have h := (tendsto_log_sub_current hu hU y).add
    (he.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [add_zero] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def,reducedMain]
  ring


/-- Combine disjoint payments: all horizontal zero modes and the full
Gamma correction. Only the signed pole/right-edge response remains. -/
def poleEdgeMain (u y : ℝ) (N : ℕ) : ℂ :=
  reducedMain u y N-ZetaRieszCompletionPayment.completionResponse
    (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y (SquarefreeVaughanLogSource.length u N)

/-- A genuine geometric payment for both components of the original
signed main, with no exposed-zero or multiplicity assumption. -/
theorem logMain_poleEdge_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-poleEdgeMain u y N)‖ ≤
      (responseConstant*zeroMass y+Real.pi*(couplingConstant+couplingMassConstant))*
        ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  unfold poleEdgeMain
  rw [sub_sub_eq_add_sub,show logMain u y N+
      ZetaRieszCompletionPayment.completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N)-reducedMain u y N =
      (logMain u y N-reducedMain u y N)+
        ZetaRieszCompletionPayment.completionResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
          (SquarefreeVaughanLogSource.length u N) by ring,mul_add]
  apply (norm_add_le _ _).trans
  exact (add_le_add (logMain_reduced_bound hu hU y N)
    (ZetaRieszCompletionPayment.completionResponse_bound _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) hN y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU)).trans_eq (by ring)

/-- Terminal source ledger: the global-sector and Gamma payments leave
the original literal packet source unchanged. The retained pole/right-edge
expression still requires an independent signed floor and ceiling. -/
theorem tendsto_poleEdge_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (poleEdgeMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have hc := ZetaRieszCompletionPayment.tendsto_completionResponse
    (fun N => ZetaRieszRoughEulerTransfer.roughPrimes u N)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) (fun _ => y)
    (SquarefreeVaughanLogSource.length u) (fun _ => u)
    (ZetaRieszHeadOrders.one_le_length u) (fun _ => by linarith) (fun _ => hU)
  have he := (tendsto_reduced_sub_current hu hU y).sub
    (hc.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_zero] at he
  convert he using 1
  ext j
  dsimp only [Function.comp_def,poleEdgeMain]
  ring

end
end RiemannGaussian.ZetaRieszGlobalHorizontal
