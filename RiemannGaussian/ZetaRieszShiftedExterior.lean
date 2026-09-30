/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGlobalHorizontal

/-!
# Geometric payment outside the actual shifted resonances

The signed pole/right-edge response keeps its central Fourier band and
all mode-relative resonance intervals. Only the complementary shifted
terms are estimated, with their original cofactor and factorial rectangle.
The mode-distance weight makes the estimate summable over genuine zeros.
-/

namespace RiemannGaussian.ZetaRieszShiftedExterior
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszExposedModeCoupling ZetaRieszOrderedEulerBound
open ZetaRieszMarkedEuler ZetaRieszMarkedPrimeCompletion ZetaRieszMarkedLogDerivative
open ZetaRieszGlobalHorizontal

/-- Both denominators stay in the genuine zero/pole half-plane. -/
theorem half_radius {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) (xi : ℝ) :
    (1/2 : ℝ) ≤ ‖z‖ ∧ (1/2 : ℝ) ≤ ‖Complex.I*xi-z‖ := by
  constructor
  · have h := Complex.abs_re_le_norm z
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  · have h := Complex.abs_re_le_norm (Complex.I*(xi : ℂ)-z)
    have he : (Complex.I*(xi : ℂ)-z).re = -z.re := by simp
    rw [he,abs_of_nonneg (by linarith)] at h
    linarith

/-- Stay outside the central band and the particular mode's resonance.
The retained complement includes the selected resonance without a norm. -/
def Exterior (z : ℂ) (xi : ℝ) : Prop :=
  (1/2000 : ℝ) ≤ |xi| ∧ (1/40 : ℝ) ≤ |xi-z.im|

/-- A vertical separation of 1/40 supplies the rational radius used by
the already proved joint-order geometric estimate. -/
theorem exterior_radius {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) {xi : ℝ}
    (he : Exterior z xi) : modeRadius ≤ ‖Complex.I*xi-z‖ := by
  have hsq : ‖Complex.I*(xi : ℂ)-z‖^2 = z.re^2+(xi-z.im)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have ht := he.2
  have hnorm := norm_nonneg (Complex.I*(xi : ℂ)-z)
  dsimp only [modeRadius]
  nlinarith [sq_abs (xi-z.im)]

/-- An unmodified shifted principal part, with its original marked-order
normalization. Its unused order-zero value is harmless division by zero. -/
def shiftedMark (z : ℂ) (j : ℕ) (xi : ℝ) : ℂ :=
  ((Complex.I*xi-z)⁻¹)^j/(j : ℂ)

/-- The actual shifted factorial rectangle; no cofactor is completed. -/
def shiftedSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    shiftedMark z j xi*cofactor A N j h (3/2+Complex.I*y) xi

/-- Projection is performed on the coupled symbol before integration. -/
def exteriorSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  if Exterior z xi then shiftedSymbol z A N y xi else 0

/-- Both original phases remain, with the same mode-relative test on
their own signed frequency. -/
def exteriorPair (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*exteriorSymbol z A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*exteriorSymbol z A N y (-xi)

/-- The near-resonant part remains an exact signed complement. -/
theorem shiftedSymbol_split (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    shiftedSymbol z A N y xi = exteriorSymbol z A N y xi+
      (if Exterior z xi then 0 else shiftedSymbol z A N y xi) := by
  unfold exteriorSymbol
  split_ifs <;> simp

/-- The shifted principal part retains two inverse powers for the
subsequent sum over zero ordinates. -/
theorem shiftedMark_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) {xi : ℝ}
    (he : Exterior z xi) {j : ℕ} (hj : 2 ≤ j) :
    ‖shiftedMark z j xi‖ ≤ modeRadius⁻¹^j/‖Complex.I*xi-z‖^2 := by
  rw [shiftedMark,norm_div,Complex.norm_natCast]
  apply (div_le_self (norm_nonneg _) (by exact_mod_cast (show 1 ≤ j by omega))).trans
  rw [norm_pow]
  exact inverse_power_weighted (exterior_radius hz he) hj

/-- The original cofactor/order correlation supplies a geometric rate
on every retained exterior term, including right-edge modes. -/
theorem shiftedSymbol_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (he : Exterior z xi) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*shiftedSymbol z A N y xi‖ ≤
      largeCost*orderBudget N/‖Complex.I*xi-z‖^2 := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      2*mass (3/2-safeRadius) := by
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  unfold shiftedSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := largeCost*(9999/10000 : ℝ)^N/‖Complex.I*xi-z‖^2)
    (by positivity [largeCost_nonneg]) ?_).trans_eq (by unfold orderBudget; ring)
  intro j hj h hh
  have hm := shiftedMark_bound hz he (marked_order_two hh)
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
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)/‖Complex.I*xi-z‖^2) := by ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*
        (2*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)/‖Complex.I*xi-z‖^2) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh)
        (by positivity [mass_nonneg (3/2-safeRadius)])
    _ = _ := by unfold largeCost; ring

/-- A shifted denominator keeps an integrable Cauchy profile even at
an arbitrarily large ordinate. -/
theorem shifted_inverse_square_half {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) (xi : ℝ) :
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

/-- The Fourier weight supplies the actual inverse-square distance to
the zero, not a constant charge for infinitely many translated peaks. -/
theorem kernel_overlap_half {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ)) {xi : ℝ}
    (hxi : (1/2000 : ℝ) ≤ |xi|) :
    1/(‖Complex.I*xi-z‖^2*xi^2) ≤
      (8000010/‖z‖^2)*((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by
  have hr := half_radius hz xi
  have hz0 : 0 < ‖z‖^2 := by positivity [hr.1]
  have hd0 : 0 < ‖Complex.I*(xi : ℂ)-z‖^2 := by positivity [hr.2]
  have hx : 0 < xi^2 := by nlinarith [sq_abs xi]
  have hzn : ‖z‖ ≠ 0 := ne_of_gt (by linarith [hr.1])
  have hdn : ‖Complex.I*(xi : ℂ)-z‖ ≠ 0 := ne_of_gt (by linarith [hr.2])
  have hxn : xi ≠ 0 := by intro h; norm_num [h] at hx
  have ht : ‖z‖ ≤ ‖Complex.I*(xi : ℂ)-z‖+|xi| := by
    have ht := norm_sub_le (Complex.I*(xi : ℂ)-z) (Complex.I*(xi : ℂ))
    simpa only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs] using ht
  have ht2 : ‖z‖^2 ≤ 2*‖Complex.I*(xi : ℂ)-z‖^2+2*xi^2 := by
    have hs := mul_self_le_mul_self (norm_nonneg z) ht
    nlinarith [sq_nonneg (‖Complex.I*(xi : ℂ)-z‖-|xi|),sq_abs xi]
  have hbase : 1/(‖Complex.I*xi-z‖^2*xi^2) ≤
      (2/‖z‖^2)*(1/xi^2+1/‖Complex.I*xi-z‖^2) := by
    have he : (2/‖z‖^2)*(1/xi^2+1/‖Complex.I*xi-z‖^2) =
        (2*(‖Complex.I*xi-z‖^2+xi^2))/(‖z‖^2*(‖Complex.I*xi-z‖^2*xi^2)) := by
      field_simp [hzn,hdn,hxn]
    rw [he]
    apply (div_le_div_iff₀ (mul_pos hd0 hx) (mul_pos hz0 (mul_pos hd0 hx))).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht2 (mul_nonneg hd0.le hx.le)]
  have hf : 1/xi^2 ≤ 4000001*(1+xi^2)⁻¹ := by
    rw [show 4000001*(1+xi^2)⁻¹ = 4000001/(1+xi^2) by rw [div_eq_mul_inv]]
    apply (div_le_div_iff₀ hx (by positivity)).mpr
    nlinarith [sq_abs xi]
  apply hbase.trans
  have h := mul_le_mul_of_nonneg_left (add_le_add hf (shifted_inverse_square_half hz xi))
    (show 0 ≤ 2/‖z‖^2 by positivity)
  apply h.trans
  have h0 : 0 ≤ (1+xi^2)⁻¹ := by positivity
  have hs : 0 ≤ (1+(xi-z.im)^2)⁻¹ := by positivity
  have hsum : 2*(4000001*(1+xi^2)⁻¹+4*(1+(xi-z.im)^2)⁻¹) ≤
      8000010*((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by nlinarith
  convert mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hz0.le) using 1 <;> ring


/-- The full exterior symbol has a summable, distance-weighted frequency
profile. The central band is exactly zero in this isolated component. -/
theorem exteriorSymbol_profile {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*exteriorSymbol z A N y xi/(xi : ℂ)^2‖ ≤
      (8000010*largeCost*orderBudget N/‖z‖^2)*
        ((1+xi^2)⁻¹+(1+(xi-z.im)^2)⁻¹) := by
  by_cases he : Exterior z xi
  · rw [exteriorSymbol,if_pos he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    apply (div_le_div_of_nonneg_right (shiftedSymbol_bound hz A h16 N y he hu hU) (sq_nonneg xi)).trans
    calc
      _ = (largeCost*orderBudget N)*(1/(‖Complex.I*xi-z‖^2*xi^2)) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (kernel_overlap_half hz he.1)
          (mul_nonneg largeCost_nonneg (orderBudget_nonneg N))
        exact h.trans_eq (by ring)
  · simp only [exteriorSymbol,if_neg he,mul_zero,zero_div,norm_zero]
    positivity [largeCost_nonneg,orderBudget_nonneg N]

/-- A fixed coefficient for the paired Cauchy profile. -/
def exteriorConstant : ℝ := 16000020*largeCost

theorem exteriorConstant_nonneg : 0 ≤ exteriorConstant := by
  unfold exteriorConstant
  positivity [largeCost_nonneg]

/-- Both phases are estimated only on their respective nonresonant
regions. The residual signed pair is not replaced by a Fourier norm. -/
theorem exteriorPair_profile {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(exteriorPair z A N y L xi/(xi : ℂ)^2)‖ ≤
      (exteriorConstant*orderBudget N/‖z‖^2)*distanceProfile z xi := by
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*
      (Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*exteriorSymbol z A N y t)/(t : ℂ)^2‖ =
        ‖(u : ℂ)^(N+1)*exteriorSymbol z A N y t/(t : ℂ)^2‖ := by
    rw [mul_left_comm,mul_div_assoc,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  unfold exteriorPair
  rw [← mul_div_assoc,mul_add,add_div]
  apply (norm_add_le _ _).trans
  have hm : ((-xi : ℝ) : ℂ)^2 = (xi : ℂ)^2 := by push_cast; ring
  rw [he,← hm,he]
  have hsum := add_le_add (exteriorSymbol_profile hz A h16 N y xi hu hU)
    (exteriorSymbol_profile hz A h16 N y (-xi) hu hU)
  simp only [hm] at hsum ⊢
  apply hsum.trans
  simp only [neg_sq]
  rw [show (-xi-z.im)^2 = (xi-(-z.im))^2 by ring]
  unfold exteriorConstant distanceProfile
  have hp : 0 ≤ (8000010*largeCost*orderBudget N/‖z‖^2)*
      ((1+(xi-z.im)^2)⁻¹+(1+(xi-(-z.im))^2)⁻¹) := by
    positivity [largeCost_nonneg,orderBudget_nonneg N]
  ring_nf at hp ⊢
  linarith

theorem measurable_exteriorSymbol (z : ℂ) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ) :
    Measurable (fun xi : ℝ => exteriorSymbol z A N y xi) := by
  have hm : Measurable (fun xi : ℝ => shiftedSymbol z A N y xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Measurable.mul _ (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
    unfold shiftedMark
    fun_prop
  have hE : MeasurableSet {xi : ℝ | Exterior z xi} := by
    apply MeasurableSet.inter
    · exact (isClosed_le continuous_const continuous_abs).measurableSet
    · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).abs).measurableSet
  exact hm.ite hE measurable_const

theorem measurable_exteriorPair (z : ℂ) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => exteriorPair z A N y L xi/(xi : ℂ)^2) := by
  have hm := measurable_exteriorSymbol z A h16 N y
  have hn := hm.comp measurable_neg
  unfold exteriorPair
  fun_prop

/-- The hard exterior projection has an ordinary absolutely integrable
response. There is no boundary completion error. -/
theorem integrable_exteriorPair {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(exteriorPair z A N y L xi/(xi : ℂ)^2)) (Ioi 0) := by
  apply ((integrable_distanceProfile z).integrableOn.const_mul
    (exteriorConstant*orderBudget N/‖z‖^2)).mono'
  · exact ((measurable_exteriorPair z A h16 N y L).const_mul _).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => exteriorPair_profile hz A h16 N y L xi hu hU)

/-- An L1 estimate strong enough to sum every genuine zero before
performing the original frequency integral. -/
theorem integral_norm_exteriorPair_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    (∫ xi : ℝ in Ioi 0, ‖(u : ℂ)^(N+1)*(exteriorPair z A N y L xi/(xi : ℂ)^2)‖) ≤
      (3*Real.pi*exteriorConstant)*orderBudget N/‖z‖^2 := by
  have h := integral_mono_ae (integrable_exteriorPair hz A h16 N y L hu hU).norm
    ((integrable_distanceProfile z).integrableOn.const_mul (exteriorConstant*orderBudget N/‖z‖^2))
    (Eventually.of_forall (fun xi => exteriorPair_profile hz A h16 N y L xi hu hU))
  rw [integral_const_mul] at h
  have hp : (∫ xi : ℝ in Ioi 0, distanceProfile z xi) ≤ 3*Real.pi :=
    (setIntegral_le_integral (integrable_distanceProfile z)
      (Eventually.of_forall (distanceProfile_nonneg z))).trans_eq (integral_distanceProfile z)
  exact h.trans ((mul_le_mul_of_nonneg_left hp
    (by positivity [exteriorConstant_nonneg,orderBudget_nonneg N])).trans_eq (by ring))

/-- The exterior part of one genuine shifted principal part. -/
def exteriorResponse (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, exteriorPair z A N y L xi/(xi : ℂ)^2

/-- The common response constant is independent of the mode, prime
cutoff, order and height. -/
def exteriorResponseConstant : ℝ := 3*Real.pi*exteriorConstant

theorem exteriorResponseConstant_nonneg : 0 ≤ exteriorResponseConstant := by
  unfold exteriorResponseConstant
  positivity [exteriorConstant_nonneg]

/-- A genuine geometric payment for a shifted pole or zero mode outside
its resonance, with the original factorial weights still coupled. -/
theorem exteriorResponse_bound {z : ℂ} (hz : z.re ≤ -(1/2 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*exteriorResponse z A N y L‖ ≤
      exteriorResponseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N/‖z‖^2 := by
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold exteriorResponse
  rw [mul_left_comm,← integral_const_mul,norm_mul]
  apply (mul_le_mul hpref ((norm_integral_le_integral_norm _).trans
    (integral_norm_exteriorPair_bound hz A h16 N y L hu hU)) (norm_nonneg _) (by positivity)).trans
  calc
    _ ≤ ((N : ℝ)+2)*((3*Real.pi*exteriorConstant)*orderBudget N/‖z‖^2) := by
      exact mul_le_mul_of_nonneg_right (by linarith)
        (by positivity [exteriorConstant_nonneg,orderBudget_nonneg N])
    _ = _ := by unfold exteriorResponseConstant orderBudget; ring

/-- Every genuine zero has the half-plane separation used above. -/
theorem modeLocation_half (y : ℝ) (tau : NontrivialZetaZero) :
    (modeLocation y tau).re ≤ -(1/2 : ℝ) := by
  have ht := NontrivialZetaZero.re_lt_one tau
  simp only [modeLocation,Complex.sub_re]
  norm_num
  linarith

/-- The nonresonant shifted right-edge part of the genuine divisor,
inside the original paired symbol and factorial rectangle. -/
def edgeExteriorPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
    (analyticZetaZeroMultiplicity tau : ℂ)*exteriorPair (modeLocation y tau) A N y L xi else 0

/-- The full frequency integral of that actual global principal part. -/
def edgeExteriorResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, edgeExteriorPair A N y L xi/(xi : ℂ)^2

/-- The coupled zero series has summable full-frequency L1 norms. -/
theorem edgeExteriorPair_L1 (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    let F := (fun tau : NontrivialZetaZero => fun xi : ℝ =>
      if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*
          (exteriorPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0)
    (∀ tau, IntegrableOn (F tau) (Ioi 0)) ∧
      Summable (fun tau => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (exteriorPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  have hi (tau : NontrivialZetaZero) : IntegrableOn (F tau) (Ioi 0) := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · simpa only [IntegrableOn,F,if_pos ht,mul_left_comm] using
        (integrable_exteriorPair (modeLocation_half y tau) A h16 N y L hu hU).const_mul
          (analyticZetaZeroMultiplicity tau : ℂ)
    · simp only [F,if_neg ht]
      exact integrableOn_zero
  have hn (tau : NontrivialZetaZero) :
      (∫ xi : ℝ in Ioi 0, ‖F tau xi‖) ≤
        (exteriorResponseConstant*orderBudget N)*zeroWeight y tau := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · have he (xi : ℝ) : ‖F tau xi‖ = (analyticZetaZeroMultiplicity tau : ℝ)*
          ‖(u : ℂ)^(N+1)*(exteriorPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)‖ := by
        dsimp only [F]
        rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      simp_rw [he]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left
        (integral_norm_exteriorPair_bound (modeLocation_half y tau) A h16 N y L hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq
          (by unfold exteriorResponseConstant zeroWeight; ring)
    · simp only [F,if_neg ht,norm_zero,integral_zero]
      positivity [exteriorResponseConstant_nonneg,orderBudget_nonneg N,zeroWeight_nonneg y tau]
  have hsum : Summable (fun tau : NontrivialZetaZero => ∫ xi : ℝ in Ioi 0, ‖F tau xi‖) :=
    ((summable_zeroWeight y).mul_left (exteriorResponseConstant*orderBudget N)).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn
  exact ⟨hi,hsum⟩

/-- Absolute integrability of the coupled response licenses summing
the genuine zero divisor inside the Fourier integral. This is not an
inverse of a global infinite zero product. -/
theorem hasSum_edgeExteriorResponse (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    HasSum (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        exteriorResponse (modeLocation y tau) A N y L) else 0)
      ((u : ℂ)^(N+1)*edgeExteriorResponse A N y L) := by
  let F (tau : NontrivialZetaZero) (xi : ℝ) : ℂ :=
    if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
      ((analyticZetaZeroMultiplicity tau : ℂ)*
        (exteriorPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0
  obtain ⟨hi,hsum⟩ := edgeExteriorPair_L1 A h16 N y L hu hU
  have hs := (hasSum_integral_of_summable_integral_norm hi hsum).mul_left
    (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ)))
  have hs' : HasSum (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
        exteriorResponse (modeLocation y tau) A N y L) else 0)
      (((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0, ∑' tau, F tau xi) := by
    apply hs.congr_fun
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · simp only [if_pos ht,integral_const_mul,exteriorResponse]
      ring
    · simp only [if_neg ht,integral_zero,mul_zero]
  have he (xi : ℝ) : (∑' tau, F tau xi) =
      (u : ℂ)^(N+1)*(edgeExteriorPair A N y L xi/(xi : ℂ)^2) := by
    rw [edgeExteriorPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re <;> simp [F,ht,mul_div_assoc]
  convert hs' using 1
  simp_rw [he,integral_const_mul]
  unfold edgeExteriorResponse
  ring

/-- The global paired principal part is genuinely integrable, not an
arbitrary value assigned to a divergent integral. -/
theorem integrable_edgeExteriorPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => edgeExteriorPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  obtain ⟨hi,hs⟩ := edgeExteriorPair_L1 A h16 N y L (u := 1/2) (by norm_num)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  have h := integrable_complex_tsum hi hs
  have he (xi : ℝ) :
      (∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
        (((1/2 : ℝ) : ℂ)^(N+1))*((analyticZetaZeroMultiplicity tau : ℂ)*
          (exteriorPair (modeLocation y tau) A N y L xi/(xi : ℂ)^2)) else 0) =
      (((1/2 : ℝ) : ℂ)^(N+1))*(edgeExteriorPair A N y L xi/(xi : ℂ)^2) := by
    rw [edgeExteriorPair,← tsum_div_const,← tsum_mul_left]
    apply tsum_congr
    intro tau
    by_cases ht : (999/1000 : ℝ) < tau.1.re <;> simp [ht,mul_div_assoc]
  simp_rw [he] at h
  exact (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ)))
    (isUnit_iff_ne_zero.mpr (pow_ne_zero (N+1) (by norm_num : ((1/2 : ℝ) : ℂ) ≠ 0))) _).mp h

/-- The entire right-edge exterior zero sector has an explicit geometric
bound with its true multiplicity-weighted zero count already paid. -/
theorem edgeExteriorResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {L u : ℝ} (hL : 1 ≤ L)
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*edgeExteriorResponse A N y L‖ ≤
      (exteriorResponseConstant*zeroMass y)*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have hs := hasSum_edgeExteriorResponse A h16 N y L hu hU
  have hb (tau : NontrivialZetaZero) :
      ‖if (999/1000 : ℝ) < tau.1.re then (u : ℂ)^(N+1)*
        ((analyticZetaZeroMultiplicity tau : ℂ)*exteriorResponse (modeLocation y tau) A N y L) else 0‖ ≤
      (exteriorResponseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N)*zeroWeight y tau := by
    by_cases ht : (999/1000 : ℝ) < tau.1.re
    · rw [if_pos ht,mul_left_comm,norm_mul,Complex.norm_natCast]
      exact (mul_le_mul_of_nonneg_left
        (exteriorResponse_bound (modeLocation_half y tau) A h16 N y hL hu hU)
        (Nat.cast_nonneg (analyticZetaZeroMultiplicity tau))).trans_eq (by unfold zeroWeight; ring)
    · simp only [if_neg ht,norm_zero]
      positivity [exteriorResponseConstant_nonneg,zeroWeight_nonneg y tau]
  rw [← hs.tsum_eq]
  apply (norm_tsum_le_tsum_norm hs.summable.norm).trans
  apply (hs.summable.norm.tsum_le_tsum hb
    ((summable_zeroWeight y).mul_left (exteriorResponseConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))).trans_eq
  rw [tsum_mul_left]
  unfold zeroMass
  ring




/-- The shifted zero sum is the actual xi derivative at the shifted
ordinate, not a separate-leg limit or synthetic modal expansion. -/
theorem hasSum_shiftedMark (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    HasSum (fun tau : NontrivialZetaZero => (analyticZetaZeroMultiplicity tau : ℂ)*
      shiftedMark (modeLocation y tau) j xi)
      (signedTaylorMoment (j-1) (logDeriv riemannXi) (3/2+Complex.I*y+Complex.I*xi)/(j : ℂ)) := by
  have h := (ZetaRieszShiftedCenter.hasSum_global_zero_moment (y+xi) (j-1) (by omega)).div_const (j : ℂ)
  have he : ZetaRieszShiftedCenter.center (y+xi) = 3/2+Complex.I*y+Complex.I*xi := by
    unfold ZetaRieszShiftedCenter.center
    push_cast
    ring
  rw [he] at h
  apply h.congr_fun
  intro tau
  simp only [shiftedMark,modeLocation,show j-1+1=j by omega]
  rw [show Complex.I*(xi : ℂ)-(tau.1-(3/2+Complex.I*y)) =
    3/2+Complex.I*y+Complex.I*xi-tau.1 by ring]
  ring

/-- Keep the selected and competing modes inside their resonance bands. -/
def retainedDifference (z : ℂ) (j : ℕ) (xi : ℝ) : ℂ :=
  shiftedMark z j 0-(if Exterior z xi then 0 else shiftedMark z j xi)

/-- Exact signed deletion of only the paid shifted part. -/
theorem modeDifference_add_exterior (z : ℂ) (j : ℕ) (xi : ℝ) :
    modeDifference z j xi+(if Exterior z xi then shiftedMark z j xi else 0) =
      retainedDifference z j xi := by
  simp only [modeDifference,retainedDifference,shiftedMark,Complex.ofReal_zero,mul_zero,zero_sub]
  split_ifs <;> ring

/-- The actual exterior shifted zero coefficient on the right edge. -/
def exteriorEdgeMark (y xi : ℝ) (j : ℕ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
    (analyticZetaZeroMultiplicity tau : ℂ)*
      (if Exterior (modeLocation y tau) xi then shiftedMark (modeLocation y tau) j xi else 0) else 0

/-- The exact remaining signed zero coefficient; its resonances are
retained rather than bounded by absolute values. -/
def retainedEdgeDifference (y xi : ℝ) (j : ℕ) : ℂ :=
  ∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
    (analyticZetaZeroMultiplicity tau : ℂ)*retainedDifference (modeLocation y tau) j xi else 0

theorem summable_exteriorEdgeMark (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    Summable (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (analyticZetaZeroMultiplicity tau : ℂ)*
        (if Exterior (modeLocation y tau) xi then shiftedMark (modeLocation y tau) j xi else 0) else 0) := by
  apply (hasSum_shiftedMark y xi hj).summable.norm.of_norm_bounded
  intro tau
  split_ifs <;> simp only [mul_zero,norm_zero,le_refl] <;> exact norm_nonneg _

/-- The exterior and central terms are parts of one convergent global
principal-part series, with the original residue sign. -/
theorem edgeDifference_add_exterior (y xi : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    edgeDifference y xi j+exteriorEdgeMark y xi j = retainedEdgeDifference y xi j := by
  have hd : Summable (fun tau : NontrivialZetaZero => if tau.1.re ≤ (999/1000 : ℝ) then 0 else
      (analyticZetaZeroMultiplicity tau : ℂ)*modeDifference (modeLocation y tau) j xi) := by
    apply (hasSum_xiDifference y xi hj).summable.norm.of_norm_bounded
    intro tau
    by_cases ht : tau.1.re ≤ (999/1000 : ℝ)
    · simp only [if_pos ht,norm_zero]
      exact norm_nonneg _
    · simp only [if_neg ht,le_refl]
  rw [edgeDifference,exteriorEdgeMark,← hd.tsum_add (summable_exteriorEdgeMark y xi hj),retainedEdgeDifference]
  apply tsum_congr
  intro tau
  by_cases ht : (999/1000 : ℝ) < tau.1.re
  · simp only [if_pos ht,if_neg (not_le.mpr ht),← mul_add,modeDifference_add_exterior]
  · simp only [if_neg ht,if_pos (not_lt.mp ht),add_zero]

/-- Summing the original rectangle commutes with this absolutely
convergent projected zero coefficient. -/
theorem hasSum_exteriorEdgeSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    HasSum (fun tau : NontrivialZetaZero => if (999/1000 : ℝ) < tau.1.re then
      (analyticZetaZeroMultiplicity tau : ℂ)*exteriorSymbol (modeLocation y tau) A N y xi else 0)
      (∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        exteriorEdgeMark y xi j*cofactor A N j h (3/2+Complex.I*y) xi) := by
  have hs := hasSum_sum (fun j (_hj : j ∈ Finset.range (N+2)) =>
    hasSum_sum (fun h (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) =>
      (summable_exteriorEdgeMark y xi (marked_order_two hh)).hasSum.mul_right
        (cofactor A N j h (3/2+Complex.I*y) xi)))
  apply hs.congr_fun
  intro tau
  by_cases ht : (999/1000 : ℝ) < tau.1.re
  · by_cases he : Exterior (modeLocation y tau) xi
    · simp only [if_pos ht,if_pos he,exteriorSymbol,shiftedSymbol,Finset.mul_sum,mul_assoc]
    · simp only [if_pos ht,if_neg he,exteriorSymbol,mul_zero,zero_mul,Finset.sum_const_zero]
  · simp only [if_neg ht,zero_mul,Finset.sum_const_zero]

/-- The genuine zeta pole has the same half-plane geometry, including
its nonzero ordinate relative to the selected evaluation center. -/
def poleLocation (y : ℝ) : ℂ := 1-(3/2+Complex.I*y)

theorem poleLocation_half (y : ℝ) : (poleLocation y).re ≤ -(1/2 : ℝ) := by
  norm_num [poleLocation]

/-- Exact signed symbol left after paying the two disjoint exterior
components. Both unshifted parts and the complete resonances remain. -/
def resonantSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    (retainedDifference (poleLocation y) j xi-retainedEdgeDifference y xi j)*
      cofactor A N j h (3/2+Complex.I*y) xi

/-- The new geometric payments belong to the actual pole/right-edge
expression. No count, allocation, physical support or phase is altered. -/
theorem poleEdgeSymbol_split (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    ZetaRieszGlobalHorizontal.retainedSymbol A N y xi-
        ZetaRieszCompletionPayment.completionSymbol A N (3/2+Complex.I*y) xi+
      exteriorSymbol (poleLocation y) A N y xi-
        (∑' tau : NontrivialZetaZero, if (999/1000 : ℝ) < tau.1.re then
          (analyticZetaZeroMultiplicity tau : ℂ)*exteriorSymbol (modeLocation y tau) A N y xi else 0) =
      resonantSymbol A N y xi := by
  rw [(hasSum_exteriorEdgeSymbol A N y xi).tsum_eq,ZetaRieszGlobalHorizontal.retainedSymbol,add_sub_cancel_left]
  have hp : exteriorSymbol (poleLocation y) A N y xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        (if Exterior (poleLocation y) xi then shiftedMark (poleLocation y) j xi else 0)*
          cofactor A N j h (3/2+Complex.I*y) xi := by
    unfold exteriorSymbol
    split_ifs <;> simp only [shiftedSymbol,zero_mul,Finset.sum_const_zero]
  rw [hp,resonantSymbol,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  have he := edgeDifference_add_exterior y xi (marked_order_two hh)
  have hp := modeDifference_add_exterior (poleLocation y) j xi
  change _ = (retainedDifference (poleLocation y) j xi-retainedEdgeDifference y xi j)*_
  rw [← he,← hp]
  unfold poleLocation
  ring

/-- The corrected main changes only the independently paid shifted
exteriors of the pole and right-edge zero divisor. -/
def resonantMain (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszGlobalHorizontal.poleEdgeMain u y N+
    exteriorResponse (poleLocation y) (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)-
    edgeExteriorResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)

/-- A finite height-dependent budget for both disjoint exterior payments. -/
def paymentConstant (y : ℝ) : ℝ :=
  exteriorResponseConstant*(1/‖poleLocation y‖^2+zeroMass y)

theorem paymentConstant_nonneg (y : ℝ) : 0 ≤ paymentConstant y := by
  unfold paymentConstant
  positivity [exteriorResponseConstant_nonneg,zeroMass_nonneg y]

/-- Both pole and zero exterior components have an explicit geometric
payment at the literal moving length and original rough-prime support. -/
theorem poleEdge_resonant_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(resonantMain u y N-ZetaRieszGlobalHorizontal.poleEdgeMain u y N)‖ ≤
      paymentConstant y*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have he : resonantMain u y N-ZetaRieszGlobalHorizontal.poleEdgeMain u y N =
      exteriorResponse (poleLocation y) (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N)-
      edgeExteriorResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
        (SquarefreeVaughanLogSource.length u N) := by unfold resonantMain; ring
  rw [he,mul_sub]
  apply (norm_sub_le _ _).trans
  exact (add_le_add
    (exteriorResponse_bound (poleLocation_half y) _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU)
    (edgeExteriorResponse_bound _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
      (ZetaRieszHeadOrders.one_le_length u N) hu hU)).trans_eq (by unfold paymentConstant; ring)

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

/-- The literal packet retains its source after the new exterior
payments. This theorem does not bound the surviving signed resonances. -/
theorem tendsto_resonant_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (resonantMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have he : Tendsto (fun N => (u : ℂ)^(N+1)*
      (resonantMain u y N-ZetaRieszGlobalHorizontal.poleEdgeMain u y N)) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => paymentConstant y*(((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))
    · intro N
      simpa only [mul_assoc] using poleEdge_resonant_bound (by linarith : 0 ≤ u) hU y N
    · simpa only [mul_zero] using tendsto_cubic_rate.const_mul (paymentConstant y)
  have h := (ZetaRieszGlobalHorizontal.tendsto_poleEdge_sub_current hu hU y).add
    (he.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [add_zero] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def]
  ring


/-- The shifted part of the retained response is confined to explicit
central or zero-relative intervals. Its values there stay signed. -/
theorem retained_shift_support {z : ℂ} {j : ℕ} {xi : ℝ}
    (h : retainedDifference z j xi ≠ shiftedMark z j 0) :
    |xi| < (1/2000 : ℝ) ∨ |xi-z.im| < (1/40 : ℝ) := by
  by_contra hn
  have he : Exterior z xi := by
    rw [not_or] at hn
    exact ⟨not_lt.mp hn.1,not_lt.mp hn.2⟩
  exact h (by simp only [retainedDifference,if_pos he,sub_zero])

/-- No central or mode-resonant term is included in the norm payment. -/
theorem exteriorSymbol_zero_of_resonance (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ)
    (h : |xi| < (1/2000 : ℝ) ∨ |xi-z.im| < (1/40 : ℝ)) :
    exteriorSymbol z A N y xi = 0 := by
  have hn : ¬Exterior z xi := by
    intro he
    rcases h with h | h
    · exact (not_le.mpr h) he.1
    · exact (not_le.mpr h) he.2
  exact if_neg hn

/-- Combined error relative to the original signed log main. The full
horizontal zero sector, Gamma correction, shifted pole exterior and
shifted right-edge exterior are each charged once. -/
theorem logMain_resonant_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-resonantMain u y N)‖ ≤
      (ZetaRieszGlobalHorizontal.responseConstant*zeroMass y+
        Real.pi*(couplingConstant+couplingMassConstant)+paymentConstant y)*
        ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have he : logMain u y N-resonantMain u y N =
      (logMain u y N-ZetaRieszGlobalHorizontal.poleEdgeMain u y N)-
        (resonantMain u y N-ZetaRieszGlobalHorizontal.poleEdgeMain u y N) := by ring
  rw [he,mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add
    (ZetaRieszGlobalHorizontal.logMain_poleEdge_bound hu hU y hN)
    (poleEdge_resonant_bound hu hU y N)).trans_eq (by ring))

end
end RiemannGaussian.ZetaRieszShiftedExterior
