/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaExposedMovingModes
import RiemannGaussian.ZetaRieszMarkedLogDerivative
import RiemannGaussian.ZetaRieszLocalXiDivisor

/-!
# Paying separated zero modes together with the literal ordered cofactor

The marked order uses only part of the total factorial order. Its exposed
gap must beat the cofactor amplification before the whole symbol can be
declared small. We retain the exact cofactor, rectangle and Fourier zero.
The selected mode, closer competitors and exterior frequencies remain signed.
-/

namespace RiemannGaussian.ZetaRieszExposedModeCoupling
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszOrderedEulerBound ZetaRieszMarkedPrimeCompletion
open ZetaRieszMarkedLogDerivative ZetaRieszMarkedEuler

/-- An actual principal part at both marked frequencies, with the exact
reciprocal marked order. Its Fourier zero is not separated by a norm. -/
def modeDifference (z : ℂ) (j : ℕ) (xi : ℝ) : ℂ :=
  (((-z)⁻¹)^j-((Complex.I*xi-z)⁻¹)^j)/(j : ℂ)

/-- The power difference retains the separation of the two inverse nodes. -/
theorem power_difference (x y : ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t) (k : ℕ) :
    ‖x^(k+1)-y^(k+1)‖ ≤ ((k+1 : ℕ) : ℝ)*t^k*‖x-y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : x^(k+1+1)-y^(k+1+1) =
        x*(x^(k+1)-y^(k+1))+(x-y)*y^(k+1) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_pow]
    calc
      _ ≤ t*(((k+1 : ℕ) : ℝ)*t^k*‖x-y‖)+‖x-y‖*t^(k+1) := by
        gcongr
      _ = _ := by push_cast; ring

/-- The marked difference gains one frequency factor uniformly while
both denominators stay outside the same positive radius. -/
theorem modeDifference_bound {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz : R ≤ ‖z‖) (xi : ℝ) (hx : R ≤ ‖Complex.I*xi-z‖)
    {j : ℕ} (hj : 0 < j) :
    ‖modeDifference z j xi‖ ≤ |xi| *R⁻¹^(j+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have ha0 : -z ≠ 0 := norm_pos_iff.mp (by simpa only [norm_neg] using hR.trans_le hz)
  have hb0 : Complex.I*(xi : ℂ)-z ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  have ha : ‖(-z)⁻¹‖ ≤ R⁻¹ := by
    rw [norm_inv,norm_neg]
    exact (inv_le_inv₀ (hR.trans_le hz) hR).mpr hz
  have hb : ‖(Complex.I*(xi : ℂ)-z)⁻¹‖ ≤ R⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hR.trans_le hx) hR).mpr hx
  have hd : ‖(-z)⁻¹-(Complex.I*(xi : ℂ)-z)⁻¹‖ ≤ |xi| *R⁻¹^2 := by
    rw [inv_sub_inv ha0 hb0,norm_div,norm_mul,norm_neg,
      show Complex.I*(xi : ℂ)-z-(-z)=Complex.I*(xi : ℂ) by ring,
      norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    have hden : R^2 ≤ ‖z‖*‖Complex.I*(xi : ℂ)-z‖ := by nlinarith
    apply (div_le_div_of_nonneg_left (abs_nonneg xi) (sq_pos_of_pos hR) hden).trans_eq
    simp only [div_eq_mul_inv,inv_pow]
  have hp := (power_difference _ _ (inv_nonneg.mpr hR.le) ha hb k).trans
    (mul_le_mul_of_nonneg_left hd (by positivity))
  unfold modeDifference
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) (k+1))).trans_eq
  have hk : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Nat.succ_eq_add_one, pow_add, pow_one]
  field_simp [hk, hR.ne']

/-- The fixed Fourier band leaves an effective denominator radius 1001/2000
for every mode of modulus at least 501/1000. -/
theorem shifted_radius {z : ℂ} (hz : (501/1000 : ℝ) ≤ ‖z‖)
    {xi : ℝ} (hxi : |xi| ≤ 1/2000) :
    (1001/2000 : ℝ) ≤ ‖Complex.I*xi-z‖ := by
  have h := norm_sub_norm_le (z : ℂ) (Complex.I*(xi : ℂ))
  rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    norm_sub_rev z] at h
  linarith

/-- The cofactor rate is included in this rational check. A gap on the
marked leg alone is not the asserted inequality. -/
theorem coupled_rate_check :
    (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)^2*
      (safeRadius/(1001/2000 : ℝ)) ≤ (9999/10000 : ℝ)^2 := by
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius]

/-- The actual marked half-order pays the entire complementary cofactor
order, leaving an explicit geometric rate for the coupled term. -/
theorem coupled_order_bound {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {N j h : ℕ} (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
    u^(N+1)*(1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j) ≤
      2*(9999/10000 : ℝ)^N := by
  have hn : N ≤ 2*j := by
    have hb := (Finset.mem_filter.mp hh).2
    omega
  have hjN : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  let a : ℝ := ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius
  let b : ℝ := safeRadius/(1001/2000 : ℝ)
  have ha0 : 0 ≤ a := by norm_num [a,ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius]
  have ha2 : a ≤ 2 := by norm_num [a,ZetaRieszWideOwnerAudit.radiusCeiling,safeRadius]
  have hb0 : 0 ≤ b := by norm_num [b,safeRadius]
  have hb1 : b ≤ 1 := by norm_num [b,safeRadius]
  have hrate : a^2*b ≤ (9999/10000 : ℝ)^2 := coupled_rate_check
  have hp : (a^(N+1)*b^j)^2 ≤ (a*(9999/10000 : ℝ)^N)^2 := by
    calc
      _ = a^2*(a^2)^N*b^(2*j) := by ring
      _ ≤ a^2*(a^2)^N*b^N := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hb0 hb1 hn) (by positivity)
      _ = a^2*(a^2*b)^N := by ring
      _ ≤ a^2*((9999/10000 : ℝ)^2)^N := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 N]
  have hroot : a^(N+1)*b^j ≤ a*(9999/10000 : ℝ)^N := by
    nlinarith [show 0 ≤ a^(N+1)*b^j by positivity,
      show 0 ≤ a*(9999/10000 : ℝ)^N by positivity]
  have he : ZetaRieszWideOwnerAudit.radiusCeiling^(N+1)*
      (1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j) = a^(N+1)*b^j := by
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
        (1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j) := by
      have hR := safeRadius_pos
      gcongr
    _ = a^(N+1)*b^j := he
    _ ≤ a*(9999/10000 : ℝ)^N := hroot
    _ ≤ 2*(9999/10000 : ℝ)^N := by gcongr

/-- A principal part is coupled to the unchanged ordered cofactor and
the complete marked factorial rectangle before taking its norm. -/
def modeSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    modeDifference z j xi*cofactor A N j h (3/2+Complex.I*y) xi

/-- The fixed cofactor constant is independent of the prime cutoff,
height, total order and choice of separated mode. -/
def couplingConstant : ℝ :=
  4*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)

theorem couplingConstant_nonneg : 0 ≤ couplingConstant := by
  unfold couplingConstant
  positivity [logMass_nonneg (by norm_num [safeRadius] : (1 : ℝ) < 3/2-safeRadius)]

/-- A geometric estimate for the actual coupled marked symbol. The
quadratic Fourier zero is retained, so the Riesz origin is integrable. -/
theorem modeSymbol_bound_of_radii {z : ℂ} (hz : (1001/2000 : ℝ) ≤ ‖z‖)
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (hxi : (1001/2000 : ℝ) ≤ ‖Complex.I*xi-z‖) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*modeSymbol z A N y xi‖ ≤
      couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2 := by
  have hR := safeRadius_pos
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hlog := logMass_nonneg hs
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r)) ≤
      |xi| *logMass (3/2-safeRadius) := by
    simp_rw [show ∀ r : ℕ, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r) =
      |xi| *(Real.log r*zetaPrimeExpWeight (3/2-safeRadius) r) from fun r => by ring]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_logMass_le A hs) (abs_nonneg xi)
  unfold modeSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := couplingConstant*(9999/10000 : ℝ)^N*xi^2)
    (by positivity [couplingConstant_nonneg]) ?_).trans_eq
    (by ring)
  intro j hj h hh
  have hm := modeDifference_bound (by norm_num : (0 : ℝ) < 1001/2000)
    hz xi hxi (marked_order_pos hh)
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi
    (fun p => |xi| *Real.log p) (fun p => mul_nonneg (abs_nonneg xi) (Real.log_natCast_nonneg p))
    (fun p => ZetaRieszMainFrequency.phase_le_log p xi)
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*(1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j))*
        ((1001/2000 : ℝ)⁻¹*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)*xi^2) := by
      rw [pow_succ,← sq_abs]; ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*
        ((1001/2000 : ℝ)⁻¹*Real.exp (4*mass (3/2-safeRadius))*logMass (3/2-safeRadius)*xi^2) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh) (by positivity)
    _ ≤ couplingConstant*(9999/10000 : ℝ)^N*xi^2 := by
      unfold couplingConstant
      have hi : (1001/2000 : ℝ)⁻¹ ≤ 2 := by norm_num
      nlinarith [mul_le_mul_of_nonneg_right hi
        (show 0 ≤ 2*(9999/10000 : ℝ)^N*Real.exp (4*mass (3/2-safeRadius))*
          logMass (3/2-safeRadius)*xi^2 by positivity)]

/-- Small frequencies leave the required gap on both marked legs. -/
theorem modeSymbol_bound {z : ℂ} (hz : (501/1000 : ℝ) ≤ ‖z‖)
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (hxi : |xi| ≤ 1/2000) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*modeSymbol z A N y xi‖ ≤
      couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2 :=
  modeSymbol_bound_of_radii (by linarith) A h16 N y (shifted_radius hz hxi) hu hU

/-- Genuine separated zeros; all other zeros remain in the signed rest. -/
def farDivisor (W : Finset NontrivialZetaZero) (y : ℝ) : Finset NontrivialZetaZero :=
  W.filter (fun tau => (501/1000 : ℝ) ≤ ‖tau.1-(3/2+Complex.I*y)‖)

/-- The selected source is never removed by this partial payment. -/
theorem selected_not_far (W : Finset NontrivialZetaZero) (rho : NontrivialZetaZero)
    (hu : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    rho ∉ farDivisor W rho.1.im := by
  have he : rho.1-(3/2+Complex.I*(rho.1.im : ℂ)) =
      -((3/2-rho.1.re : ℝ) : ℂ) := by apply Complex.ext <;> simp
  have hp : 0 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  simp only [farDivisor,Finset.mem_filter,he,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hp]
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hu
  intro h
  linarith [h.2]

/-- The full actual multiplicity weight of the paid finite sector. -/
def farMass (W : Finset NontrivialZetaZero) (y : ℝ) : ℝ :=
  ∑ tau ∈ farDivisor W y, (analyticZetaZeroMultiplicity tau : ℝ)

theorem farMass_nonneg (W : Finset NontrivialZetaZero) (y : ℝ) : 0 ≤ farMass W y := by
  unfold farMass
  positivity

/-- Signed principal parts in the marked logarithmic derivative. The
minus sign with which these enter the carrier is retained in the ledger. -/
def farSymbol (W : Finset NontrivialZetaZero) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ tau ∈ farDivisor W y, (analyticZetaZeroMultiplicity tau : ℂ)*
    modeSymbol (tau.1-(3/2+Complex.I*y)) A N y xi

theorem farSymbol_bound (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {xi u : ℝ} (hxi : |xi| ≤ 1/2000) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*farSymbol W A N y xi‖ ≤
      farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2 := by
  unfold farSymbol
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ tau ∈ farDivisor W y, (analyticZetaZeroMultiplicity tau : ℝ)*
        (couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2) := by
      apply Finset.sum_le_sum
      intro tau htau
      rw [show (u : ℂ)^(N+1)*((analyticZetaZeroMultiplicity tau : ℂ)*
          modeSymbol (tau.1-(3/2+Complex.I*y)) A N y xi) =
        (analyticZetaZeroMultiplicity tau : ℂ)*((u : ℂ)^(N+1)*
          modeSymbol (tau.1-(3/2+Complex.I*y)) A N y xi) by ring,
        norm_mul,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (modeSymbol_bound (Finset.mem_filter.mp htau).2 A h16 N y hxi hu hU) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; dsimp [farMass]; ring

/-- Both frequencies and the moving Riesz phase remain coupled. -/
def farPair (W : Finset NontrivialZetaZero) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*farSymbol W A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*farSymbol W A N y (-xi)

theorem farPair_bound (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {xi u : ℝ} (hxi : |xi| ≤ 1/2000) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(farPair W A N y L xi/(xi : ℂ)^2)‖ ≤
      2*farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
  by_cases hx : xi = 0
  · simp only [hx,Complex.ofReal_zero,zero_pow (by omega : 2 ≠ 0),div_zero,mul_zero,norm_zero]
    positivity [farMass_nonneg W y,couplingConstant_nonneg]
  have hb : ‖(u : ℂ)^(N+1)*farPair W A N y L xi‖ ≤
      2*farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N*xi^2 := by
    unfold farPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    have he (t : ℝ) : ‖(u : ℂ)^(N+1)*(Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*
        farSymbol W A N y t)‖ = ‖(u : ℂ)^(N+1)*farSymbol W A N y t‖ := by
      rw [mul_left_comm,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    rw [he,show -xi*L = (-xi)*L by rfl,he]
    exact (add_le_add (farSymbol_bound W A h16 N y hxi hu hU)
      (farSymbol_bound W A h16 N y (by simpa using hxi : |-xi| ≤ 1/2000) hu hU)).trans_eq
        (by rw [neg_sq]; ring)
  rw [← mul_div_assoc,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact (div_le_div_of_nonneg_right hb (sq_nonneg xi)).trans_eq
    (mul_div_cancel_right₀ _ (pow_ne_zero 2 hx))

theorem measurable_farPair (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => farPair W A N y L xi/(xi : ℂ)^2) := by
  have hm : Measurable (fun xi : ℝ => farSymbol W A N y xi) := by
    apply Finset.measurable_fun_sum
    intro tau _htau
    apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Measurable.mul _ (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
    unfold modeDifference
    fun_prop
  have hn := hm.comp measurable_neg
  unfold farPair
  fun_prop

/-- Genuine integrability at the Fourier origin, not a totalized integral. -/
theorem integrable_scaled_farPair (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(farPair W A N y L xi/(xi : ℂ)^2))
      (Ioc 0 (1/2000 : ℝ)) := by
  apply (integrableOn_const (C := (2*farMass W y*couplingConstant*
    ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N : ℝ)) measure_Ioc_lt_top.ne).mono'
  · exact ((measurable_farPair W A h16 N y L).const_mul _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with xi hxi
    exact farPair_bound W A h16 N y L (by rw [abs_of_pos hxi.1]; exact hxi.2) hu hU

/-- Only the stated Fourier band and separated genuine divisor are paid. -/
def farResponse (W : Finset NontrivialZetaZero) (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioc 0 (1/2000 : ℝ), farPair W A N y L xi/(xi : ℂ)^2

/-- This uniform geometric bound includes the Riesz integral and moving
length. No estimate on the selected mode has been used. -/
theorem farResponse_bound (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*farResponse W A N y L‖ ≤
      2*farMass W y*couplingConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have hc : 0 ≤ 2*farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
    positivity [farMass_nonneg W y,couplingConstant_nonneg]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Ioc 0 (1/2000 : ℝ)) measure_Ioc_lt_top (fun xi hxi =>
      farPair_bound W A h16 N y L (by rw [abs_of_pos hxi.1]; exact hxi.2) hu hU)
  simp only [Measure.real,Real.volume_Ioc,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2000-0)] at hi
  have hi' : ‖∫ xi : ℝ in Ioc 0 (1/2000 : ℝ),
      (u : ℂ)^(N+1)*(farPair W A N y L xi/(xi : ℂ)^2)‖ ≤
      2*farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
    exact hi.trans (mul_le_of_le_one_right hc (by norm_num))
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold farResponse
  rw [mul_left_comm,← integral_const_mul,norm_mul]
  apply (mul_le_mul hpref hi' (norm_nonneg _) (by positivity)).trans
  calc
    _ ≤ ((N : ℝ)+2)*(2*farMass W y*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hc
    _ = _ := by ring

/-- A fixed finite divisor is paid uniformly over arbitrary physical
prime sets and admissible moving lengths. -/
theorem tendsto_farResponse (W : Finset NontrivialZetaZero) (y : ℝ)
    (A : ℕ → Finset ℕ) (h16 : ∀ N p, p ∈ A N → 16 ≤ p)
    (length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*farResponse W (A N) N y (length N)) atTop (nhds 0) := by
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
    · ext N; simp only [pow_zero,pow_one]; ring
    · norm_num
  apply squeeze_zero_norm (a := fun N : ℕ =>
    (2*farMass W y*couplingConstant)*(((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))
  · intro N
    simpa only [mul_assoc] using farResponse_bound W (A N) (h16 N) N y (hL N) hu hU
  · simpa only [mul_zero] using ht.const_mul (2*farMass W y*couplingConstant)

private theorem reciprocal_moment (s a : ℂ) (n : ℕ) :
    signedTaylorMoment n (fun z => 1/(z-a)) s = ((s-a)⁻¹)^(n+1) := by
  have ht := congrFun (iteratedDeriv_comp_const_add n (fun z : ℂ => (z-a)⁻¹) s) 0
  simp only [add_zero] at ht
  rw [show (fun z : ℂ => 1/(z-a)) = (fun z => (z-a)⁻¹) by ext; simp,
    signedTaylorMoment,← ht]
  have he : (fun z : ℂ => (s+z-a)⁻¹) = (fun z => (1*z+(s-a))⁻¹) := by
    ext z; congr 1; ring
  rw [he]
  simpa only [signedTaylorMoment,one_pow,one_mul] using signedTaylorMoment_inv_linear n 1 (s-a)

/-- The exact remainder after a finite genuine divisor is subtracted.
The pole, regular correction and any unlisted zeros are not declared paid. -/
def regularPart (W : Finset NontrivialZetaZero) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s+ZetaRieszLocalXiDivisor.principalSum W s

private theorem principal_analytic (tau : NontrivialZetaZero) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => (analyticZetaZeroMultiplicity tau : ℂ)/(z-tau.1)) s := by
  apply analyticAt_const.div (analyticAt_id.sub analyticAt_const)
  apply Complex.ne_zero_of_re_pos
  have ht := NontrivialZetaZero.re_lt_one tau
  change 0 < s.re-tau.1.re
  linarith

private theorem principal_moment (W : Finset NontrivialZetaZero) {s : ℂ}
    (hs : 1 < s.re) (k : ℕ) :
    signedTaylorMoment k (ZetaRieszLocalXiDivisor.principalSum W) s =
      ∑ tau ∈ W, (analyticZetaZeroMultiplicity tau : ℂ)*((s-tau.1)⁻¹)^(k+1) := by
  unfold ZetaRieszLocalXiDivisor.principalSum
  rw [signedTaylorMoment_sum W k _ (fun tau _ => principal_analytic tau hs)]
  apply Finset.sum_congr rfl
  intro tau _htau
  rw [show (fun z => (analyticZetaZeroMultiplicity tau : ℂ)/(z-tau.1)) =
      (fun z => (analyticZetaZeroMultiplicity tau : ℂ)*(1/(z-tau.1))) by ext; ring,
    signedTaylorMoment_const_mul,reciprocal_moment]

theorem moment_principal_split (W : Finset NontrivialZetaZero) {s : ℂ}
    (hs : 1 < s.re) (k : ℕ) :
    zetaPrimeLogMoment k s = signedTaylorMoment k (regularPart W) s-
      ∑ tau ∈ W, (analyticZetaZeroMultiplicity tau : ℂ)*((s-tau.1)⁻¹)^(k+1) := by
  unfold regularPart
  have hp : AnalyticAt ℂ (ZetaRieszLocalXiDivisor.principalSum W) s :=
    Finset.analyticAt_fun_sum W (fun tau _ => principal_analytic tau hs)
  rw [signedTaylorMoment_add k
    (ZetaRieszShiftedCenter.analyticAt_zeta_logDeriv hs) hp,principal_moment W hs]
  simp only [zetaPrimeLogMoment,add_sub_cancel_right]

/-- On the chosen local divisor the retained remainder is exactly the
old zeta pole plus completion correction minus the analytic xi remainder. -/
theorem regularPart_local (rho : NontrivialZetaZero) (hrho : 1/2 < rho.1.re)
    {s : ℂ} (hs : 1 < s.re) :
    regularPart (ZetaRieszLocalXiDivisor.localDivisor rho.1.im
      (ZetaRieszLocalXiDivisor.radius rho hrho)) s =
      1/(s-1)+zetaGlobalRegularCorrection s-ZetaRieszLocalXiDivisor.localXiLogRemainder rho hrho s := by
  have hx : riemannXi s ≠ 0 := by
    intro he
    have h := NontrivialZetaZero.re_lt_one
      ⟨s,(riemannXi_eq_zero_iff_isNontrivialZetaZero s).mp he⟩
    linarith
  have h := (ZetaRieszLocalXiDivisor.localXiLogRemainder_spec rho hrho).2 s hx
  have hb := zeta_global_complex_budget hs
  unfold regularPart
  rw [h] at hb
  linear_combination hb

/-- The signed regular difference retains both marked frequencies. -/
def regularDifference (W : Finset NontrivialZetaZero) : ℕ → ℂ → ℝ → ℂ
  | 0, s, xi => logDifference 0 s xi
  | k+1, s, xi =>
    (signedTaylorMoment k (regularPart W) s-
      signedTaylorMoment k (regularPart W) (s+Complex.I*xi))/(k+1)

theorem logDifference_principal_split (W : Finset NontrivialZetaZero)
    (y xi : ℝ) {j : ℕ} (hj : 0 < j) :
    logDifference j (3/2+Complex.I*y) xi =
      regularDifference W j (3/2+Complex.I*y) xi-
      ∑ tau ∈ W, (analyticZetaZeroMultiplicity tau : ℂ)*
        modeDifference (tau.1-(3/2+Complex.I*y)) j xi := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  rw [logDifference,regularDifference,moment_principal_split W (by norm_num) k,
    moment_principal_split W (by norm_num) k]
  simp only [modeDifference]
  simp only [show ∀ tau : NontrivialZetaZero, -(tau.1-(3/2+Complex.I*(y : ℂ))) =
      3/2+Complex.I*y-tau.1 from fun tau => by ring,
    show ∀ tau : NontrivialZetaZero, Complex.I*(xi : ℂ)-(tau.1-(3/2+Complex.I*y)) =
      3/2+Complex.I*y+Complex.I*xi-tau.1 from fun tau => by ring]
  simp only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one]
  simp_rw [← mul_div_assoc,mul_sub,sub_div]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_div]
  ring

/-- A literal remaining marked symbol: the local regular part and all
unpaid nearby zeros. It contains the selected source and every cofactor. -/
def retainedSymbol (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    (regularDifference W j (3/2+Complex.I*y) xi-
      ∑ tau ∈ W \ farDivisor W y, (analyticZetaZeroMultiplicity tau : ℂ)*
        modeDifference (tau.1-(3/2+Complex.I*y)) j xi)*
      cofactor A N j h (3/2+Complex.I*y) xi

/-- The geometric term is an actual component of the existing signed
logarithmic-derivative symbol, with the correct negative residue sign. -/
theorem logSymbol_retained_split (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (N : ℕ) (y xi : ℝ) :
    logSymbol A N (3/2+Complex.I*y) xi = retainedSymbol W A N y xi-farSymbol W A N y xi := by
  have hs : farDivisor W y ⊆ W := Finset.filter_subset _ _
  have he : farSymbol W A N y xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        (∑ tau ∈ farDivisor W y, (analyticZetaZeroMultiplicity tau : ℂ)*
          modeDifference (tau.1-(3/2+Complex.I*y)) j xi)*
          cofactor A N j h (3/2+Complex.I*y) xi := by
    unfold farSymbol modeSymbol
    simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.sum_comm]
  rw [he,retainedSymbol,← Finset.sum_sub_distrib]
  unfold logSymbol
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [logDifference_principal_split W y xi (marked_order_pos hh)]
  have hsplit := Finset.sum_sdiff hs (f := fun tau => (analyticZetaZeroMultiplicity tau : ℂ)*
    modeDifference (tau.1-(3/2+Complex.I*y)) j xi)
  rw [← hsplit]
  ring

/-- Paying the small-band far principal parts changes no other frequency,
nearby zero, local regular term or arithmetic completion error. -/
def retainedMain (W : Finset NontrivialZetaZero) (u y : ℝ) (N : ℕ) : ℂ :=
  logMain u y N+farResponse W (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
    (SquarefreeVaughanLogSource.length u N)

/-- Explicit geometric cost for removing the paid sector from the exact
current logarithmic-derivative main. -/
theorem logMain_retained_bound (W : Finset NontrivialZetaZero) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-retainedMain W u y N)‖ ≤
      2*farMass W y*couplingConstant*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  unfold retainedMain
  rw [sub_add_cancel_left,mul_neg,norm_neg]
  exact farResponse_bound W _ (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N y
    (ZetaRieszHeadOrders.one_le_length u N) hu hU

/-- All earlier independently paid errors survive the subtraction.
This is the same literal packet, not a completed surrogate. The selected
resonance and the remaining independent floor/ceiling are still open. -/
theorem tendsto_retained_sub_current (W : Finset NontrivialZetaZero)
    {u : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (retainedMain W u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have hfar := (tendsto_farResponse W y (ZetaRieszRoughEulerTransfer.roughPrimes u)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp)
    (SquarefreeVaughanLogSource.length u) (ZetaRieszHeadOrders.one_le_length u)
    (by linarith : 0 ≤ u) hU).comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  have h := (tendsto_log_sub_current hu hU y).add hfar
  simp only [zero_add] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def,retainedMain]
  ring

/-- Horizontal separation survives every Fourier shift. -/
theorem horizontal_radius {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ)) (xi : ℝ) :
    (1001/2000 : ℝ) ≤ ‖z‖ ∧ (1001/2000 : ℝ) ≤ ‖Complex.I*xi-z‖ := by
  have ha := Complex.re_le_norm (-z)
  have hb := Complex.re_le_norm (Complex.I*(xi : ℂ)-z)
  simp only [Complex.neg_re,norm_neg] at ha
  norm_num only [Complex.sub_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,mul_one,zero_mul,sub_zero,zero_sub] at hb
  constructor <;> linarith

private theorem modeDifference_large {z : ℂ} {xi : ℝ}
    (hz : (1001/2000 : ℝ) ≤ ‖z‖) (hx : (1001/2000 : ℝ) ≤ ‖Complex.I*xi-z‖)
    {j : ℕ} (hj : 0 < j) :
    ‖modeDifference z j xi‖ ≤ 2*(1001/2000 : ℝ)⁻¹^j := by
  have ha : ‖(-z)⁻¹‖ ≤ (1001/2000 : ℝ)⁻¹ := by
    rw [norm_inv,norm_neg]
    exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr hz
  have hb : ‖(Complex.I*(xi : ℂ)-z)⁻¹‖ ≤ (1001/2000 : ℝ)⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr hx
  unfold modeDifference
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_self (norm_nonneg _) (by exact_mod_cast hj : (1 : ℝ) ≤ j)).trans
  apply (norm_sub_le _ _).trans
  simp only [norm_pow]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) ha j,pow_le_pow_left₀ (norm_nonneg _) hb j]

/-- The large-frequency constant is finite without a height hypothesis. -/
def couplingMassConstant : ℝ := 8*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)

theorem couplingMassConstant_nonneg : 0 ≤ couplingMassConstant := by
  unfold couplingMassConstant
  positivity [mass_nonneg (3/2-safeRadius)]

private theorem modeSymbol_large {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*modeSymbol z A N y xi‖ ≤
      couplingMassConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
  have hR := safeRadius_pos
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hmass := mass_nonneg (3/2-safeRadius)
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      mass (3/2-safeRadius)*2 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num)
  unfold modeSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _
    (B := couplingMassConstant*(9999/10000 : ℝ)^N)
    (by positivity [couplingMassConstant_nonneg]) ?_).trans_eq (by ring)
  intro j hj h hh
  have hm := modeDifference_large (horizontal_radius hz xi).1
    (horizontal_radius hz xi).2 (marked_order_pos hh)
  have hc := cofactor_bound A h16 N j h hh
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi
    (fun _ => 2) (fun _ => by norm_num) (fun p => ZetaRieszMainFrequency.phase_le_two p xi)
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hc
  have hc := hc.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,norm_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul hm hc (norm_nonneg _) (by positivity))
    (pow_nonneg hu _)).trans
  calc
    _ = (u^(N+1)*(1001/2000 : ℝ)⁻¹^j*safeRadius⁻¹^(N+1-j))*
        (4*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)) := by ring
    _ ≤ (2*(9999/10000 : ℝ)^N)*
        (4*Real.exp (4*mass (3/2-safeRadius))*mass (3/2-safeRadius)) :=
      mul_le_mul_of_nonneg_right (coupled_order_bound hu hU hj hh) (by positivity)
    _ = _ := by unfold couplingMassConstant; ring

/-- Both phases of one horizontally separated genuine principal part. -/
def modePair (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*modeSymbol z A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*modeSymbol z A N y (-xi)

/-- A common integrable envelope pays the entire Fourier axis. -/
theorem horizontal_pair_profile {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*(modePair z A N y L xi/(xi : ℂ)^2)‖ ≤
      (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)*
        (1+xi^2)⁻¹ := by
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*(Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*
      modeSymbol z A N y t)‖ = ‖(u : ℂ)^(N+1)*modeSymbol z A N y t‖ := by
    rw [mul_left_comm,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have hn : ‖(u : ℂ)^(N+1)*modePair z A N y L xi‖ ≤
      (2*couplingConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)*xi^2 := by
    unfold modePair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add
      (modeSymbol_bound_of_radii (horizontal_radius hz xi).1 A h16 N y (horizontal_radius hz xi).2 hu hU)
      (modeSymbol_bound_of_radii (horizontal_radius hz (-xi)).1 A h16 N y (horizontal_radius hz (-xi)).2 hu hU)).trans_eq
        (by rw [neg_sq]; ring)
  have hl : ‖(u : ℂ)^(N+1)*modePair z A N y L xi‖ ≤
      2*couplingMassConstant*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N := by
    unfold modePair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (modeSymbol_large hz A h16 N y xi hu hU)
      (modeSymbol_large hz A h16 N y (-xi) hu hU)).trans_eq (by ring)
  rw [← mul_div_assoc]
  exact (norm_div_square_profile (by positivity [couplingConstant_nonneg])
    (by positivity [couplingMassConstant_nonneg]) hn hl).trans_eq (by ring)

private theorem measurable_modePair (z : ℂ) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ => modePair z A N y L xi/(xi : ℂ)^2) := by
  have hm : Measurable (fun xi : ℝ => modeSymbol z A N y xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Measurable.mul _ (measurable_cofactor A h16 N j h (by norm_num [safeRadius]))
    unfold modeDifference
    fun_prop
  have hn := hm.comp measurable_neg
  unfold modePair
  fun_prop

theorem integrable_horizontal_pair {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(modePair z A N y L xi/(xi : ℂ)^2)) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N)).mono'
  · exact ((measurable_modePair z A h16 N y L).const_mul _).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => horizontal_pair_profile hz A h16 N y L xi hu hU)

/-- One separated principal part integrated over every frequency. -/
def horizontalResponse (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, modePair z A N y L xi/(xi : ℂ)^2

theorem horizontalResponse_bound {z : ℂ} (hz : z.re ≤ -(501/1000 : ℝ))
    (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*horizontalResponse z A N y L‖ ≤
      (Real.pi*(couplingConstant+couplingMassConstant))*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  have hc : 0 ≤ Real.pi*(couplingConstant+couplingMassConstant) := by
    positivity [couplingConstant_nonneg,couplingMassConstant_nonneg]
  have hi := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
      (2*(couplingConstant+couplingMassConstant)*((N : ℝ)+2)^2*(9999/10000 : ℝ)^N))
    (Eventually.of_forall (fun xi => horizontal_pair_profile hz A h16 N y L xi hu hU))
  simp only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] at hi
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold horizontalResponse
  rw [mul_left_comm,norm_mul]
  apply (mul_le_mul hpref hi (norm_nonneg _) (by positivity)).trans
  calc
    _ = ((N : ℝ)+1)*(Real.pi*(couplingConstant+couplingMassConstant)*
        ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N) := by ring
    _ ≤ ((N : ℝ)+2)*(Real.pi*(couplingConstant+couplingMassConstant)*
        ((N : ℝ)+2)^2*(9999/10000 : ℝ)^N) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = _ := by ring

/-- Genuine zeros with beta<=999/1000 have no unpaid exterior frequency. -/
def horizontalDivisor (W : Finset NontrivialZetaZero) : Finset NontrivialZetaZero :=
  W.filter (fun tau => tau.1.re ≤ (999/1000 : ℝ))

theorem selected_not_horizontal (W : Finset NontrivialZetaZero) (rho : NontrivialZetaZero)
    (hu : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    rho ∉ horizontalDivisor W := by
  intro h
  have ht := (Finset.mem_filter.mp h).2
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hu
  linarith

theorem farDivisor_horizontal (W : Finset NontrivialZetaZero) (y : ℝ) :
    farDivisor (horizontalDivisor W) y = horizontalDivisor W := by
  apply Finset.filter_eq_self.mpr
  intro tau htau
  have ht := (Finset.mem_filter.mp htau).2
  have hn := Complex.re_le_norm (3/2+Complex.I*(y : ℂ)-tau.1)
  rw [Complex.sub_re,show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num,
    norm_sub_rev] at hn
  linarith

/-- Full-frequency payment with each actual multiplicity retained. -/
def horizontalContribution (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (N : ℕ) (y L : ℝ) : ℂ :=
  ∑ tau ∈ horizontalDivisor W, (analyticZetaZeroMultiplicity tau : ℂ)*
    horizontalResponse (tau.1-(3/2+Complex.I*y)) A N y L

/-- The finite sum is literally the principal-part integral; every
summand is integrable before the finite sum is exchanged. -/
theorem horizontalContribution_eq_integral (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L : ℝ) :
    horizontalContribution W A N y L =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
      ∫ xi : ℝ in Ioi 0, ∑ tau ∈ horizontalDivisor W,
        (analyticZetaZeroMultiplicity tau : ℂ)*
          (modePair (tau.1-(3/2+Complex.I*y)) A N y L xi/(xi : ℂ)^2) := by
  have hi (tau : NontrivialZetaZero) (htau : tau ∈ horizontalDivisor W) :
      IntegrableOn (fun xi : ℝ => modePair (tau.1-(3/2+Complex.I*y)) A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
    have hz : (tau.1-(3/2+Complex.I*(y : ℂ))).re ≤ -(501/1000 : ℝ) := by
      have ht := (Finset.mem_filter.mp htau).2
      rw [Complex.sub_re,show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num]
      linarith
    have hscaled := integrable_horizontal_pair hz A h16 N y L (u := 1/2) (by norm_num)
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    have hunit : IsUnit (((1/2 : ℝ) : ℂ)^(N+1)) :=
      isUnit_iff_ne_zero.mpr (pow_ne_zero (N+1) (by norm_num))
    exact (integrable_const_mul_iff (μ := volume.restrict (Ioi (0 : ℝ))) hunit
      (fun xi : ℝ => modePair (tau.1-(3/2+Complex.I*y)) A N y L xi/(xi : ℂ)^2)).mp hscaled
  rw [integral_finsetSum _ (fun tau htau => (hi tau htau).const_mul _)]
  simp only [horizontalContribution,horizontalResponse,integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tau _htau
  ring

/-- The constant for the union of two disjoint paid sectors. -/
def paidConstant (W : Finset NontrivialZetaZero) (y : ℝ) : ℝ :=
  (∑ tau ∈ horizontalDivisor W, (analyticZetaZeroMultiplicity tau : ℝ))*
    (Real.pi*(couplingConstant+couplingMassConstant))+
      2*farMass (W \ horizontalDivisor W) y*couplingConstant

theorem horizontalContribution_bound (W : Finset NontrivialZetaZero) (A : Finset ℕ)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ‖(u : ℂ)^(N+1)*horizontalContribution W A N y L‖ ≤
      ((∑ tau ∈ horizontalDivisor W, (analyticZetaZeroMultiplicity tau : ℝ))*
        (Real.pi*(couplingConstant+couplingMassConstant)))*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  unfold horizontalContribution
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ tau ∈ horizontalDivisor W, (analyticZetaZeroMultiplicity tau : ℝ)*
        ((Real.pi*(couplingConstant+couplingMassConstant))*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N) := by
      apply Finset.sum_le_sum
      intro tau htau
      have hz : (tau.1-(3/2+Complex.I*(y : ℂ))).re ≤ -(501/1000 : ℝ) := by
        have ht := (Finset.mem_filter.mp htau).2
        rw [Complex.sub_re,show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num]
        linarith
      rw [mul_left_comm,norm_mul,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (horizontalResponse_bound hz A h16 N y hL hu hU) (by positivity)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The horizontal and small-frequency sectors are disjoint: modes paid
on the whole axis are deleted before the band payment. -/
def reducedMain (W : Finset NontrivialZetaZero) (u y : ℝ) (N : ℕ) : ℂ :=
  retainedMain (W \ horizontalDivisor W) u y N+
    horizontalContribution W (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
      (SquarefreeVaughanLogSource.length u N)

theorem logMain_reduced_bound (W : Finset NontrivialZetaZero) {u : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (N : ℕ) :
    ‖(u : ℂ)^(N+1)*(logMain u y N-reducedMain W u y N)‖ ≤
      paidConstant W y*((N : ℝ)+2)^3*(9999/10000 : ℝ)^N := by
  unfold reducedMain
  rw [sub_add_eq_sub_sub,mul_sub]
  apply (norm_sub_le _ _).trans
  exact (add_le_add (logMain_retained_bound (W \ horizontalDivisor W) hu hU y N)
    (horizontalContribution_bound W _ (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp)
      N y (ZetaRieszHeadOrders.one_le_length u N) hu hU)).trans_eq (by unfold paidConstant; ring)

/-- Both sector payments preserve the original literal-packet ledger and
every previous paid error. No bound on the remaining signed main is asserted. -/
theorem tendsto_reduced_sub_current (W : Finset NontrivialZetaZero) {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (reducedMain W u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9999/10000) (by norm_num : (9999/10000 : ℝ) < 1)
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*(9999/10000 : ℝ)^N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
    · ext N; simp only [pow_zero,pow_one]; ring
    · norm_num
  have he : Tendsto (fun N => (u : ℂ)^(N+1)*(logMain u y N-reducedMain W u y N))
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => paidConstant W y*(((N : ℝ)+2)^3*(9999/10000 : ℝ)^N))
    · intro N
      simpa only [mul_assoc] using logMain_reduced_bound W (by linarith : 0 ≤ u) hU y N
    · simpa only [mul_zero] using ht.const_mul (paidConstant W y)
  have h := (tendsto_log_sub_current hu hU y).sub
    (he.comp ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_zero] at h
  convert h using 1
  ext j
  dsimp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszExposedModeCoupling
