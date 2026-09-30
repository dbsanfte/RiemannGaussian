/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnshiftedPayment

/-!
# Joint payment of every unshifted logarithmic-derivative channel

Exposure bounds the actual complete moments, with all zeros, the pole and
the regular terms still included. Composite saturation then pays their
entire unshifted cofactor response. No prime-leg limit is transferred
through a share mask, and the shifted logarithmic derivative remains signed.
-/

namespace RiemannGaussian.ZetaRieszUnshiftedLogPayment
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszMarkedPrimeCompletion
open ZetaRieszMarkedLogDerivative ZetaRieszMarkedSeparation ZetaRieszSkewAllocation
open ZetaRieszUnshiftedCofactor ZetaRieszUnshiftedCharacter
open ZetaRieszUnshiftedEulerError
open ZetaRieszOrderedEulerBound

/-- The complete von Mangoldt moment at the original positive marked
order. The unused zero order does not delete any cofactor allocation. -/
def momentMark : ℕ → ℂ → ℂ
  | 0, _ => 0
  | k+1, s => zetaPrimeLogMoment k s/(k+1)

theorem logDifference_eq {j : ℕ} (hj : 0 < j) (s : ℂ) (xi : ℝ) :
    logDifference j s xi = momentMark j s-momentMark j (s+Complex.I*xi) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  simp only [logDifference,momentMark,sub_div]

/-- The existing complete-moment theorem discharges the coefficient
budget, without simplicity, a global rightmost zero or a masked phase limit. -/
theorem exists_normalized_mark_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      ‖((3/2-rho.1.re : ℝ) : ℂ)^j*momentMark j (3/2+Complex.I*rho.1.im)‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := ZetaExposedPrimeMoments.exists_normalized_prime_moment_bound rho hrho hexposed
  refine ⟨C,hC,?_⟩
  intro j
  cases j with
  | zero => simpa only [momentMark,mul_zero,norm_zero] using hC
  | succ k =>
    rw [momentMark,← mul_div_assoc,norm_div]
    have hk : 1 ≤ ‖((k : ℂ)+1)‖ := by norm_cast; omega
    exact (div_le_self (norm_nonneg _) hk).trans (hb k)

/-- A bounded marked coefficient leaves exactly the complementary
source power; no moving cofactor coefficient is assumed polynomial. -/
theorem scaled_mark_bound {u C : ℝ} (hu : 0 < u) {a : ℂ} {N j : ℕ}
    (hj : j ≤ N+1) (hb : ‖(u : ℂ)^j*a‖ ≤ C) :
    ‖(u : ℂ)^(N+1)*a‖ ≤ C*u^(N+1-j) := by
  have he : (u : ℂ)^(N+1)*a = (u : ℂ)^(N+1-j)*((u : ℂ)^j*a) := by
    rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hj]
  rw [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hu.le _)).trans_eq (mul_comm _ _)

/-- The unshifted half of the actual completed logarithmic derivative. -/
def unshiftedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    momentMark j s*cofactor A N j h s xi

/-- The remaining full shifted moment, still coupled to its original
ordered cofactor and factorial rectangle at both Fourier frequencies. -/
def shiftedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    momentMark j (s+Complex.I*xi)*cofactor A N j h s xi

theorem logSymbol_split (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    logSymbol A N s xi = unshiftedSymbol A N s xi-shiftedSymbol A N s xi := by
  unfold logSymbol unshiftedSymbol shiftedSymbol
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [logDifference_eq (marked_order_pos hh),sub_mul]

/-- The finite character after its exact signed Fourier integral. -/
def characterResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  -((N+1 : ℕ) : ℂ)/(L : ℂ)*∑ j ∈ Finset.range (N+2),
    momentMark j (3/2+Complex.I*y)*orderResponse (labels A) N j L (3/2+Complex.I*y)

theorem characterResponse_bound (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (y : ℝ) {u L C : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hL0 : 0 < L)
    (hL : (11/8 : ℝ)*N ≤ L) (hC : 0 ≤ C)
    (hb : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    ‖(u : ℂ)^(N+1)*characterResponse A N y L‖ ≤
      C*(3*divisorSquareDirichletMass (1025/1024)*((N : ℝ)+1)*((N : ℝ)+2)*
        Real.exp (-(N : ℝ)/100)) := by
  have hmass := divisorSquareDirichletMass_nonneg (1025/1024)
  have hatom (j : ℕ) (hj : j ∈ Finset.range (N+2)) :
      ‖(u : ℂ)^(N+1)*(momentMark j (3/2+Complex.I*y)*
        orderResponse (labels A) N j L (3/2+Complex.I*y))‖ ≤
          C*(3*L*divisorSquareDirichletMass (1025/1024)*Real.exp (-(N : ℝ)/100)) := by
    by_cases hempty : rectangleOrders N j = ∅
    · simp only [orderResponse,allocationKernel_eq_zero hempty,mul_zero,Finset.sum_const_zero,norm_zero]
      positivity
    obtain ⟨h,hh⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hjM : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
    rw [← mul_assoc,norm_mul]
    apply (mul_le_mul (scaled_mark_bound hu hjM (hb j))
      (orderResponse_bound _ (fun _ ha => labels_data hA ha) N j y hL0.le)
      (norm_nonneg _) (by positivity)).trans
    calc
      _ = C*(u^(N+1-j)*(1024/255 : ℝ)^(N+1-j)*Real.exp (-L/4))*
          (L*divisorSquareDirichletMass (1025/1024)) := by ring
      _ ≤ C*(3*Real.exp (-(N : ℝ)/100))*(L*divisorSquareDirichletMass (1025/1024)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (complementary_rate hj hh hu hU hL) hC) (by positivity)
      _ = _ := by ring
  have hsum : ‖(u : ℂ)^(N+1)*(∑ j ∈ Finset.range (N+2),
      momentMark j (3/2+Complex.I*y)*orderResponse (labels A) N j L (3/2+Complex.I*y))‖ ≤
        ((N : ℝ)+2)*(C*(3*L*divisorSquareDirichletMass (1025/1024)*Real.exp (-(N : ℝ)/100))) := by
    rw [Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum hatom).trans_eq
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  unfold characterResponse
  rw [mul_left_comm,norm_mul,norm_div,norm_neg,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  push_cast
  field_simp

/-- The full Euler correction with the actual unshifted complete moment. -/
def errorSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    momentMark j (3/2+Complex.I*y)*
      ZetaRieszUnshiftedEulerError.errorCofactor A N j h (3/2+Complex.I*y) xi

theorem errorSymbol_bound (A : Finset ℕ) (N : ℕ) (y xi : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ Finset.range (N+2), ∀ h ∈ rectangleOrders N j,
      ‖ZetaRieszUnshiftedEulerError.errorCofactor A N j h (3/2+Complex.I*y) xi‖ ≤
        B*Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j)) :
    ‖(u : ℂ)^(N+1)*errorSymbol A N y xi‖ ≤
      C*(2*B*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) := by
  unfold errorSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _ (B := C*(2*B*Real.exp (-(N : ℝ)/300)))
    (by positivity) ?_).trans_eq (by ring)
  intro j hj h hh
  have hjM : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  rw [← mul_assoc,norm_mul]
  apply (mul_le_mul (scaled_mark_bound hu hjM (hc j)) (hb j hj h hh)
    (norm_nonneg _) (by positivity)).trans
  calc
    _ = (C*B)*(u^(N+1-j)*safeRadius⁻¹^(N+1-j)*Real.exp (-(N : ℝ)/220)) := by ring
    _ ≤ (C*B)*(2*Real.exp (-(N : ℝ)/300)) :=
      mul_le_mul_of_nonneg_left
        (ZetaRieszUnshiftedEulerError.error_source_rate hu hU (N := N) (k := N+1-j) (by omega))
        (mul_nonneg hC hB)
    _ = _ := by ring

/-- Both signed frequencies of the unshifted complete-moment correction. -/
def errorPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*errorSymbol A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*errorSymbol A N y (-xi)

theorem errorPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L xi : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    ‖(u : ℂ)^(N+1)*(errorPair A N y L xi/(xi : ℂ)^2)‖ ≤
      (C*(4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)))*(1+xi^2)⁻¹ := by
  have hsmall (t : ℝ) : ‖(u : ℂ)^(N+1)*errorSymbol A N y t‖ ≤
      (C*(2*smallConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)))*t^2 := by
    have he := errorSymbol_bound A N y t hu hU hC hc
      (mul_nonneg smallConstant_nonneg (sq_nonneg t))
      (fun j _ h hh => (errorCofactor_small A h16 N j h hh hhead y t).trans_eq
        (by unfold smallConstant; ring))
    exact he.trans_eq (by ring)
  have hlarge (t : ℝ) : ‖(u : ℂ)^(N+1)*errorSymbol A N y t‖ ≤
      C*(2*largeConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) :=
    errorSymbol_bound A N y t hu hU hC hc largeConstant_nonneg
      (fun j _ h hh => errorCofactor_large A h16 N j h hh hhead y t)
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*(Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*
      errorSymbol A N y t)‖ = ‖(u : ℂ)^(N+1)*errorSymbol A N y t‖ := by
    rw [mul_left_comm,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have hn : ‖(u : ℂ)^(N+1)*errorPair A N y L xi‖ ≤
      (C*(4*smallConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)))*xi^2 := by
    unfold errorPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (hsmall xi) (hsmall (-xi))).trans_eq (by rw [neg_sq]; ring)
  have hl : ‖(u : ℂ)^(N+1)*errorPair A N y L xi‖ ≤
      C*(4*largeConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) := by
    unfold errorPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (hlarge xi) (hlarge (-xi))).trans_eq (by ring)
  rw [← mul_div_assoc]
  exact (norm_div_square_profile (by positivity [smallConstant_nonneg])
    (by positivity [largeConstant_nonneg]) hn hl).trans_eq (by ring)

theorem measurable_errorPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    StronglyMeasurable (fun xi : ℝ => errorPair A N y L xi/(xi : ℂ)^2) := by
  have hm (j h : ℕ) : Measurable (fun xi : ℝ => errorCofactor A N j h (3/2+Complex.I*y) xi) := by
    apply Finset.measurable_fun_sum
    intro r _hr
    have he := (measurable_error_moment (tailPrimes A r)
      (fun p hp => h16 p (Finset.mem_filter.mp hp).1) (s := 3/2+Complex.I*y)
      safeRadius_pos (by norm_num [safeRadius]) (N+1-j-h)).measurable
    simp only [coeff_leg]
    unfold zetaPrimeFeature
    fun_prop
  have hsymbol : Measurable (fun xi : ℝ => errorSymbol A N y xi) := by
    unfold errorSymbol
    fun_prop
  have hneg := hsymbol.comp measurable_neg
  apply Measurable.stronglyMeasurable
  unfold errorPair
  fun_prop

theorem integrable_errorPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    IntegrableOn (fun xi : ℝ => errorPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  have he : IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(errorPair A N y L xi/(xi : ℂ)^2))
      (Ioi 0) := by
    apply ((integrable_inv_one_add_sq.integrableOn).const_mul
      (C*(4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)))).mono'
    · exact ((measurable_errorPair A h16 N y L).const_mul _).aestronglyMeasurable
    · exact Eventually.of_forall (fun xi => errorPair_profile A h16 N hhead y L xi hu hU hC hc)
  have hpow : (u : ℂ)^(N+1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne')
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hpow)
    (f := fun xi : ℝ => errorPair A N y L xi/(xi : ℂ)^2)).mp he

/-- The full-frequency Euler error with its unchanged Riesz prefactor. -/
def errorResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, errorPair A N y L xi/(xi : ℂ)^2

theorem errorResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y : ℝ)
    {L u C : ℝ} (hL : 1 ≤ L) (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    ‖(u : ℂ)^(N+1)*errorResponse A N y L‖ ≤
      C*((2*Real.pi*(smallConstant+largeConstant))*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)) := by
  have hi := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
      (C*(4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))))
    (Eventually.of_forall (fun xi => errorPair_profile A h16 N hhead y L xi hu hU hC hc))
  simp only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] at hi
  have hL0 : 0 < L := by linarith
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) (by nlinarith [Real.pi_gt_three])
  unfold errorResponse
  rw [mul_left_comm,norm_mul]
  apply (mul_le_mul hpref hi (norm_nonneg _) (by positivity)).trans
  calc
    _ = ((N : ℝ)+1)*(C*(2*Real.pi*(smallConstant+largeConstant)*
        ((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))) := by ring
    _ ≤ ((N : ℝ)+2)*(C*(2*Real.pi*(smallConstant+largeConstant)*
        ((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity [smallConstant_nonneg,largeConstant_nonneg]
    _ = _ := by ring

/-- The unshifted logarithmic moment with both original Fourier phases. -/
def unshiftedPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*unshiftedSymbol A N (3/2+Complex.I*y) xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*unshiftedSymbol A N (3/2+Complex.I*y) (-xi)

/-- The entire shifted logarithmic moment, with its cofactor unchanged. -/
def shiftedPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*shiftedSymbol A N (3/2+Complex.I*y) xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*shiftedSymbol A N (3/2+Complex.I*y) (-xi)

theorem logPair_split (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) :
    logPair A N (3/2+Complex.I*y) L xi = unshiftedPair A N y L xi-shiftedPair A N y L xi := by
  simp only [logPair,logSymbol_split,unshiftedPair,shiftedPair]
  ring

/-- The corresponding finite-character pair before its exact integration. -/
def characterPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), momentMark j (3/2+Complex.I*y)*
    ZetaRieszUnshiftedCharacter.characterPair A N j (3/2+Complex.I*y) L xi

theorem unshiftedPair_split (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L xi : ℝ) :
    unshiftedPair A N y L xi = characterPair A N y L xi-errorPair A N y L xi := by
  simp only [unshiftedPair,unshiftedSymbol,characterPair,ZetaRieszUnshiftedCharacter.characterPair,
    ZetaRieszUnshiftedPayment.characterCofactor_split A h16 N _
      (by norm_num : 1/2 ≤ (3/2+Complex.I*(y : ℂ)).re),errorPair,errorSymbol]
  have hep : Complex.exp (Complex.I*(xi : ℂ)*(L : ℂ)) =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I) := by congr 1; push_cast; ring
  have hen : Complex.exp (-(Complex.I*(xi : ℂ)*(L : ℂ))) =
      Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I) := by congr 1; push_cast; ring
  rw [hep,hen]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  ring

theorem integrable_characterPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => characterPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  simp_rw [characterPair,Finset.sum_div,mul_div_assoc]
  exact integrable_finsetSum _ (fun j _ =>
    (ZetaRieszUnshiftedCharacter.characterPair_integrable A hA N j (3/2+Complex.I*y) L).const_mul _)

theorem integrable_unshiftedPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    IntegrableOn (fun xi : ℝ => unshiftedPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  simp_rw [unshiftedPair_split A h16,sub_div]
  exact (integrable_characterPair A hA N y L).sub
    (integrable_errorPair A h16 N hhead y L hu hU hC hc)

/-- The full unshifted response at the original finite support and length. -/
def unshiftedResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, unshiftedPair A N y L xi/(xi : ℂ)^2

theorem characterPair_integral (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (y L : ℝ) :
    ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
      (∫ xi : ℝ in Ioi 0, characterPair A N y L xi/(xi : ℂ)^2) = characterResponse A N y L := by
  simp_rw [characterPair,Finset.sum_div,mul_div_assoc]
  rw [integral_finsetSum _ (fun j _ =>
    (ZetaRieszUnshiftedCharacter.characterPair_integrable A hA N j (3/2+Complex.I*y) L).const_mul _)]
  simp_rw [integral_const_mul]
  unfold characterResponse
  simp_rw [← ZetaRieszUnshiftedCharacter.characterPair_integral A hA]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem unshiftedResponse_eq (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    unshiftedResponse A N y L = characterResponse A N y L-errorResponse A N y L := by
  unfold unshiftedResponse
  simp_rw [unshiftedPair_split A h16,sub_div]
  rw [integral_sub (integrable_characterPair A hA N y L)
    (integrable_errorPair A h16 N hhead y L hu hU hC hc),mul_sub,characterPair_integral A hA]
  rfl

/-- One geometric bound pays the whole unshifted complete-moment
contribution, including every pole, zero and regular channel jointly. -/
theorem unshiftedResponse_bound (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y : ℝ)
    {L u C : ℝ} (hL : 1 ≤ L) (hlen : (11/8 : ℝ)*N ≤ L)
    (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    ‖(u : ℂ)^(N+1)*unshiftedResponse A N y L‖ ≤
      (C*ZetaRieszUnshiftedPayment.paymentConstant)*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
  rw [unshiftedResponse_eq A hA h16 N hhead y L hu hU hC hc,mul_sub]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (characterResponse_bound A hA N y hu hU (by linarith) hlen hC hc)
    (errorResponse_bound A h16 N hhead y hL hu hU hC hc)).trans
  have he : Real.exp (-(N : ℝ)/100) ≤ Real.exp (-(N : ℝ)/300) :=
    Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hp : ((N : ℝ)+1)*((N : ℝ)+2) ≤ ((N : ℝ)+2)^3 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N,sq_nonneg ((N : ℝ)+2)]
  unfold ZetaRieszUnshiftedPayment.paymentConstant
  calc
    _ ≤ C*(3*divisorSquareDirichletMass (1025/1024)*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300))+
        C*((2*Real.pi*(smallConstant+largeConstant))*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ hC
      rw [mul_assoc (3*_) ((N : ℝ)+1)]
      have hD := divisorSquareDirichletMass_nonneg (1025/1024)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- At an actual exposed zero the complete-moment budget is proved,
so the whole unshifted term has an eventual geometric payment. -/
theorem exists_exposed_unshifted_bound (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ‖((3/2-rho.1.re : ℝ) : ℂ)^(N+1)*unshiftedResponse
        (ZetaRieszRoughEulerTransfer.roughPrimes (3/2-rho.1.re) N) N rho.1.im
        (SquarefreeVaughanLogSource.length (3/2-rho.1.re) N)‖ ≤
          B*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
  obtain ⟨C,hC,hc⟩ := exists_normalized_mark_bound rho hrho hexposed
  refine ⟨C*ZetaRieszUnshiftedPayment.paymentConstant,
    mul_nonneg hC ZetaRieszUnshiftedPayment.paymentConstant_nonneg,?_⟩
  have hu : 0 < (3/2-rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he : (3/2-rho.1.re : ℝ) < Real.exp (-((11/8 : ℝ)/2)) := by
    rw [show ((11/8 : ℝ)/2) = 11/16 by norm_num]
    exact hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ (11/8)/2) he] with N hN
  exact unshiftedResponse_bound _
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_head hp) rho.1.im
    (ZetaRieszHeadOrders.one_le_length _ N) (by nlinarith [hN]) hu hU hC hc

/-- All unshifted channels decay jointly. The selected zero may have
any analytic multiplicity; its shifted resonance has not been estimated. -/
theorem tendsto_exposed_unshifted (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => ((3/2-rho.1.re : ℝ) : ℂ)^(N+1)*unshiftedResponse
      (ZetaRieszRoughEulerTransfer.roughPrimes (3/2-rho.1.re) N) N rho.1.im
      (SquarefreeVaughanLogSource.length (3/2-rho.1.re) N)) atTop (nhds 0) := by
  obtain ⟨B,_hB,hb⟩ := exists_exposed_unshifted_bound rho hrho hexposed hU
  apply squeeze_zero_norm' (a := fun N : ℕ => B*(((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)))
  · simpa only [mul_assoc] using hb
  · simpa only [mul_zero] using ZetaRieszUnshiftedPayment.tendsto_cubic_exp.const_mul B

/-- Integrability of the original logarithmic response follows from
the already paid prime completion and proper-power terms. -/
theorem integrable_logPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => logPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2) (Ioi 0) := by
  have hs : 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius := by norm_num [safeRadius]
  simp_rw [ZetaRieszMarkedLogDerivative.logPair_split A N
    (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div,
    completedPair_split A hA N (by norm_num : 1 < (3/2+Complex.I*(y : ℂ)).re),add_div]
  exact ((integrable_separatedPair A hA h16 N hhead safeRadius_pos hs L).add
    (ZetaRieszMarkedPrimeCompletion.integrable_completionPair A h16 N hgap hs L)).add
    (integrable_properPair A h16 N y L)

/-- The shifted response keeps the complete logarithmic moment, full
frequency dependence and the unchanged correlated ordered cofactor. -/
def shiftedResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, shiftedPair A N y L xi/(xi : ℂ)^2

/-- Actual integrability licenses the split; no formal subtraction of
undefined Fourier integrals is used. -/
theorem logResponse_eq (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p) (y L : ℝ)
    {u C : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hC : 0 ≤ C) (hc : ∀ j, ‖(u : ℂ)^j*momentMark j (3/2+Complex.I*y)‖ ≤ C) :
    logResponse A N (3/2+Complex.I*y) L = unshiftedResponse A N y L-shiftedResponse A N y L := by
  have hi := integrable_unshiftedPair A hA h16 N hhead y L hu hU hC hc
  have hs : IntegrableOn (fun xi : ℝ => shiftedPair A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
    convert hi.sub (integrable_logPair A hA h16 N hhead hgap y L) using 1
    ext xi
    dsimp only [Pi.sub_apply]
    rw [logPair_split]
    ring
  unfold logResponse unshiftedResponse shiftedResponse
  simp_rw [logPair_split,sub_div]
  rw [integral_sub hi hs,mul_sub]

/-- The remaining signed main after paying every unshifted complete
channel. This is the same cofactor and moving Riesz length. -/
def shiftedMain (u y : ℝ) (N : ℕ) : ℂ :=
  -shiftedResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y
    (SquarefreeVaughanLogSource.length u N)

theorem tendsto_shifted_sub_log (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => ((3/2-rho.1.re : ℝ) : ℂ)^(N+1)*
      (shiftedMain (3/2-rho.1.re) rho.1.im N-logMain (3/2-rho.1.re) rho.1.im N))
      atTop (nhds 0) := by
  obtain ⟨C,hC,hc⟩ := exists_normalized_mark_bound rho hrho hexposed
  have hu : 0 < (3/2-rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have ht := (tendsto_exposed_unshifted rho hrho hexposed hU).neg
  simp only [neg_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_rough_support hu hU] with N hgap
  rw [logMain,logResponse_eq _
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_head hp) hgap rho.1.im _ hu hU hC hc]
  unfold shiftedMain
  ring

/-- Terminal literal transfer. All previous finite-prime, factorial,
allocation and exterior errors are retained. No signed floor or ceiling
for this surviving shifted expression is asserted. -/
theorem tendsto_shifted_sub_current (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*rho.1.im)-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun j => ((3/2-rho.1.re : ℝ) : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (shiftedMain (3/2-rho.1.re) rho.1.im (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket (3/2-rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket (3/2-rho.1.re) rho.1.im
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have hu : 1/2 < (3/2-rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have he := ((tendsto_shifted_sub_log rho hrho hexposed hU).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add (tendsto_log_sub_current hu hU rho.1.im)
  simp only [zero_add] at he
  convert he using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszUnshiftedLogPayment
