/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnshiftedCharacter
import RiemannGaussian.ZetaRieszUnshiftedEulerError

/-!
# Paying the unshifted selected mode in the retained Euler carrier

Composite saturation pays the finite character, and the full Euler
correction supplies the second Fourier zero needed to transfer that bound.
The shifted mode remains signed. This is not a bound on that remaining mode.
-/

namespace RiemannGaussian.ZetaRieszUnshiftedPayment
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszMarkedPrimeCompletion
open ZetaRieszMarkedSeparation ZetaRieszSkewAllocation
open ZetaRieszUnshiftedCofactor ZetaRieszUnshiftedCharacter ZetaRieszUnshiftedEulerError

/-- This is the unshifted half of the existing principal-part symbol,
with exactly the original Euler cofactor. -/
def unshiftedSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    ((-z)⁻¹)^j/(j : ℂ)*cofactor A N j h (3/2+Complex.I*y) xi

/-- The shifted half retains its frequency/cofactor correlation. -/
def shiftedSymbol (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    ((Complex.I*xi-z)⁻¹)^j/(j : ℂ)*cofactor A N j h (3/2+Complex.I*y) xi

theorem modeSymbol_split (z : ℂ) (A : Finset ℕ) (N : ℕ) (y xi : ℝ) :
    ZetaRieszExposedModeCoupling.modeSymbol z A N y xi =
      unshiftedSymbol z A N y xi-shiftedSymbol z A N y xi := by
  simp only [ZetaRieszExposedModeCoupling.modeSymbol,ZetaRieszExposedModeCoupling.modeDifference,
    sub_div,sub_mul,Finset.sum_sub_distrib,unshiftedSymbol,shiftedSymbol]

/-- The finite character and actual quotient differ by exactly the
previously bounded middle error at every original factorial order. -/
theorem characterCofactor_split (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    characterCofactor A N j s xi =
      (∑ h ∈ rectangleOrders N j, cofactor A N j h s xi)+
        ∑ h ∈ rectangleOrders N j, errorCofactor A N j h s xi := by
  simp only [characterCofactor,cofactor,errorCofactor,← Finset.sum_add_distrib,coeff_character]
  apply Finset.sum_congr rfl
  intro h _hh
  apply Finset.sum_congr rfl
  intro r _hr
  have he : signedTaylorMoment (N+1-j-h) (error (tailPrimes A r) xi) s =
      signedTaylorMoment (N+1-j-h) (character (tailPrimes A r) xi) s-
        signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s :=
    signedTaylorMoment_sub _ (analyticAt_character _ _ _) (analyticAt_quotient _
      (fun p hp => h16 p (Finset.mem_filter.mp hp).1) hs xi)
  rw [he]
  ring

/-- The original paired frequencies with only the unshifted marked term. -/
def unshiftedPair (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*unshiftedSymbol z A N y xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*unshiftedSymbol z A N y (-xi)

/-- Its exact finite-character counterpart at the same factorial orders. -/
def characterModePair (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ((-z)⁻¹)^j/(j : ℂ)*
    characterPair A N j (3/2+Complex.I*y) L xi

/-- The exact paired quotient identity, with no unestimated correction. -/
theorem unshiftedPair_split (z : ℂ) (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L xi : ℝ) :
    unshiftedPair z A N y L xi = characterModePair z A N y L xi-
      errorPair A N y L xi z := by
  simp only [unshiftedPair,unshiftedSymbol,characterModePair,characterPair,
    characterCofactor_split A h16 N _ (by norm_num : 1/2 ≤ (3/2+Complex.I*(y : ℂ)).re),
    errorPair,errorSymbol]
  have hep : Complex.exp (Complex.I*(xi : ℂ)*(L : ℂ)) =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I) := by congr 1; push_cast; ring
  have hen : Complex.exp (-(Complex.I*(xi : ℂ)*(L : ℂ))) =
      Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I) := by congr 1; push_cast; ring
  rw [hep,hen]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
  ring

theorem characterModePair_integrable (z : ℂ) (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ => characterModePair z A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  simp_rw [characterModePair,Finset.sum_div,mul_div_assoc]
  exact integrable_finsetSum _ (fun j _ =>
    (characterPair_integrable A hA N j (3/2+Complex.I*y) L).const_mul _)

theorem unshiftedPair_integrable (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    IntegrableOn (fun xi : ℝ => unshiftedPair z A N y L xi/(xi : ℂ)^2) (Ioi 0) := by
  have he := integrable_errorPair A h16 N hhead y L hu hU hz
  have hpow : (u : ℂ)^(N+1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne')
  have hei := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hpow)
    (f := fun xi : ℝ => errorPair A N y L xi z/(xi : ℂ)^2)).mp he
  simp_rw [unshiftedPair_split z A h16,sub_div]
  exact (characterModePair_integrable z A hA N y L).sub hei

/-- The unshifted half of the original full-frequency mode response. -/
def quotientResponse (z : ℂ) (A : Finset ℕ) (N : ℕ) (y L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, unshiftedPair z A N y L xi/(xi : ℂ)^2

theorem characterModePair_integral (z : ℂ) (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (y L : ℝ) :
    ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
      (∫ xi : ℝ in Ioi 0, characterModePair z A N y L xi/(xi : ℂ)^2) =
        unshiftedResponse (labels A) N L y z := by
  simp_rw [characterModePair,Finset.sum_div,mul_div_assoc]
  rw [integral_finsetSum _ (fun j _ =>
    (characterPair_integrable A hA N j (3/2+Complex.I*y) L).const_mul _)]
  simp_rw [integral_const_mul]
  unfold unshiftedResponse
  simp_rw [← characterPair_integral A hA]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Composite saturation plus the paid Euler correction is an exact
decomposition of the current quotient response, not a new completion. -/
theorem quotientResponse_eq (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    quotientResponse z A N y L = unshiftedResponse (labels A) N L y z-errorResponse A N y L z := by
  have he := integrable_errorPair A h16 N hhead y L hu hU hz
  have hpow : (u : ℂ)^(N+1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne')
  have hei := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hpow)
    (f := fun xi : ℝ => errorPair A N y L xi z/(xi : ℂ)^2)).mp he
  unfold quotientResponse
  simp_rw [unshiftedPair_split z A h16,sub_div]
  rw [integral_sub (characterModePair_integrable z A hA N y L) hei,mul_sub,
    characterModePair_integral z A hA]
  rfl

/-- Concrete geometric saving for the unshifted selected mode itself.
The constants are independent of height, finite prime support and length. -/
theorem quotientResponse_bound (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hlen : (11/8 : ℝ)*N ≤ L)
    (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    ‖(u : ℂ)^(N+1)*quotientResponse z A N y L‖ ≤
      3*divisorSquareDirichletMass (1025/1024)*((N : ℝ)+1)*((N : ℝ)+2)*Real.exp (-(N : ℝ)/100)+
      (2*Real.pi*(smallConstant+largeConstant))*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
  rw [quotientResponse_eq A hA h16 N hhead y L hu hU hz,mul_sub]
  apply (norm_sub_le _ _).trans
  exact add_le_add (unshiftedResponse_bound _ (fun _ ha => labels_data hA ha) N y hu hU
    (by linarith) hlen hz) (errorResponse_bound A h16 N hhead y hL hu hU hz)

/-- A single constant and rate suffice for the full transfer payment. -/
def paymentConstant : ℝ :=
  3*divisorSquareDirichletMass (1025/1024)+2*Real.pi*(smallConstant+largeConstant)

theorem paymentConstant_nonneg : 0 ≤ paymentConstant := by
  unfold paymentConstant
  have := divisorSquareDirichletMass_nonneg (1025/1024)
  positivity [smallConstant_nonneg,largeConstant_nonneg]

theorem quotientResponse_single_rate (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hlen : (11/8 : ℝ)*N ≤ L)
    (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    ‖(u : ℂ)^(N+1)*quotientResponse z A N y L‖ ≤
      paymentConstant*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
  apply (quotientResponse_bound A hA h16 N hhead y hL hlen hu hU hz).trans
  have he : Real.exp (-(N : ℝ)/100) ≤ Real.exp (-(N : ℝ)/300) :=
    Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hp : ((N : ℝ)+1)*((N : ℝ)+2) ≤ ((N : ℝ)+2)^3 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N,sq_nonneg ((N : ℝ)+2)]
  unfold paymentConstant
  calc
    _ ≤ 3*divisorSquareDirichletMass (1025/1024)*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)+
        (2*Real.pi*(smallConstant+largeConstant))*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
      apply add_le_add _ le_rfl
      rw [mul_assoc (3*_) ((N : ℝ)+1)]
      have hD := divisorSquareDirichletMass_nonneg (1025/1024)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The polynomial prefactor does not consume the geometric payment. -/
theorem tendsto_cubic_exp :
    Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)) atTop (nhds 0) := by
  let q := Real.exp (-(1 : ℝ)/300)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hq0 hq1
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hq0 hq1
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hq0 hq1
  convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
  · ext N
    have he : q^N = Real.exp (-(N : ℝ)/300) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [he,pow_zero,pow_one]
    ring
  · norm_num

/-- The exact physical prime support and moving Riesz length satisfy
every premise of the payment. In particular, this covers z=-u. -/
theorem tendsto_rough_quotientResponse {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    Tendsto (fun N => (u : ℂ)^(N+1)*quotientResponse z
      (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y (SquarefreeVaughanLogSource.length u N))
      atTop (nhds 0) := by
  have he : u < Real.exp (-((11/8 : ℝ)/2)) := by
    rw [show ((11/8 : ℝ)/2) = 11/16 by norm_num]
    exact hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hlen := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
    (by norm_num : (0 : ℝ) ≤ (11/8)/2) he
  apply squeeze_zero_norm' (a := fun N : ℕ => paymentConstant*
    (((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300)))
  · filter_upwards [hlen] with N hN
    simpa only [mul_assoc] using quotientResponse_single_rate _
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N
      (fun _ hp => ZetaRieszRoughEulerTransfer.rough_head hp) y
      (ZetaRieszHeadOrders.one_le_length u N) (by nlinarith [hN]) hu hU hz
  · simpa only [mul_zero] using tendsto_cubic_exp.const_mul paymentConstant

/-- The selected mode is precisely within the new payment, including
arbitrary multiplicity. Its shifted part is not claimed to decay. -/
theorem tendsto_selected_unshifted {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) (m : ℕ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*((m : ℂ)*quotientResponse (-(u : ℂ))
      (ZetaRieszRoughEulerTransfer.roughPrimes u N) N y (SquarefreeVaughanLogSource.length u N)))
      atTop (nhds 0) := by
  have hz : u ≤ ‖-(u : ℂ)‖ := by simp [abs_of_pos hu]
  simpa only [mul_zero,mul_left_comm] using (tendsto_rough_quotientResponse hu hU y hz).const_mul (m : ℂ)

/-- The genuine selected zero has precisely the denominator used in
the payment, with its full analytic multiplicity and negative residue. -/
theorem selected_principal_split (rho : NontrivialZetaZero) (xi : ℝ)
    {j : ℕ} (hj : 0 < j) :
    ZetaRieszMarkedLogDerivative.logDifference j (3/2+Complex.I*rho.1.im) xi =
      ZetaRieszExposedModeCoupling.regularDifference {rho} j (3/2+Complex.I*rho.1.im) xi-
        (analyticZetaZeroMultiplicity rho : ℂ)*
          ((-(-(3/2-rho.1.re : ℝ) : ℂ))⁻¹)^j/(j : ℂ)+
        (analyticZetaZeroMultiplicity rho : ℂ)*
          ((Complex.I*xi-(-(3/2-rho.1.re : ℝ) : ℂ))⁻¹)^j/(j : ℂ) := by
  have hz : rho.1-(3/2+Complex.I*rho.1.im) = (-(3/2-rho.1.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [ZetaRieszExposedModeCoupling.logDifference_principal_split {rho} rho.1.im xi hj]
  simp only [Finset.sum_singleton,hz,ZetaRieszExposedModeCoupling.modeDifference]
  ring

/-- Removing the paid negative unshifted residue leaves its shifted
resonance and all previous unpaid pieces in the signed main. -/
def selectedReducedMain (W : Finset NontrivialZetaZero) (u y : ℝ) (m N : ℕ) : ℂ :=
  ZetaRieszCompletionPayment.completionReducedMain W u y N+
    (m : ℂ)*quotientResponse (-(u : ℂ)) (ZetaRieszRoughEulerTransfer.roughPrimes u N)
      N y (SquarefreeVaughanLogSource.length u N)

/-- The original literal packet and every earlier paid error are
preserved. No bound on the shifted resonance or whole carrier is assumed. -/
theorem tendsto_selectedReduced_sub_current (W : Finset NontrivialZetaZero)
    {u : ℝ} (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (y : ℝ) (m : ℕ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (selectedReducedMain W u y m (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have hp := (tendsto_selected_unshifted (by linarith : 0 < u) hU y m).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  have he := (ZetaRieszCompletionPayment.tendsto_completionReduced_sub_current W hu hU y).add hp
  simp only [add_zero] at he
  convert he using 1
  ext j
  dsimp only [Function.comp_def,selectedReducedMain]
  ring

end
end RiemannGaussian.ZetaRieszUnshiftedPayment
