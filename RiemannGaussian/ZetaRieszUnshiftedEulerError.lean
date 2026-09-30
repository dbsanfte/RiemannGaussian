/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszUnshiftedCofactor

/-!
# The Euler correction retains the second Fourier zero

After the unshifted marked principal part is separated, the least-prime
leg supplies one Fourier zero and the full middle Euler correction supplies
the other. This pays that correction without using the shifted marked leg.
-/

namespace RiemannGaussian.ZetaRieszUnshiftedEulerError
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound
open ZetaRieszEulerCorrectionEnergy ZetaRieszMainFrequency
open ZetaRieszMarkedSeparation ZetaRieszMarkedPrimeCompletion
open ZetaRieszMarkedLogDerivative
open ZetaRieszSkewAllocation

/-- A logarithmic mass pays the Fourier zero of the entire middle error. -/
def phaseCost (sigma : ℝ) : ℝ :=
  Real.exp (4*mass sigma)*(2+Real.exp (8*mass (2*sigma)))*4*logMass (3/2)

theorem phaseCost_nonneg (sigma : ℝ) : 0 ≤ phaseCost sigma := by
  unfold phaseCost
  positivity [logMass_nonneg (by norm_num : (1 : ℝ) < 3/2)]

theorem square_log_head (Q : Finset ℕ) (N : ℕ)
    (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p) {s : ℂ} (hs : 1 ≤ s.re) :
    (∑ p ∈ Q, Real.log p*‖zetaPrimeFeature s p‖^2) ≤
      Real.exp (-(N : ℝ)/220)*logMass (3/2) := by
  have hp (p : ℕ) (hq : p ∈ Q) : ‖zetaPrimeFeature s p‖^2 ≤
      Real.exp (-(N : ℝ)/220)*zetaPrimeExpWeight (3/2) p := by
    rw [norm_zetaPrimeFeature,pow_two]
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_natCast_nonneg p
    have hh := hhead p hq
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hl]
  calc
    _ ≤ ∑ p ∈ Q, Real.log p*(Real.exp (-(N : ℝ)/220)*zetaPrimeExpWeight (3/2) p) :=
      Finset.sum_le_sum (fun p hq => mul_le_mul_of_nonneg_left (hp p hq)
        (Real.log_natCast_nonneg p))
    _ = Real.exp (-(N : ℝ)/220)*∑ p ∈ Q, Real.log p*zetaPrimeExpWeight (3/2) p := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_logMass_le Q (by norm_num)) (Real.exp_pos _).le

/-- This is an estimate on the actual full product difference, with its
leading quotient still present. The phase zero is not a relative error. -/
theorem error_phase_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : sigma ≤ s.re) (xi : ℝ) :
    ‖error Q xi s‖ ≤ phaseCost sigma*Real.exp (-(N : ℝ)/220)*|xi| := by
  have hq := fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
    (by linarith : (1/2 : ℝ) ≤ s.re) (h16 p hp)
  have hm := actual_square_mass_le Q (by linarith : 1/2 < sigma) hs
  have hl := norm_correctionLogSum_le_mass Q (zetaPrimeFeature s) (fun p => Real.log p) hq (-xi)
  have hla : ‖correctionLogSum Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)‖ ≤
      8*mass (2*sigma) := hl.trans (by unfold mass; linarith)
  have hz : ‖correctionLogSum Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)‖ ≤
      4*(Real.exp (-(N : ℝ)/220)*logMass (3/2))*|xi| := by
    apply (norm_correctionLogSum_le_phase Q _ _ hq (-xi)).trans
    simp_rw [← character_phase_eq]
    calc
      _ ≤ 4*∑ p ∈ Q, ‖zetaPrimeFeature s p‖^2*(|xi| *Real.log p) := by
        gcongr with p hp
        exact phase_le_log p xi
      _ = 4*(∑ p ∈ Q, Real.log p*‖zetaPrimeFeature s p‖^2)*|xi| := by
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _hp
        ring
      _ ≤ _ := by gcongr; exact square_log_head Q N hhead (by linarith)
  have hc : ‖correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)-1‖ ≤
      (2+Real.exp (8*mass (2*sigma)))*(4*(Real.exp (-(N : ℝ)/220)*logMass (3/2))*|xi|) := by
    rw [correctionProduct_eq_exp Q _ _ hq]
    exact (ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear hla).trans
      (mul_le_mul_of_nonneg_left hz (by positivity))
  rw [error_eq Q h16 (by linarith) xi,norm_mul]
  exact (mul_le_mul (norm_quotient_le Q h16 hsigma hs xi) hc
    (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by unfold phaseCost mass; ring)

theorem error_moment_phase_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) (k : ℕ) :
    ‖signedTaylorMoment k (error Q xi) s‖ ≤
      phaseCost (s.re-R)*Real.exp (-(N : ℝ)/220)*|xi| /R^k := by
  apply norm_signedTaylorMoment_le hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    exact (analyticAt_error Q h16
      (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    exact error_phase_bound Q h16 N hhead hs
      (ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) xi

/-- The entire least-prime/cofactor correction at each original order. -/
def errorCofactor (A : Finset ℕ) (N j h : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ r ∈ A, PowerSeries.coeff h (leg s xi r)*
    signedTaylorMoment (N+1-j-h) (error (tailPrimes A r) xi) s

theorem errorCofactor_bound (A : Finset ℕ)
    (N j h : ℕ) (hh : h ∈ rectangleOrders N j)
    (s : ℂ) (xi : ℝ)
    {b : ℝ} (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (herr : ∀ r ∈ A, ‖signedTaylorMoment (N+1-j-h) (error (tailPrimes A r) xi) s‖ ≤
      b/safeRadius^(N+1-j-h)) :
    ‖errorCofactor A N j h s xi‖ ≤
      b*safeRadius⁻¹^(N+1-j)*∑ r ∈ A, zetaPrimeExpWeight (s.re-safeRadius) r*f r := by
  have hR := safeRadius_pos
  have he : h+(N+1-j-h) = N+1-j := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega
  unfold errorCofactor
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hl := (norm_leg_le r h s xi safeRadius_pos).trans
    (mul_le_mul_of_nonneg_right (hphase r) (by unfold zetaPrimeExpWeight; positivity))
  rw [norm_mul]
  apply (mul_le_mul hl (herr r hr) (norm_nonneg _)
    (by have := hf r; unfold zetaPrimeExpWeight; positivity)).trans_eq
  simp only [div_eq_mul_inv,← inv_pow]
  calc
    _ = b*(safeRadius⁻¹^h*safeRadius⁻¹^(N+1-j-h))*
        (zetaPrimeExpWeight (s.re-safeRadius) r*f r) := by ring
    _ = _ := by rw [← pow_add,he]

theorem errorCofactor_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h : ℕ) (hh : h ∈ rectangleOrders N j)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y xi : ℝ) :
    ‖errorCofactor A N j h (3/2+Complex.I*y) xi‖ ≤
      (phaseCost (3/2-safeRadius)*logMass (3/2-safeRadius))*
        Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j)*xi^2 := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hm : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r)) ≤
      |xi| *logMass (3/2-safeRadius) := by
    simp_rw [show ∀ r : ℕ, zetaPrimeExpWeight (3/2-safeRadius) r*(|xi| *Real.log r) =
      |xi| *(Real.log r*zetaPrimeExpWeight (3/2-safeRadius) r) from fun _ => by ring]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_logMass_le A hs) (abs_nonneg xi)
  have he := errorCofactor_bound A N j h hh (3/2+Complex.I*y) xi
    (b := phaseCost (3/2-safeRadius)*Real.exp (-(N : ℝ)/220)*|xi|)
    (fun p => |xi| *Real.log p)
    (fun p => mul_nonneg (abs_nonneg xi) (Real.log_natCast_nonneg p))
    (fun p => phase_le_log p xi)
    (fun r _ => by
      simpa using (error_moment_phase_bound (tailPrimes A r)
        (fun p hp => h16 p (Finset.mem_filter.mp hp).1) N
        (fun p hp => hhead p (Finset.mem_filter.mp hp).1)
        (s := 3/2+Complex.I*y) safeRadius_pos (by simpa using hs) xi (N+1-j-h)))
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at he
  apply he.trans
  have hR := safeRadius_pos
  have hC := phaseCost_nonneg (3/2-safeRadius)
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [← sq_abs xi]
  ring

theorem errorCofactor_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h : ℕ) (hh : h ∈ rectangleOrders N j)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y xi : ℝ) :
    ‖errorCofactor A N j h (3/2+Complex.I*y) xi‖ ≤
      (2*cost (3/2-safeRadius)*mass (3/2-safeRadius))*
        Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j) := by
  have hs : (1 : ℝ) < 3/2-safeRadius := by norm_num [safeRadius]
  have hm : (∑ r ∈ A, zetaPrimeExpWeight (3/2-safeRadius) r*2) ≤
      mass (3/2-safeRadius)*2 := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num)
  have he := errorCofactor_bound A N j h hh (3/2+Complex.I*y) xi
    (b := cost (3/2-safeRadius)*Real.exp (-(N : ℝ)/220))
    (fun _ => 2) (fun _ => by norm_num) (fun p => phase_le_two p xi)
    (fun r _ => by
      simpa using (norm_error_moment_le (tailPrimes A r)
        (fun p hp => h16 p (Finset.mem_filter.mp hp).1) N
        (fun p hp => hhead p (Finset.mem_filter.mp hp).1)
        (s := 3/2+Complex.I*y) safeRadius_pos (by simpa using hs) xi (N+1-j-h)))
  simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at he
  apply he.trans
  have hR := safeRadius_pos
  have hC := cost_nonneg (3/2-safeRadius)
  exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)

/-- The head saving beats the entire complementary source amplification. -/
theorem error_source_rate {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {N k : ℕ} (hk : k ≤ N+1) :
    u^k*safeRadius⁻¹^k*Real.exp (-(N : ℝ)/220) ≤
      2*Real.exp (-(N : ℝ)/300) := by
  let a : ℝ := ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius
  have hR := safeRadius_pos
  have ha : 1 ≤ a := by norm_num [a,safeRadius,ZetaRieszWideOwnerAudit.radiusCeiling]
  have hlog : Real.log a ≤ 1/1000 :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans
      (by norm_num [a,safeRadius,ZetaRieszWideOwnerAudit.radiusCeiling])
  have hp : u^k*safeRadius⁻¹^k ≤ a^(N+1) := by
    rw [← mul_pow]
    apply (pow_le_pow_left₀ (by positivity)
      (show u*safeRadius⁻¹ ≤ a by
        dsimp [a]; rw [div_eq_mul_inv]; gcongr) k).trans
    exact pow_le_pow_right₀ ha hk
  apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans
  rw [show a^(N+1) = Real.exp ((N+1 : ℕ)*Real.log a) by
    rw [Real.exp_nat_mul,Real.exp_log (by linarith)],← Real.exp_add]
  have hb : ((N+1 : ℕ) : ℝ)*Real.log a+(-(N : ℝ)/220) ≤ 1/1000-(N : ℝ)/300 := by
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (N+1))
    push_cast at hh ⊢
    linarith [Nat.cast_nonneg (α := ℝ) N]
  apply (Real.exp_le_exp.mpr hb).trans
  rw [sub_eq_add_neg,Real.exp_add]
  have he : Real.exp (1/1000 : ℝ) ≤ 2 := by
    apply (Real.exp_le_exp.mpr (by norm_num : (1/1000 : ℝ) ≤ 1/2)).trans
    have h := Real.exp_one_lt_d9
    have hs : (Real.exp (1/2 : ℝ))^2 = Real.exp 1 := by
      rw [pow_two,← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1/2 : ℝ)]
  simpa only [neg_div] using mul_le_mul_of_nonneg_right he (Real.exp_pos _).le

/-- The exact middle correction summed over the original marked rectangle. -/
def errorSymbol (A : Finset ℕ) (N : ℕ) (y xi : ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    ((-z)⁻¹)^j/(j : ℂ)*errorCofactor A N j h (3/2+Complex.I*y) xi

theorem errorSymbol_bound (A : Finset ℕ) (N : ℕ) (y xi : ℝ)
    {u : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ Finset.range (N+2), ∀ h ∈ rectangleOrders N j,
      ‖errorCofactor A N j h (3/2+Complex.I*y) xi‖ ≤
        B*Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j)) :
    ‖(u : ℂ)^(N+1)*errorSymbol A N y xi z‖ ≤
      2*B*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300) := by
  unfold errorSymbol
  simp only [Finset.mul_sum]
  apply (rectangle_sum_bound N _ (B := 2*B*Real.exp (-(N : ℝ)/300))
    (by positivity) ?_).trans_eq (by ring)
  intro j hj h hh
  have hj0 := ZetaRieszMarkedLogDerivative.marked_order_pos hh
  have hjM : j ≤ N+1 := by have := Finset.mem_range.mp hj; omega
  have hn : ‖((-z)⁻¹)^j/(j : ℂ)‖ ≤ ‖(-z)⁻¹‖^j := by
    rw [norm_div,norm_pow,Complex.norm_natCast]
    exact div_le_self (by positivity) (by exact_mod_cast hj0)
  have hm := ZetaRieszUnshiftedCofactor.scaled_mode_le hu hz hjM
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
  calc
    _ ≤ (u^(N+1)*‖(-z)⁻¹‖^j)*
        (B*Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j)) := by
      rw [← mul_assoc]
      have hR := safeRadius_pos
      exact mul_le_mul (mul_le_mul_of_nonneg_left hn (by positivity)) (hb j hj h hh)
        (norm_nonneg _) (by positivity)
    _ ≤ u^(N+1-j)*(B*Real.exp (-(N : ℝ)/220)*safeRadius⁻¹^(N+1-j)) := by
      have hR := safeRadius_pos
      exact mul_le_mul_of_nonneg_right hm (by positivity)
    _ = B*(u^(N+1-j)*safeRadius⁻¹^(N+1-j)*Real.exp (-(N : ℝ)/220)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (error_source_rate hu hU (by omega)) hB).trans_eq (by ring)

/-- Height-independent constant for the two-zero small-frequency bound. -/
def smallConstant : ℝ := phaseCost (3/2-safeRadius)*logMass (3/2-safeRadius)
/-- Height-independent constant for the bounded large-frequency numerator. -/
def largeConstant : ℝ := 2*cost (3/2-safeRadius)*mass (3/2-safeRadius)

theorem smallConstant_nonneg : 0 ≤ smallConstant := by
  exact mul_nonneg (phaseCost_nonneg _) (logMass_nonneg (by norm_num [safeRadius]))

theorem largeConstant_nonneg : 0 ≤ largeConstant := by
  unfold largeConstant
  have := cost_nonneg (3/2-safeRadius)
  have := mass_nonneg (3/2-safeRadius)
  positivity

/-- Both signed Fourier phases of the same unshifted Euler correction. -/
def errorPair (A : Finset ℕ) (N : ℕ) (y L xi : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*errorSymbol A N y xi z+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*errorSymbol A N y (-xi) z

/-- An integrable whole-frequency profile for the unshifted correction.
No selected-mode Fourier cancellation is charged to this error. -/
theorem errorPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L xi : ℝ)
    {u : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    ‖(u : ℂ)^(N+1)*(errorPair A N y L xi z/(xi : ℂ)^2)‖ ≤
      (4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))*(1+xi^2)⁻¹ := by
  have hsmall (t : ℝ) : ‖(u : ℂ)^(N+1)*errorSymbol A N y t z‖ ≤
      (2*smallConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))*t^2 := by
    have he := errorSymbol_bound A N y t hu hU hz
      (mul_nonneg smallConstant_nonneg (sq_nonneg t))
      (fun j _ h hh => (errorCofactor_small A h16 N j h hh hhead y t).trans_eq
        (by unfold smallConstant; ring))
    exact he.trans_eq (by ring)
  have hlarge (t : ℝ) : ‖(u : ℂ)^(N+1)*errorSymbol A N y t z‖ ≤
      2*largeConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300) :=
    errorSymbol_bound A N y t hu hU hz largeConstant_nonneg
      (fun j _ h hh => errorCofactor_large A h16 N j h hh hhead y t)
  have he (t : ℝ) : ‖(u : ℂ)^(N+1)*(Complex.exp (((t*L : ℝ) : ℂ)*Complex.I)*
      errorSymbol A N y t z)‖ = ‖(u : ℂ)^(N+1)*errorSymbol A N y t z‖ := by
    rw [mul_left_comm,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have hn : ‖(u : ℂ)^(N+1)*errorPair A N y L xi z‖ ≤
      (4*smallConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))*xi^2 := by
    unfold errorPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (hsmall xi) (hsmall (-xi))).trans_eq (by rw [neg_sq]; ring)
  have hl : ‖(u : ℂ)^(N+1)*errorPair A N y L xi z‖ ≤
      4*largeConstant*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300) := by
    unfold errorPair
    rw [mul_add]
    apply (norm_add_le _ _).trans
    rw [he,he]
    exact (add_le_add (hlarge xi) (hlarge (-xi))).trans_eq (by ring)
  rw [← mul_div_assoc]
  exact (norm_div_square_profile (by positivity [smallConstant_nonneg])
    (by positivity [largeConstant_nonneg]) hn hl).trans_eq (by ring)

theorem measurable_errorPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) (z : ℂ) :
    StronglyMeasurable (fun xi : ℝ => errorPair A N y L xi z/(xi : ℂ)^2) := by
  have hm (j h : ℕ) : Measurable (fun xi : ℝ => errorCofactor A N j h (3/2+Complex.I*y) xi) := by
    apply Finset.measurable_fun_sum
    intro r _hr
    have he := (measurable_error_moment (tailPrimes A r)
      (fun p hp => h16 p (Finset.mem_filter.mp hp).1) (s := 3/2+Complex.I*y)
      safeRadius_pos (by norm_num [safeRadius]) (N+1-j-h)).measurable
    simp only [coeff_leg]
    unfold zetaPrimeFeature
    fun_prop
  have hsymbol : Measurable (fun xi : ℝ => errorSymbol A N y xi z) := by
    unfold errorSymbol
    fun_prop
  have hneg := hsymbol.comp measurable_neg
  apply Measurable.stronglyMeasurable
  unfold errorPair
  fun_prop

theorem integrable_errorPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ)
    {u : ℝ} (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    IntegrableOn (fun xi : ℝ => (u : ℂ)^(N+1)*(errorPair A N y L xi z/(xi : ℂ)^2)) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300))).mono'
  · exact ((measurable_errorPair A h16 N y L z).const_mul _).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => errorPair_profile A h16 N hhead y L xi hu hU hz)

/-- The full-frequency correction with the original Riesz prefactor. -/
def errorResponse (A : Finset ℕ) (N : ℕ) (y L : ℝ) (z : ℂ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, errorPair A N y L xi z/(xi : ℂ)^2

/-- The exact character-minus-quotient correction is geometrically
paid after the marked term has been split into its two frequencies. -/
theorem errorResponse_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y : ℝ)
    {L u : ℝ} (hL : 1 ≤ L) (hu : 0 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    {z : ℂ} (hz : u ≤ ‖z‖) :
    ‖(u : ℂ)^(N+1)*errorResponse A N y L z‖ ≤
      (2*Real.pi*(smallConstant+largeConstant))*((N : ℝ)+2)^3*Real.exp (-(N : ℝ)/300) := by
  have hi := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
      (4*(smallConstant+largeConstant)*((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)))
    (Eventually.of_forall (fun xi => errorPair_profile A h16 N hhead y L xi hu hU hz))
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
    _ = ((N : ℝ)+1)*(2*Real.pi*(smallConstant+largeConstant)*
        ((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) := by ring
    _ ≤ ((N : ℝ)+2)*(2*Real.pi*(smallConstant+largeConstant)*
        ((N : ℝ)+2)^2*Real.exp (-(N : ℝ)/300)) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity [smallConstant_nonneg,largeConstant_nonneg]
    _ = _ := by ring

end
end RiemannGaussian.ZetaRieszUnshiftedEulerError
