/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedPrimeHead
import RiemannGaussian.ZetaRieszEulerMoments
import RiemannGaussian.ZetaRieszFilteredCompletion

/-!
# The full middle Euler correction above the exponential prime head

The leading quotient is retained when estimating the Euler correction.
The estimates are uniform in the finite prime set and Fourier frequency.
They do not estimate the leading signed quotient itself.
-/

namespace RiemannGaussian.ZetaRieszMarkedEulerError
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszEulerQuotient ZetaRieszEulerCorrectionEnergy

/-- The complete finite middle character, before factorial extraction. -/
def character (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ Q, (1+zetaPrimeFeature s p*(1-zetaPrimeFeature (Complex.I*xi) p))

/-- The corresponding finite Euler quotient with its full frequency. -/
def quotient (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ Q, (1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/
    (1-zetaPrimeFeature s p)

/-- The actual difference of the full products, not a relative error. -/
def error (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  character Q xi s-quotient Q xi s

theorem norm_character_phase (xi : ℝ) (p : ℕ) :
    ‖zetaPrimeFeature (Complex.I*xi) p‖ = 1 := by
  simp [norm_zetaPrimeFeature,zetaPrimeExpWeight]

theorem character_phase_eq (xi : ℝ) (p : ℕ) :
    zetaPrimeFeature (Complex.I*xi) p =
      Complex.exp (((Real.log p*(-xi) : ℝ) : ℂ)*Complex.I) := by
  unfold zetaPrimeFeature
  congr 1
  push_cast
  ring

/-- Every interaction of the correction remains multiplied by the
whole leading quotient in this exact identity. -/
theorem error_eq (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    error Q xi s = quotient Q xi s*
      (correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)-1) := by
  have h := finite_character_eq_quotient_product Q (zetaPrimeFeature s)
    (zetaPrimeFeature (Complex.I*xi))
    (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (h16 p hp))
    (fun p _ => (norm_character_phase xi p).le)
  unfold error character quotient
  rw [h,← Finset.prod_div_distrib]
  simp only [character_phase_eq,correctionProduct]
  ring

theorem norm_local_quotient_le {q z : ℂ} (hq : ‖q‖ ≤ 1/4) (hz : ‖z‖ ≤ 1) :
    ‖(1-q*z)/(1-q)‖ ≤ 1+4*‖q‖ := by
  have hd : 3/4 ≤ ‖1-q‖ := by
    simpa only [mul_one] using local_denominator_bound hq
      (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)
  have hd0 : 1-q ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : (1-q*z)/(1-q) = 1+q*(1-z)/(1-q) := by field_simp; ring
  have hz2 : ‖1-z‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num; linarith)
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_div,norm_mul]
  apply add_le_add le_rfl
  apply (div_le_iff₀ (by linarith : 0 < ‖1-q‖)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hz2 (norm_nonneg q),norm_nonneg q]

/-- A finite mass bounds the whole leading quotient on the safe
half-plane. It is uniform in both the frequency and the prime selection. -/
theorem norm_quotient_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : sigma ≤ s.re) (xi : ℝ) :
    ‖quotient Q xi s‖ ≤ Real.exp (4*∑' n, zetaPrimeExpWeight sigma n) := by
  have hsum : (∑ p ∈ Q, ‖zetaPrimeFeature s p‖) ≤ ∑' n, zetaPrimeExpWeight sigma n := by
    apply (Finset.sum_le_sum (fun p _ => ?_)).trans
      ((summable_zetaPrimeExpWeight hsigma).sum_le_tsum Q
        (fun n _ => (Real.exp_pos _).le))
    rw [norm_zetaPrimeFeature]
    exact ZetaPrimeNonlinearHalfplane.expWeight_mono hs p
  unfold quotient
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ Q, (1+4*‖zetaPrimeFeature s p‖) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp =>
        norm_local_quotient_le
          (ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter (by linarith) (h16 p hp))
          (norm_character_phase xi p).le)
    _ ≤ Real.exp (∑ p ∈ Q, 4*‖zetaPrimeFeature s p‖) :=
      Real.prod_one_add_le_exp_sum Q (fun _ => by positivity)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact Real.exp_le_exp.mpr (by linarith)

/-- The exponential prime head makes the full square-amplitude mass
exponentially small, uniformly throughout the safe contour. -/
theorem square_mass_head (Q : Finset ℕ) (N : ℕ)
    (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p) {s : ℂ} (hs : 1 ≤ s.re) :
    (∑ p ∈ Q, ‖zetaPrimeFeature s p‖^2) ≤
      Real.exp (-(N : ℝ)/220)*(∑' n, zetaPrimeExpWeight (3/2) n) := by
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
    _ ≤ ∑ p ∈ Q, Real.exp (-(N : ℝ)/220)*zetaPrimeExpWeight (3/2) p :=
      Finset.sum_le_sum hp
    _ = Real.exp (-(N : ℝ)/220)*∑ p ∈ Q, zetaPrimeExpWeight (3/2) p :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 3/2)).sum_le_tsum Q
        (fun n _ => (Real.exp_pos _).le)) (Real.exp_pos _).le

/-- An explicit finite bound for the product of the leading quotient
and every order of the nonlinear correction. -/
def cost (sigma : ℝ) : ℝ :=
  Real.exp (4*∑' n, zetaPrimeExpWeight sigma n)*
    (2+Real.exp (8*∑' n, zetaPrimeExpWeight (2*sigma) n))*
      8*(∑' n, zetaPrimeExpWeight (3/2) n)

theorem cost_nonneg (sigma : ℝ) : 0 ≤ cost sigma := by
  have hm : 0 ≤ ∑' n, zetaPrimeExpWeight (3/2) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  unfold cost
  positivity

/-- The entire Euler error, including its leading multiplier, has a
uniform exponential bound above the paid prime head. -/
theorem norm_error_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : sigma ≤ s.re) (xi : ℝ) :
    ‖error Q xi s‖ ≤ cost sigma*Real.exp (-(N : ℝ)/220) := by
  let A : ℝ := ∑' n, zetaPrimeExpWeight (2*sigma) n
  let B : ℝ := ∑' n, zetaPrimeExpWeight (3/2) n
  have hq := fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
    (by linarith : (1/2 : ℝ) ≤ s.re) (h16 p hp)
  have hm := actual_square_mass_le Q (by linarith : 1/2 < sigma) hs
  have hh := square_mass_head Q N hhead (by linarith : 1 ≤ s.re)
  have hl := norm_correctionLogSum_le_mass Q (zetaPrimeFeature s) (fun p => Real.log p) hq (-xi)
  have hla : ‖correctionLogSum Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)‖ ≤ 8*A :=
    hl.trans (by dsimp [A]; linarith)
  have hc : ‖correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)-1‖ ≤
      (2+Real.exp (8*A))*(8*(Real.exp (-(N : ℝ)/220)*B)) := by
    rw [correctionProduct_eq_exp Q _ _ hq]
    exact (ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear hla).trans
      (mul_le_mul_of_nonneg_left (hl.trans (by dsimp [B]; linarith)) (by positivity))
  rw [error_eq Q h16 (by linarith) xi,norm_mul]
  calc
    _ ≤ Real.exp (4*∑' n, zetaPrimeExpWeight sigma n)*
        ((2+Real.exp (8*A))*(8*(Real.exp (-(N : ℝ)/220)*B))) :=
      mul_le_mul (norm_quotient_le Q h16 hsigma hs xi) hc (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by dsimp [cost,A,B]; ring

theorem analyticAt_character (Q : Finset ℕ) (xi : ℝ) (s : ℂ) :
    AnalyticAt ℂ (character Q xi) s := by
  unfold character
  apply Finset.analyticAt_fun_prod
  intro p _hp
  unfold zetaPrimeFeature
  fun_prop

theorem analyticAt_quotient (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : AnalyticAt ℂ (quotient Q xi) s := by
    unfold quotient
    apply Finset.analyticAt_fun_prod
    intro p hp
    have hf : AnalyticAt ℂ (fun z => zetaPrimeFeature z p) s := by
      unfold zetaPrimeFeature
      fun_prop
    apply (analyticAt_const.sub (hf.mul analyticAt_const)).div (analyticAt_const.sub hf)
    change 1-zetaPrimeFeature s p ≠ 0
    simpa only [mul_one] using local_denominator_ne_zero
      (ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (h16 p hp))
      (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)

theorem analyticAt_error (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : AnalyticAt ℂ (error Q xi) s :=
  (analyticAt_character Q xi s).sub (analyticAt_quotient Q h16 hs xi)

/-- Cauchy's bound retains every factorial cofactor order of the full
error, including zero, with the prime-head saving still present. -/
theorem norm_error_moment_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (xi : ℝ) (k : ℕ) :
    ‖signedTaylorMoment k (error Q xi) s‖ ≤
      (cost (s.re-R)*Real.exp (-(N : ℝ)/220))/R^k := by
  apply norm_signedTaylorMoment_le hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    exact (analyticAt_error Q h16
      (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    exact norm_error_le Q h16 N hhead hhalf
      (ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) xi

/-- The constant channel is retained at order zero. -/
theorem moment_one (k : ℕ) (s : ℂ) :
    signedTaylorMoment k (fun _ => (1 : ℂ)) s =
      PowerSeries.coeff k (1 : PowerSeries ℂ) := by
  by_cases hk : k = 0
  · subst k; simp [signedTaylorMoment]
  · simp [signedTaylorMoment,iteratedDeriv_const,PowerSeries.coeff_one,hk]

/-- A local character has exactly the existing factorial prime leg,
including its constant term. -/
theorem moment_factor (k p : ℕ) (s : ℂ) (xi : ℝ) :
    signedTaylorMoment k (fun z => 1+zetaPrimeFeature z p*
      (1-zetaPrimeFeature (Complex.I*xi) p)) s =
      PowerSeries.coeff k (1+ZetaRieszMarkedEuler.leg s xi p) := by
  have he : (fun z => 1+zetaPrimeFeature z p*(1-zetaPrimeFeature (Complex.I*xi) p)) =
      (fun z => 1+(1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeFeature z p) := by
    funext z; ring
  rw [he,signedTaylorMoment_add k analyticAt_const (by unfold zetaPrimeFeature; fun_prop),
    signedTaylorMoment_const_mul,ZetaRieszFilteredCompletion.signedTaylorMoment_feature,
    moment_one,map_add,ZetaRieszMarkedEuler.coeff_leg]
  rfl

/-- The finite Euler product's analytic moments are the literal
formal factorial coefficients. No limiting share approximation enters. -/
theorem coeff_character (Q : Finset ℕ) (k : ℕ) (s : ℂ) (xi : ℝ) :
    PowerSeries.coeff k (∏ p ∈ Q, (1+ZetaRieszMarkedEuler.leg s xi p)) =
      signedTaylorMoment k (character Q xi) s := by
  induction Q using Finset.induction_on generalizing k with
  | empty =>
      have he : character ∅ xi = (fun _ => (1 : ℂ)) := by
        funext z; simp [character]
      rw [Finset.prod_empty,he]
      exact (moment_one k s).symm
  | @insert p Q hp ih =>
      rw [Finset.prod_insert hp]
      have he : character (insert p Q) xi =
          (fun z => (1+zetaPrimeFeature z p*(1-zetaPrimeFeature (Complex.I*xi) p))*
            character Q xi z) := by
        funext z
        exact Finset.prod_insert hp
      rw [he,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        signedTaylorMoment_mul (by unfold zetaPrimeFeature; fun_prop) (analyticAt_character Q xi s)]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [ih,moment_factor]

/-- The original two marked coordinates act on an entire analytic
middle response with the same correlated total order. -/
def rectangleMoment (N p r : ℕ) (s : ℂ) (xi : ℝ) (F : ℂ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    PowerSeries.coeff j (ZetaRieszMarkedEuler.leg s xi p)*
      PowerSeries.coeff h (ZetaRieszMarkedEuler.leg s xi r)*
        signedTaylorMoment (N+1-j-h) F s

/-- This is an exact bridge to the already proved ordered Euler
completion, before estimating its correction. -/
theorem rectangle_character (Q : Finset ℕ) (N p r : ℕ) (s : ℂ) (xi : ℝ) :
    ZetaRieszMarkedEuler.rectangle N p r s xi
        (∏ q ∈ Q, (1+ZetaRieszMarkedEuler.leg s xi q)) =
      rectangleMoment N p r s xi (character Q xi) := by
  simp only [ZetaRieszMarkedEuler.rectangle,rectangleMoment,coeff_character]

/-- The leading quotient and its full correction are separated only
after retaining the literal correlated factorial rectangle. -/
theorem rectangle_split (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    ZetaRieszMarkedEuler.rectangle N p r s xi
        (∏ q ∈ Q, (1+ZetaRieszMarkedEuler.leg s xi q)) =
      rectangleMoment N p r s xi (quotient Q xi)+
        rectangleMoment N p r s xi (error Q xi) := by
  rw [rectangle_character]
  have hm (k : ℕ) : signedTaylorMoment k (error Q xi) s =
      signedTaylorMoment k (character Q xi) s-signedTaylorMoment k (quotient Q xi) s :=
    signedTaylorMoment_sub k (analyticAt_character Q xi s) (analyticAt_quotient Q h16 hs xi)
  simp only [rectangleMoment,hm,mul_sub,Finset.sum_sub_distrib]
  ring

/-- A single marked coefficient retains its exact Fourier zero. -/
theorem norm_leg_le (p k : ℕ) (s : ℂ) (xi : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖PowerSeries.coeff k (ZetaRieszMarkedEuler.leg s xi p)‖ ≤
      ‖1-zetaPrimeFeature (Complex.I*xi) p‖*
        (R⁻¹^k*zetaPrimeExpWeight (s.re-R) p) := by
  rw [ZetaRieszMarkedEuler.coeff_leg,norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le k s p hR) (norm_nonneg _)

/-- The three orders sum exactly, including every low cofactor order. -/
theorem norm_rectangle_atom_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r j h : ℕ) (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (xi : ℝ) :
    ‖PowerSeries.coeff j (ZetaRieszMarkedEuler.leg s xi p)*
      PowerSeries.coeff h (ZetaRieszMarkedEuler.leg s xi r)*
        signedTaylorMoment (N+1-j-h) (error Q xi) s‖ ≤
      (cost (s.re-R)*Real.exp (-(N : ℝ)/220)/R^(N+1))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  have he : j+h+(N+1-j-h) = N+1 := by
    have hj' := Finset.mem_range.mp hj
    have hh' := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  rw [norm_mul,norm_mul]
  apply (mul_le_mul
    (mul_le_mul (norm_leg_le p j s xi hR) (norm_leg_le r h s xi hR)
      (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity))
    (norm_error_moment_le Q h16 N hhead hR hhalf xi (N+1-j-h))
    (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)).trans_eq
  simp only [div_eq_mul_inv,← inv_pow]
  have hp : R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h) = R⁻¹^(N+1) := by
    rw [← pow_add,← pow_add,he]
  calc
    _ = (cost (s.re-R)*Real.exp (-(N : ℝ)/220))*
      (R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
            simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [hp]; simp only [div_eq_mul_inv]

/-- The complete finite rectangle costs only a quadratic order factor;
the common Cauchy radius is raised to the single correlated total order. -/
theorem norm_rectangle_error_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (xi : ℝ) :
    ‖rectangleMoment N p r s xi (error Q xi)‖ ≤
      ((N : ℝ)+2)^2*(cost (s.re-R)*Real.exp (-(N : ℝ)/220)/R^(N+1))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  let B := (cost (s.re-R)*Real.exp (-(N : ℝ)/220)/R^(N+1))*
    (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
      (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖)
  have hB : 0 ≤ B := by dsimp [B]; have := cost_nonneg (s.re-R); unfold zetaPrimeExpWeight; positivity
  have hc (j : ℕ) : ((ZetaRieszSkewAllocation.rectangleOrders N j).card : ℝ) ≤ (N : ℝ)+2 := by
    have h := Finset.card_le_card
      (show ZetaRieszSkewAllocation.rectangleOrders N j ⊆ Finset.range (N+1-j+1) from
        Finset.filter_subset _ _)
    rw [Finset.card_range] at h
    exact_mod_cast (show (ZetaRieszSkewAllocation.rectangleOrders N j).card ≤ N+2 by omega)
  unfold rectangleMoment
  calc
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ‖PowerSeries.coeff j (ZetaRieszMarkedEuler.leg s xi p)*
          PowerSeries.coeff h (ZetaRieszMarkedEuler.leg s xi r)*
            signedTaylorMoment (N+1-j-h) (error Q xi) s‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ _h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, B :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh =>
        norm_rectangle_atom_le Q h16 N p r j h hj hh hhead hR hhalf xi))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*B := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hc j) hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; dsimp [B]; ring

/-- The original two marked Fourier factors pay the frequency-square
denominator. Neither marked prime is removed from this bound. -/
theorem marked_phase_bound (p r : ℕ) (xi : ℝ) :
    ‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖ ≤
      (1-Real.cos (Real.log p*xi))+(1-Real.cos (Real.log r*xi)) := by
  have hs (n : ℕ) : ‖1-zetaPrimeFeature (Complex.I*xi) n‖^2 =
      2*(1-Real.cos (Real.log n*xi)) := by
    rw [character_phase_eq,ZetaPrimeCharacterRemainder.norm_character_difference_sq]
    simp only [mul_neg,Real.cos_neg]
  nlinarith [sq_nonneg (‖1-zetaPrimeFeature (Complex.I*xi) p‖-
    ‖1-zetaPrimeFeature (Complex.I*xi) r‖),hs p,hs r]

/-- The full paired correction, with the original physical Riesz
length and both Fourier signs. -/
def rectanglePairError (Q : Finset ℕ) (N p r : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*rectangleMoment N p r s xi (error Q xi)+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*rectangleMoment N p r s (-xi) (error Q (-xi))

/-- The common budget preserves the single total factorial order. -/
def rectangleBudget (N : ℕ) (sigma R : ℝ) : ℝ :=
  ((N : ℝ)+2)^2*(cost sigma*Real.exp (-(N : ℝ)/220)/R^(N+1))

theorem rectangleBudget_nonneg (N : ℕ) (sigma : ℝ) {R : ℝ} (hR : 0 < R) :
    0 ≤ rectangleBudget N sigma R := by
  unfold rectangleBudget
  have := cost_nonneg sigma
  positivity

/-- A frequency-integrable bound for the entire quotient-times-error
after the literal marked rectangle, uniform in the physical length. -/
theorem norm_rectanglePairError_div_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L xi : ℝ) :
    ‖rectanglePairError Q N p r s L xi/(xi : ℂ)^2‖ ≤
      2*rectangleBudget N (s.re-R) R*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          ((1-Real.cos (Real.log p*xi))/xi^2+(1-Real.cos (Real.log r*xi))/xi^2) := by
  let C := rectangleBudget N (s.re-R) R*
    (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)
  have hC : 0 ≤ C := by
    dsimp [C]; have := rectangleBudget_nonneg N (s.re-R) hR
    unfold zetaPrimeExpWeight; positivity
  have hb (t : ℝ) : ‖rectangleMoment N p r s t (error Q t)‖ ≤
      C*((1-Real.cos (Real.log p*t))+(1-Real.cos (Real.log r*t))) :=
    (norm_rectangle_error_le Q h16 N p r hhead hR hhalf t).trans
      (mul_le_mul_of_nonneg_left (marked_phase_bound p r t) hC)
  have hpair : ‖rectanglePairError Q N p r s L xi‖ ≤
      2*C*((1-Real.cos (Real.log p*xi))+(1-Real.cos (Real.log r*xi))) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    have hm := hb (-xi)
    simp only [mul_neg,Real.cos_neg] at hm
    linarith [hb xi]
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  apply (div_le_div_of_nonneg_right hpair (sq_nonneg xi)).trans_eq
  dsimp [C]
  ring

/-- Frequency measurability follows from a fixed Cauchy circle, with
the complete middle error kept inside the integral. -/
theorem measurable_error_moment (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (k : ℕ) :
    StronglyMeasurable (fun xi : ℝ => signedTaylorMoment k (error Q xi) s) := by
  have hf : StronglyMeasurable (fun v : ℝ × ℂ => error Q v.1 v.2) := by
    apply Measurable.stronglyMeasurable
    unfold error character quotient zetaPrimeFeature
    fun_prop
  have he (xi : ℝ) := ZetaRieszEulerMoments.signedTaylorMoment_eq_circleIntegral hR
    (f := error Q xi) (s := s) (show DiffContOnCl ℂ _ (Metric.ball s R) from by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s hR.ne']
      intro z hz
      exact (analyticAt_error Q h16
        (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt) k
  simp_rw [he]
  exact (ZetaRieszEulerMoments.stronglyMeasurable_parametric_circle _ hf s R k).const_mul _

theorem measurable_rectangle_error (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) :
    StronglyMeasurable (fun xi : ℝ => rectangleMoment N p r s xi (error Q xi)) := by
  have hm := fun k => measurable_error_moment Q h16 hR hhalf k
  simp only [rectangleMoment,ZetaRieszMarkedEuler.coeff_leg]
  unfold zetaPrimeFeature
  fun_prop

theorem measurable_rectanglePairError_div (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    StronglyMeasurable (fun xi : ℝ => rectanglePairError Q N p r s L xi/(xi : ℂ)^2) := by
  have hm := measurable_rectangle_error Q h16 N p r hR hhalf
  have hp := hm.measurable
  have hn : Measurable (fun xi : ℝ => rectangleMoment N p r s (-xi) (error Q (-xi))) :=
    hp.comp measurable_neg
  apply Measurable.stronglyMeasurable
  unfold rectanglePairError
  fun_prop

/-- Genuine ordinary integrability of the paired, marked correction,
including its frequency-zero boundary. -/
theorem integrable_rectanglePairError_div (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => rectanglePairError Q N p r s L xi/(xi : ℂ)^2) (Ioi 0) := by
  apply (((CosineHinge.integrable_one_sub_cos_div_sq (Real.log p)).add
    (CosineHinge.integrable_one_sub_cos_div_sq (Real.log r))).const_mul
      (2*rectangleBudget N (s.re-R) R*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r))).mono'
  · exact (measurable_rectanglePairError_div Q h16 N p r hR hhalf L).aestronglyMeasurable
  · exact Eventually.of_forall (norm_rectanglePairError_div_le Q h16 N p r hhead hR hhalf L)

/-- An independent bound after integration pays the full middle Euler
error, preserving both marked logarithms and the correlated orders. -/
theorem integral_norm_rectanglePairError_div_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) (hhead : ∀ p ∈ Q, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    (∫ xi : ℝ in Ioi 0, ‖rectanglePairError Q N p r s L xi/(xi : ℂ)^2‖) ≤
      Real.pi*rectangleBudget N (s.re-R) R*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (Real.log p+Real.log r) := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0, 2*rectangleBudget N (s.re-R) R*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          ((1-Real.cos (Real.log p*xi))/xi^2+(1-Real.cos (Real.log r*xi))/xi^2) :=
      integral_mono_ae (integrable_rectanglePairError_div Q h16 N p r hhead hR hhalf L).norm
        (((CosineHinge.integrable_one_sub_cos_div_sq (Real.log p)).add
          (CosineHinge.integrable_one_sub_cos_div_sq (Real.log r))).const_mul _)
        (Eventually.of_forall (norm_rectanglePairError_div_le Q h16 N p r hhead hR hhalf L))
    _ = _ := by
      rw [integral_const_mul,integral_add (CosineHinge.integrable_one_sub_cos_div_sq _)
        (CosineHinge.integrable_one_sub_cos_div_sq _),
        CosineHinge.integral_one_sub_cos_div_sq,CosineHinge.integral_one_sub_cos_div_sq,
        abs_of_nonneg (Real.log_natCast_nonneg p),abs_of_nonneg (Real.log_natCast_nonneg r)]
      ring

end
end RiemannGaussian.ZetaRieszMarkedEulerError
