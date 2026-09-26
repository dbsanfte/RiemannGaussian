/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughEulerTransfer

/-!
# Frequency boundaries of the retained main Euler quotient

The full main quotient and its two marked factorial slots stay coupled.
Only the frequency exteriors receive norm bounds. The surviving central
integral still requires its signed arithmetic estimate.
-/

namespace RiemannGaussian.ZetaRieszMainFrequency
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound

/-- A common moment bound passes through the exact rectangle, with
one total Cauchy order and both marked Fourier zeros still present. -/
theorem rectangle_bound (F : ℂ → ℂ) (N p r : ℕ) (s : ℂ) (xi : ℝ)
    {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hF : ∀ k, ‖signedTaylorMoment k F s‖ ≤ M/R^k) :
    ‖rectangleMoment N p r s xi F‖ ≤
      ((N : ℝ)+2)^2*(M/R^(N+1))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  let B := (M/R^(N+1))*(zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
    (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖)
  have hB : 0 ≤ B := by dsimp [B]; unfold zetaPrimeExpWeight; positivity
  have ha (j : ℕ) (hj : j ∈ Finset.range (N+2)) (h : ℕ)
      (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
      ‖PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
        signedTaylorMoment (N+1-j-h) F s‖ ≤ B := by
    have he : j+h+(N+1-j-h) = N+1 := by
      have hj' := Finset.mem_range.mp hj
      have hh' := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
      omega
    rw [norm_mul,norm_mul]
    apply (mul_le_mul
      (mul_le_mul (norm_leg_le p j s xi hR) (norm_leg_le r h s xi hR)
        (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity))
      (hF (N+1-j-h)) (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)).trans_eq
    have hp : R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h) = R⁻¹^(N+1) := by
      rw [← pow_add,← pow_add,he]
    dsimp [B]
    simp only [div_eq_mul_inv,← inv_pow]
    calc
      _ = M*(R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by ring
      _ = _ := by rw [hp]
  have hc (j : ℕ) : ((ZetaRieszSkewAllocation.rectangleOrders N j).card : ℝ) ≤ (N : ℝ)+2 := by
    have h := Finset.card_le_card
      (show ZetaRieszSkewAllocation.rectangleOrders N j ⊆ Finset.range (N+1-j+1) from
        Finset.filter_subset _ _)
    rw [Finset.card_range] at h
    exact_mod_cast (show (ZetaRieszSkewAllocation.rectangleOrders N j).card ≤ N+2 by omega)
  unfold rectangleMoment
  calc
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ‖PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
          signedTaylorMoment (N+1-j-h) F s‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ _h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, B :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh => ha j hj h hh))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*B := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hc j) hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; dsimp [B]; ring

/-- The leading product has a uniform Cauchy bound before any
factorial coordinate or Fourier frequency is projected. -/
theorem quotient_moment_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) (k : ℕ) :
    ‖signedTaylorMoment k (quotient Q xi) s‖ ≤ Real.exp (4*mass (s.re-R))/R^k := by
  apply norm_signedTaylorMoment_le hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    exact (analyticAt_quotient Q h16
      (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    exact norm_quotient_le Q h16 hs
      (ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) xi

/-- The remaining main term's common order budget, without any
asserted source saving. -/
def mainBudget (N : ℕ) (sigma R : ℝ) : ℝ :=
  ((N : ℝ)+2)^2*(Real.exp (4*mass sigma)/R^(N+1))

theorem mainBudget_nonneg (N : ℕ) (sigma : ℝ) {R : ℝ} (hR : 0 < R) :
    0 ≤ mainBudget N sigma R := by unfold mainBudget; positivity

theorem ordered_mass_le_square (A : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ A, 0 ≤ f p) :
    (∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p), f p*f r) ≤ (∑ p ∈ A, f p)^2 := by
  calc
    _ ≤ ∑ r ∈ A, ∑ p ∈ A, f p*f r := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => mul_nonneg (hf p hp) (hf r hr))
    _ = _ := by rw [pow_two,Finset.sum_mul]; simp only [Finset.mul_sum];
                exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun p _ => mul_comm _ _))

/-- Marked phases may be bounded only after summing the entire
middle quotient and retaining the exact common moment order. -/
theorem quotientSymbol_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p ∈ A, 0 ≤ f p)
    (hp : ∀ p ∈ A, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖quotientSymbol A N s xi‖ ≤
      mainBudget N (s.re-R) R*(∑ p ∈ A, zetaPrimeExpWeight (s.re-R) p*f p)^2 := by
  have hB := mainBudget_nonneg N (s.re-R) hR
  unfold quotientSymbol
  calc
    _ ≤ ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
        ‖rectangleMoment N p r s xi (quotient (middlePrimes A p r) xi)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p), mainBudget N (s.re-R) R*
        ((zetaPrimeExpWeight (s.re-R) p*f p)*(zetaPrimeExpWeight (s.re-R) r*f r)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro p hp'
      have hpA := (Finset.mem_filter.mp hp').1
      have h := rectangle_bound (quotient (middlePrimes A p r) xi) N p r s xi hR
        (Real.exp_pos _).le (quotient_moment_bound _ (fun q hq => h16 q (Finset.mem_filter.mp hq).1) hR hs xi)
      apply h.trans
      have he := mul_le_mul_of_nonneg_left (mul_le_mul (hp p hpA) (hp r hr)
        (norm_nonneg _) (hf p hpA))
          (mul_nonneg hB (show 0 ≤ zetaPrimeExpWeight (s.re-R) p *
            zetaPrimeExpWeight (s.re-R) r from mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
      convert he using 1
      dsimp [mainBudget]
      ring
    _ ≤ _ := by
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ordered_mass_le_square A _
        (fun p hp => mul_nonneg (Real.exp_pos _).le (hf p hp))) hB

theorem phase_le_two (p : ℕ) (xi : ℝ) : ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by rw [norm_one,norm_character_phase]; norm_num)

theorem phase_le_log (p : ℕ) (xi : ℝ) :
    ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ |xi| * Real.log p := by
  rw [character_phase_eq,norm_sub_rev]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(Real.log p*xi))
  convert h using 1
  · congr 3
    push_cast
    ring
  · rw [Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg p)]
    ring

/-- At the far frequency boundary no prime ordering or count class
has been removed from the response being bounded. -/
theorem quotientSymbol_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖quotientSymbol A N s xi‖ ≤ 4*mainBudget N (s.re-R) R*mass (s.re-R)^2 := by
  apply (quotientSymbol_bound A h16 N hR hs xi (fun _ => 2) (fun _ _ => by norm_num)
    (fun p _ => phase_le_two p xi)).trans
  rw [← Finset.sum_mul]
  have he := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by unfold zetaPrimeExpWeight; positivity : 0 ≤ (∑ p ∈ A, zetaPrimeExpWeight (s.re-R) p)*2)
      (mul_le_mul_of_nonneg_right (sum_mass_le A hs) (by norm_num : (0 : ℝ) ≤ 2)) 2)
    (mainBudget_nonneg N (s.re-R) hR)
  convert he using 1
  ring

/-- At frequency zero the two actual marked phases give a quadratic
zero, with a finite logarithmic prime mass. -/
theorem quotientSymbol_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖quotientSymbol A N s xi‖ ≤ mainBudget N (s.re-R) R*logMass (s.re-R)^2*xi^2 := by
  apply (quotientSymbol_bound A h16 N hR hs xi (fun p => |xi| * Real.log p)
    (fun p _ => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg _))
    (fun p _ => phase_le_log p xi)).trans
  have he : (∑ p ∈ A, zetaPrimeExpWeight (s.re-R) p*(|xi| * Real.log p)) =
      |xi| * (∑ p ∈ A, Real.log p*zetaPrimeExpWeight (s.re-R) p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [he]
  have hm := mul_le_mul_of_nonneg_left (sum_logMass_le A hs) (abs_nonneg xi)
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg (abs_nonneg xi) (Finset.sum_nonneg (fun p _ =>
      mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le))) hm 2)
    (mainBudget_nonneg N (s.re-R) hR)
  simpa only [zetaPrimeExpWeight,mul_pow,sq_abs,mul_assoc,mul_left_comm,mul_comm] using hb

/-- The original two Fourier signs retain the same uniform large-frequency
bound; no phase of the arithmetic response is replaced. -/
theorem quotientPair_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L xi : ℝ) :
    ‖quotientPair A N s L xi‖ ≤ 8*mainBudget N (s.re-R) R*mass (s.re-R)^2 := by
  unfold quotientPair
  apply (norm_add_le _ _).trans
  simpa only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul] using
    add_le_add (quotientSymbol_large A h16 N hR hs xi)
      (quotientSymbol_large A h16 N hR hs (-xi)) |>.trans_eq (by ring)

theorem quotientPair_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L xi : ℝ) :
    ‖quotientPair A N s L xi‖ ≤ 2*mainBudget N (s.re-R) R*logMass (s.re-R)^2*xi^2 := by
  unfold quotientPair
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  have h := add_le_add (quotientSymbol_small A h16 N hR hs xi)
    (quotientSymbol_small A h16 N hR hs (-xi))
  simpa only [neg_sq,two_mul,add_mul] using h

theorem quotientPair_div_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L xi : ℝ) :
    ‖quotientPair A N s L xi/(xi : ℂ)^2‖ ≤
      (8*mainBudget N (s.re-R) R*mass (s.re-R)^2)/xi^2 := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact div_le_div_of_nonneg_right (quotientPair_large A h16 N hR hs L xi) (sq_nonneg xi)

theorem quotientPair_div_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L xi : ℝ) :
    ‖quotientPair A N s L xi/(xi : ℂ)^2‖ ≤
      2*mainBudget N (s.re-R) R*logMass (s.re-R)^2 := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  by_cases hx : xi = 0
  · simp only [hx,zero_pow (by decide : 2 ≠ 0),div_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (mainBudget_nonneg N _ hR)) (sq_nonneg _)
  · exact (div_le_div_of_nonneg_right (quotientPair_small A h16 N hR hs L xi)
      (sq_nonneg xi)).trans_eq (mul_div_cancel_right₀ _ (pow_ne_zero _ hx))

/-- The actual near-zero integral. Its quadratic Fourier zero is kept
until after the division by frequency squared. -/
theorem norm_small_integral_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R)
    (L : ℝ) {eps : ℝ} (heps : 0 ≤ eps) :
    ‖∫ xi : ℝ in (0 : ℝ)..eps, quotientPair A N s L xi/(xi : ℂ)^2‖ ≤
      2*mainBudget N (s.re-R) R*logMass (s.re-R)^2*eps := by
  simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg heps] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := eps) (fun xi _ => quotientPair_div_small A h16 N hR hs L xi)

theorem rpow_neg_two_eq (xi : ℝ) : xi^(-2 : ℝ) = (xi^2)⁻¹ := by
  simp

theorem inv_square_integral {X : ℝ} (hX : 0 < X) :
    (∫ xi : ℝ in Ioi X, (xi^2)⁻¹) = X⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hX
  simpa only [rpow_neg_two_eq,show (-2 : ℝ)+1 = -1 by norm_num,
    Real.rpow_neg_one,neg_div,div_neg,div_one,neg_neg] using h

theorem norm_large_integral_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R)
    (L : ℝ) {X : ℝ} (hX : 0 < X) :
    ‖∫ xi : ℝ in Ioi X, quotientPair A N s L xi/(xi : ℂ)^2‖ ≤
      (8*mainBudget N (s.re-R) R*mass (s.re-R)^2)/X := by
  have hi : IntegrableOn (fun xi : ℝ => (xi^2)⁻¹) (Ioi X) := by
    simpa only [rpow_neg_two_eq] using
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hX
  have h := norm_integral_le_of_norm_le (hi.const_mul
    (8*mainBudget N (s.re-R) R*mass (s.re-R)^2))
    (Filter.Eventually.of_forall (fun xi => by
      simpa only [div_eq_mul_inv] using quotientPair_div_large A h16 N hR hs L xi))
  simpa only [integral_const_mul,inv_square_integral hX,div_eq_mul_inv] using h

/-- The signed central frequency integral, with the same prime ordering,
factorial rectangle and logarithmic-mark prefactor as the full response. -/
def centralResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L eps X : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in eps..X, quotientPair A N s L xi/(xi : ℂ)^2

/-- Both exterior frequency pieces of that exact same response. -/
def exteriorResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L eps X : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ((∫ xi : ℝ in (0 : ℝ)..eps, quotientPair A N s L xi/(xi : ℂ)^2)+
      ∫ xi : ℝ in Ioi X, quotientPair A N s L xi/(xi : ℂ)^2)

/-- No sign or source term is lost at either boundary. -/
theorem response_split_frequency (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ)
    {eps X : ℝ} (heps : 0 ≤ eps) (hX : 0 ≤ X) :
    quotientResponse A N s L = centralResponse A N s L eps X+
      exteriorResponse A N s L eps X := by
  have hi := integrable_quotientPair A hA h16 N hhead hR hs L
  have hiE := hi.mono_set (Ioi_subset_Ioi heps)
  have hiX := hi.mono_set (Ioi_subset_Ioi hX)
  have h0 := intervalIntegral.integral_interval_add_Ioi hi hiE
  have h1 := intervalIntegral.integral_interval_add_Ioi hiE hiX
  unfold quotientResponse centralResponse exteriorResponse
  rw [← h0,← h1]
  ring

theorem norm_exteriorResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R)
    {L eps X : ℝ} (hL : 1 ≤ L) (heps : 0 ≤ eps) (hX : 0 < X) :
    ‖exteriorResponse A N s L eps X‖ ≤
      ((N : ℝ)+1)*mainBudget N (s.re-R) R*
        (2*logMass (s.re-R)^2*eps+8*mass (s.re-R)^2/X) := by
  have hL0 : 0 < L := by linarith
  have hden : 1 ≤ 2*Real.pi*L := by nlinarith [Real.pi_gt_three]
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) hden
  unfold exteriorResponse
  rw [norm_mul]
  apply (mul_le_mul hpref (norm_add_le _ _) (norm_nonneg _) (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (norm_small_integral_le A h16 N hR hs L heps)
    (norm_large_integral_le A h16 N hR hs L hX)) (by positivity : 0 ≤ (N : ℝ)+1)).trans_eq
  ring

/-- The exterior cuts are deliberately generous: their exponential rate
beats the source growth using only a safe arithmetic Cauchy circle. -/
theorem norm_scaled_exterior_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R u U L : ℝ} (hR : 0 < R) (hs : 1 < s.re-R)
    (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*exteriorResponse A N s L
      (Real.exp (-(N : ℝ)/220)) (Real.exp ((N : ℝ)/220))‖ ≤
      (Real.exp (4*mass (s.re-R))*(2*logMass (s.re-R)^2+8*mass (s.re-R)^2)*(U/R))*
        ((N : ℝ)+2)^3*(U/R*Real.exp (-(1 : ℝ)/220))^N := by
  have hU0 := hu.trans hU
  have hB := mainBudget_nonneg N (s.re-R) hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_exteriorResponse_le A h16 N hR hs hL (Real.exp_pos _).le (Real.exp_pos _))
    (norm_nonneg _) (pow_nonneg hU0 _)).trans
  have he : 2*logMass (s.re-R)^2*Real.exp (-(N : ℝ)/220)+
      8*mass (s.re-R)^2/Real.exp ((N : ℝ)/220) =
      (2*logMass (s.re-R)^2+8*mass (s.re-R)^2)*Real.exp (-(N : ℝ)/220) := by
    rw [show -(N : ℝ)/220 = -((N : ℝ)/220) by ring,Real.exp_neg]
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show (N : ℝ)+1 ≤ N+2 by linarith) hB) (by positivity)) (pow_nonneg hU0 _)).trans_eq
  have hexp : Real.exp (-(N : ℝ)/220) = Real.exp (-(1 : ℝ)/220)^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold mainBudget
  rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ R]
  field_simp

/-- The actual two frequency exteriors vanish at source scale, uniformly
in moving heights and in the entire ordered finite prime set. -/
theorem tendsto_exteriorResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p)
    (height length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*exteriorResponse (A N) N
      (3/2+Complex.I*height N) (length N)
      (Real.exp (-(N : ℝ)/220)) (Real.exp ((N : ℝ)/220))) atTop (nhds 0) := by
  have hr := sourceRate_bounds
  have hr1 : sourceRate < 1 := lt_trans hr.2 (by norm_num)
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr.1 hr1
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr.1 hr1
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.1 hr1
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hr.1 hr1
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*sourceRate^N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
    · ext N; simp only [pow_zero,pow_one]; ring
    · norm_num
  have hs (N : ℕ) : (3/2+Complex.I*(height N : ℂ)).re-safeRadius = 1+1/262144 := by
    norm_num [safeRadius]
  let C : ℝ := Real.exp (4*mass (1+1/262144))*
    (2*logMass (1+1/262144)^2+8*mass (1+1/262144)^2)*
    (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm (a := fun N : ℕ => C*(((N : ℝ)+2)^3*sourceRate^N))
  · intro N
    have h := norm_scaled_exterior_le (A N) (h16 N) N safeRadius_pos
      (show 1 < (3/2+Complex.I*(height N : ℂ)).re-safeRadius by rw [hs]; norm_num) hu hU (hL N)
    simpa only [hs,sourceRate,mul_assoc,C] using h
  · simpa only [mul_zero] using ht.const_mul C

/-- The literal leading response restricted to the central frequency
band. This is a restriction of the same coupled arithmetic integrand. -/
def centralMain (u y : ℝ) (N : ℕ) : ℂ :=
  centralResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N (3/2+Complex.I*y)
    (SquarefreeVaughanLogSource.length u N)
    (Real.exp (-(N : ℝ)/220)) (Real.exp ((N : ℝ)/220))

theorem main_sub_central (u y : ℝ) (N : ℕ) :
    ZetaRieszRoughEulerTransfer.mainQuotient u y N-centralMain u y N =
      exteriorResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N (3/2+Complex.I*y)
        (SquarefreeVaughanLogSource.length u N)
        (Real.exp (-(N : ℝ)/220)) (Real.exp ((N : ℝ)/220)) := by
  unfold ZetaRieszRoughEulerTransfer.mainQuotient centralMain
  rw [response_split_frequency _ (fun _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp) N
    (fun _ hp => ZetaRieszRoughEulerTransfer.rough_head hp) safeRadius_pos
    (by norm_num [safeRadius]) _ (Real.exp_pos _).le (Real.exp_pos _).le,
    add_sub_cancel_left]

theorem tendsto_main_sub_central {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (ZetaRieszRoughEulerTransfer.mainQuotient u (height N) N-centralMain u (height N) N))
      atTop (nhds 0) := by
  simp_rw [main_sub_central]
  exact tendsto_exteriorResponse (ZetaRieszRoughEulerTransfer.roughPrimes u)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp)
    height (SquarefreeVaughanLogSource.length u)
    (ZetaRieszHeadOrders.one_le_length u) hu hU

/-- The original signed counts 3..55 minus short overflow 3..13 have
the same source-scale value as the central ordered quotient. Both frequency
exteriors and the full Euler correction are paid, independently of zeros.
No estimate for the remaining central signed integral is assumed or proved. -/
theorem tendsto_central_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (centralMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := (ZetaRieszRoughEulerTransfer.tendsto_main_sub_current hu hU y).sub
    ((tendsto_main_sub_central (by linarith : 0 ≤ u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_self] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszMainFrequency
