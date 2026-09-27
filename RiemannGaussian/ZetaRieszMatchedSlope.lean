/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOrderedWard

/-!
# Matching the marked logarithmic slope to its ordered Euler cofactor

The extra local prime powers and the wrong high/least-prime ordering are
paid at the exact factorial rectangle. The result retains the same finite
Euler quotient in the marked slope and in the cofactor. No order window is
completed, and no main signed bound is assumed.
-/

namespace RiemannGaussian.ZetaRieszMatchedSlope
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound
open ZetaRieszMainFrequency ZetaRieszMarkedSeparation ZetaRieszRoughEulerTransfer
open ZetaRieszMarkedPrimeCompletion ZetaRieszMarkedLogDerivative ZetaRieszOrderedWard

/-- The first-prime term of the finite logarithmic Euler slope. -/
def firstSlope (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ Q, (Real.log p : ℂ)*(1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeFeature s p

/-- The exact extra local prime-power terms, before differentiation. -/
def powerSlope (Q : Finset ℕ) (xi : ℝ) (s : ℂ) : ℂ := eulerSlope Q xi s-firstSlope Q xi s

theorem local_power_identity {q z : ℂ} (hq : 1-q ≠ 0) (hz : 1-q*z ≠ 0) :
    q/(1-q)-q*z/(1-q*z)-q*(1-z) =
      q^2*(1-z)*(1+z-q*z)/((1-q)*(1-q*z)) := by
  field_simp
  ring

/-- Both frequencies survive in the local quadratic prime-power error. -/
theorem norm_local_power_le {q z : ℂ} (hq : ‖q‖ ≤ 1/4) (hz : ‖z‖ ≤ 1) :
    ‖q/(1-q)-q*z/(1-q*z)-q*(1-z)‖ ≤ 4*‖q‖^2*‖1-z‖ := by
  have hd := ZetaRieszEulerQuotient.local_denominator_bound hq hz
  have he := ZetaRieszEulerQuotient.local_denominator_bound hq
    (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)
  simp only [mul_one] at he
  have hd0 : 1-q*z ≠ 0 := norm_pos_iff.mp (by linarith)
  have he0 : 1-q ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn : ‖1+z-q*z‖ ≤ 9/4 := by
    apply (norm_sub_le _ _).trans
    have h := norm_add_le (1 : ℂ) z
    rw [norm_one] at h
    rw [norm_mul]
    nlinarith [norm_nonneg q,norm_nonneg z]
  rw [local_power_identity he0 hd0,norm_div,norm_mul,norm_mul,norm_mul,norm_pow]
  apply (div_le_iff₀ (mul_pos (by linarith : 0 < ‖1-q‖) (by linarith : 0 < ‖1-q*z‖))).mpr
  have hden : 9/16 ≤ ‖1-q‖*‖1-q*z‖ := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 4*‖q‖^2*‖1-z‖ by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ ‖q‖^2*‖1-z‖ by positivity)]

theorem analyticAt_firstSlope (Q : Finset ℕ) (xi : ℝ) (s : ℂ) :
    AnalyticAt ℂ (firstSlope Q xi) s := by
  apply Finset.analyticAt_fun_sum
  intro p _hp
  unfold zetaPrimeFeature
  fun_prop

theorem analyticAt_eulerSlope (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : AnalyticAt ℂ (eulerSlope Q xi) s := by
  apply Finset.analyticAt_fun_sum
  intro p hp
  have hf : AnalyticAt ℂ (fun z => zetaPrimeFeature z p) s := by unfold zetaPrimeFeature; fun_prop
  have hd := local_denominators (h16 p hp) hs xi
  exact analyticAt_const.mul ((hf.div (analyticAt_const.sub hf) hd.1).sub
    ((hf.mul analyticAt_const).div (analyticAt_const.sub (hf.mul analyticAt_const)) hd.2))

theorem analyticAt_powerSlope (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : AnalyticAt ℂ (powerSlope Q xi) s :=
  (analyticAt_eulerSlope Q h16 hs xi).sub (analyticAt_firstSlope Q xi s)

theorem norm_powerSlope_le (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} (hs : 3/4 ≤ s.re) (xi : ℝ) (f : ℕ → ℝ) (_hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖powerSlope Q xi s‖ ≤ 4*∑ p ∈ Q, Real.log p*zetaPrimeExpWeight (3/2) p*f p := by
  have he (p : ℕ) : localSlope p xi s-
      (Real.log p : ℂ)*(1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeFeature s p =
      (Real.log p : ℂ)*(zetaPrimeFeature s p/(1-zetaPrimeFeature s p)-
        zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p/
          (1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)-
        zetaPrimeFeature s p*(1-zetaPrimeFeature (Complex.I*xi) p)) := by unfold localSlope; ring
  unfold powerSlope eulerSlope firstSlope
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.log_natCast_nonneg p)]
  have hw : ‖zetaPrimeFeature s p‖^2 ≤ zetaPrimeExpWeight (3/2) p := by
    rw [norm_zetaPrimeFeature,zetaPrimeExpWeight,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hs (Real.log_natCast_nonneg p)]
  have h := (norm_local_power_le
    (ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter (by linarith) (h16 p hp))
    (norm_character_phase xi p).le).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 4))
      (hphase p) (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity))
  exact (mul_le_mul_of_nonneg_left h (Real.log_natCast_nonneg p)).trans_eq (by ring)

/-- The larger Cauchy circle is uniform in the finite ordered prime set. -/
theorem powerSlope_moment_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (k : ℕ) (y xi : ℝ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖signedTaylorMoment k (powerSlope Q xi) (3/2+Complex.I*y)‖ ≤
      (4*∑ p ∈ Q, Real.log p*zetaPrimeExpWeight (3/2) p*f p)/(3/4 : ℝ)^k := by
  apply norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 3/4)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by norm_num : (3/4 : ℝ) ≠ 0)]
    intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound hz
    norm_num at hd
    exact (analyticAt_powerSlope Q h16 (by linarith) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    have hd := ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)
    norm_num at hd
    exact norm_powerSlope_le Q h16 (by linarith) xi f hf hphase

/-- The finite marked slope, with the exact reciprocal marked order. -/
def slopeMark (Q : Finset ℕ) : ℕ → ℂ → ℝ → ℂ
  | 0, s, xi => primeDifference Q 0 s xi
  | k+1, s, xi => signedTaylorMoment k (eulerSlope Q xi) s/(k+1)

/-- The finite extra-power mark, at the same factorial normalization. -/
def powerMark (Q : Finset ℕ) : ℕ → ℂ → ℝ → ℂ
  | 0, _, _ => 0
  | k+1, s, xi => signedTaylorMoment k (powerSlope Q xi) s/(k+1)

theorem moment_firstSlope (Q : Finset ℕ) (k : ℕ) (s : ℂ) (xi : ℝ) :
    signedTaylorMoment k (firstSlope Q xi) s = ((k+1 : ℕ) : ℂ)*primeDifference Q (k+1) s xi := by
  change signedTaylorMoment k (fun z => ∑ p ∈ Q,
    (Real.log p : ℂ)*(1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeFeature z p) s = _
  rw [signedTaylorMoment_sum Q k _ (fun p _ => by unfold zetaPrimeFeature; fun_prop)]
  simp only [signedTaylorMoment_const_mul,ZetaRieszFilteredCompletion.signedTaylorMoment_feature,
    primeDifference,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← coeff_leg_difference,coeff_leg]
  unfold zetaPrimeLogKernel
  simp only [Nat.factorial_succ,Nat.cast_mul,pow_succ,Nat.cast_add,Nat.cast_one]
  have hk : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

theorem slopeMark_split (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (j : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    slopeMark Q j s xi = primeDifference Q j s xi+powerMark Q j s xi := by
  cases j with
  | zero => simp [slopeMark,powerMark]
  | succ k =>
    have he : eulerSlope Q xi = fun z => firstSlope Q xi z+powerSlope Q xi z := by
      funext z; unfold powerSlope; ring
    rw [slopeMark,powerMark,he,signedTaylorMoment_add k (analyticAt_firstSlope Q xi s)
      (analyticAt_powerSlope Q h16 hs xi),moment_firstSlope,add_div]
    have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at hk ⊢
    field_simp

/-- Every finite extra-power mark is exponentially negligible in the
original rectangle, still with its Fourier zero intact. -/
theorem powerMark_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) (N j h : ℕ)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (y xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖powerMark Q j (3/2+Complex.I*y) xi‖ ≤
      Real.exp (-(N : ℝ)/10)*safeRadius⁻¹^j*
        (4*∑ p ∈ Q, Real.log p*zetaPrimeExpWeight (3/2) p*f p) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (marked_order_pos hh))
  rw [powerMark,norm_div]
  have hk : 1 ≤ ‖((k : ℂ)+1)‖ := by norm_cast; omega
  apply (div_le_self (norm_nonneg _) hk).trans
  apply (powerSlope_moment_bound Q h16 k y xi f hf hphase).trans
  rw [div_eq_mul_inv,← inv_pow,mul_comm]
  exact mul_le_mul_of_nonneg_right (proper_radius_saving hh)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ =>
      mul_nonneg (mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le) (hf p))))

/-- The ordinary prime difference splits at the actual least-prime
order, before any bound or completion is applied. -/
theorem primeDifference_tail_split (A : Finset ℕ) (r j : ℕ) (s : ℂ) (xi : ℝ) :
    primeDifference A j s xi = primeDifference (tailPrimes A r) j s xi+
      ∑ p ∈ A.filter (fun p => p ≤ r), PowerSeries.coeff j (leg s xi p) := by
  simp only [primeDifference,tailPrimes,Finset.sum_filter,coeff_leg_difference]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpr : r < p
  · simp [hpr,show ¬p ≤ r by omega]
  · simp [hpr,show p ≤ r by omega]

/-- A single low marked leg remains coupled to every middle order. -/
theorem low_cofactor_bound (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N j h r : ℕ) (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    (y xi : ℝ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖PowerSeries.coeff h (leg (3/2+Complex.I*y) xi r)*
      signedTaylorMoment (N+1-j-h) (quotient Q xi) (3/2+Complex.I*y)‖ ≤
      Real.exp (4*mass (3/2-safeRadius))*safeRadius⁻¹^(N+1-j)*
        (zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by
  have he : h+(N+1-j-h) = N+1-j := by
    have hh' := Finset.mem_range.mp (Finset.mem_filter.mp hh).1; omega
  have hR := safeRadius_pos
  have hl := (norm_leg_le r h (3/2+Complex.I*y) xi hR).trans
    (mul_le_mul_of_nonneg_right (hphase r) (by unfold zetaPrimeExpWeight; positivity))
  have hm := quotient_moment_bound Q h16 hR
    (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi (N+1-j-h)
  rw [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at hl hm
  have hfr := hf r
  rw [norm_mul]
  apply (mul_le_mul hl hm (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)).trans_eq
  simp only [div_eq_mul_inv,← inv_pow]
  calc
    _ = Real.exp (4*mass (3/2-safeRadius))*
      (safeRadius⁻¹^h*safeRadius⁻¹^(N+1-j-h))*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by ring
    _ = _ := by rw [← pow_add,he]; simp only [div_eq_mul_inv]

/-- The marked logarithmic derivative now belongs to precisely the
same finite ordered Euler product as its middle cofactor. -/
def matchedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    ∑ r ∈ A, slopeMark (tailPrimes A r) j s xi*PowerSeries.coeff h (leg s xi r)*
      signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s

/-- The exact signed mismatch at one retained factorial allocation. -/
def mismatchAtom (A : Finset ℕ) (N j h r : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (slopeMark (tailPrimes A r) j s xi-primeDifference A j s xi)*
    PowerSeries.coeff h (leg s xi r)*
      signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s

theorem matchedSymbol_difference (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    matchedSymbol A N s xi-separatedSymbol A N s xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ∑ r ∈ A, mismatchAtom A N j h r s xi := by
  rw [separatedSymbol_factor]
  simp only [matchedSymbol,mismatchAtom,Finset.mul_sum,Finset.sum_sub_distrib,sub_mul,mul_assoc]

/-- Exact splitting of the mismatch into local extra prime powers
and the forbidden high/least-prime ordering. -/
theorem mismatchAtom_split (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h r : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    mismatchAtom A N j h r s xi =
      powerMark (tailPrimes A r) j s xi*PowerSeries.coeff h (leg s xi r)*
        signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s-
      ∑ p ∈ A.filter (fun p => p ≤ r),
        PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
          signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s := by
  rw [mismatchAtom,slopeMark_split (tailPrimes A r) (fun p hp => h16 p (Finset.mem_filter.mp hp).1) j hs,
    primeDifference_tail_split A r j s xi]
  rw [← Finset.sum_mul,← Finset.sum_mul]
  ring

theorem mismatchAtom_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h r : ℕ) (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (y xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    {V : ℝ} (hV : (∑ p ∈ A, zetaPrimeExpWeight (3/2-safeRadius) p*f p) ≤ V)
    (hPV : (4*∑ p ∈ A, Real.log p*zetaPrimeExpWeight (3/2) p*f p) ≤ V) :
    ‖mismatchAtom A N j h r (3/2+Complex.I*y) xi‖ ≤
      (2*Real.exp (4*mass (3/2-safeRadius))*Real.exp (-(N : ℝ)/10)/safeRadius^(N+1))*
        V*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by
  have hR := safeRadius_pos
  have hv0 : 0 ≤ V := (Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  have htail : ∀ p ∈ tailPrimes A r, 16 ≤ p := fun p hp => h16 p (Finset.mem_filter.mp hp).1
  have hpv : (4*∑ p ∈ tailPrimes A r, Real.log p*zetaPrimeExpWeight (3/2) p*f p) ≤ V := by
    apply le_trans _ hPV
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => mul_nonneg (mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le) (hf p))
  let B := Real.exp (4*mass (3/2-safeRadius))*Real.exp (-(N : ℝ)/10)/safeRadius^(N+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfirst : ‖powerMark (tailPrimes A r) j (3/2+Complex.I*y) xi*
      PowerSeries.coeff h (leg (3/2+Complex.I*y) xi r)*
        signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) (3/2+Complex.I*y)‖ ≤
      B*V*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by
    have hp := (powerMark_bound _ htail N j h hh y xi f hf hphase).trans
      (mul_le_mul_of_nonneg_left hpv (by positivity))
    have hl := low_cofactor_bound _ htail N j h r hh y xi f hf hphase
    rw [mul_assoc,norm_mul]
    apply (mul_le_mul hp hl (norm_nonneg _) (by positivity)).trans_eq
    have he : j+(N+1-j) = N+1 := by have := Finset.mem_range.mp hj; omega
    dsimp [B]
    simp only [div_eq_mul_inv,← inv_pow]
    calc
      _ = Real.exp (4*mass (3/2-safeRadius))*Real.exp (-(N : ℝ)/10)*
        (safeRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*V*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by ring
      _ = _ := by rw [← pow_add,he]; ring
  have hsecond : ‖∑ p ∈ A.filter (fun p => p ≤ r),
      PowerSeries.coeff j (leg (3/2+Complex.I*y) xi p)*
        PowerSeries.coeff h (leg (3/2+Complex.I*y) xi r)*
          signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) (3/2+Complex.I*y)‖ ≤
      B*V*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by
    calc
      _ ≤ ∑ p ∈ A.filter (fun p => p ≤ r),
          B*(zetaPrimeExpWeight (3/2-safeRadius) p*f p)*(zetaPrimeExpWeight (3/2-safeRadius) r*f r) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro p hp
        have h := wrong_order_atom (quotient (tailPrimes A r) xi) N p r j h (3/2+Complex.I*y) xi
          (by have := h16 p (Finset.mem_filter.mp hp).1; omega) (Finset.mem_filter.mp hp).2
          hj hh hR (Real.exp_pos _).le
          (quotient_moment_bound _ htail hR
            (show 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius by norm_num [safeRadius]) xi)
        simp only [show (3/2+Complex.I*(y : ℂ)).re = 3/2 by norm_num] at h
        apply h.trans
        have hp' := mul_le_mul (hphase p) (hphase r) (norm_nonneg _) (hf p)
        exact (mul_le_mul_of_nonneg_left hp' (by unfold zetaPrimeExpWeight; positivity)).trans_eq
          (by dsimp [B]; ring)
      _ ≤ _ := by
        rw [← Finset.sum_mul,← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le (hf r))
        apply mul_le_mul_of_nonneg_left _ hB
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  rw [mismatchAtom_split A h16 N j h r (by norm_num : (1/2 : ℝ) ≤ (3/2+Complex.I*(y : ℂ)).re)]
  exact (norm_sub_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by dsimp [B]; ring))

/-- The mismatch is paid after summing every retained least prime
and every factorial allocation. -/
theorem matchedSymbol_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    {V : ℝ} (hV : (∑ p ∈ A, zetaPrimeExpWeight (3/2-safeRadius) p*f p) ≤ V)
    (hPV : (4*∑ p ∈ A, Real.log p*zetaPrimeExpWeight (3/2) p*f p) ≤ V) :
    ‖matchedSymbol A N (3/2+Complex.I*y) xi-separatedSymbol A N (3/2+Complex.I*y) xi‖ ≤
      2*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*V^2 := by
  have hR := safeRadius_pos
  have hv0 : 0 ≤ V := (Finset.sum_nonneg (fun p _ => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  let B := (2*Real.exp (4*mass (3/2-safeRadius))*Real.exp (-(N : ℝ)/10)/safeRadius^(N+1))*V^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  rw [matchedSymbol_difference]
  apply (rectangle_sum_bound N _ hB (fun j hj h hh => ?_)).trans_eq (by dsimp [B,mainBudget]; ring)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun r _ => mismatchAtom_bound A h16 N j h r hj hh y xi f hf hphase hV hPV)).trans
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left hV (by positivity)).trans_eq
  dsimp [B]
  ring

/-- The second logarithm used at the Fourier origin is summable. -/
theorem logSquared_weight_bound (p : ℕ) :
    (Real.log p)^2*zetaPrimeExpWeight (3/2) p ≤ 32*zetaPrimeExpWeight (5/4) p := by
  have h := norm_zetaPrimeLogKernel_le 2 (3/2 : ℂ) p (by norm_num : (0 : ℝ) < 1/4)
  norm_num [norm_zetaPrimeLogKernel] at h
  nlinarith

theorem sum_logSquared_weight_le (A : Finset ℕ) :
    (∑ p ∈ A, (Real.log p)^2*zetaPrimeExpWeight (3/2) p) ≤ 32*mass (5/4) := by
  apply (Finset.sum_le_sum (fun p _ => logSquared_weight_bound p)).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_mass_le A (by norm_num : (1 : ℝ) < 5/4)) (by norm_num)

/-- A common mass envelope for the two explicitly paid error channels. -/
def matchedMass : ℝ := mass (3/2-safeRadius)+4*logMass (3/2)

/-- The common logarithmic envelope retains the two Fourier zeros. -/
def matchedLogMass : ℝ := logMass (3/2-safeRadius)+128*mass (5/4)

theorem matchedMass_nonneg : 0 ≤ matchedMass :=
  add_nonneg (mass_nonneg _) (mul_nonneg (by norm_num) (logMass_nonneg (by norm_num)))

theorem matchedLogMass_nonneg : 0 ≤ matchedLogMass :=
  add_nonneg (logMass_nonneg (by norm_num [safeRadius])) (mul_nonneg (by norm_num) (mass_nonneg _))

theorem matchedSymbol_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ) :
    ‖matchedSymbol A N (3/2+Complex.I*y) xi-separatedSymbol A N (3/2+Complex.I*y) xi‖ ≤
      8*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*matchedMass^2 := by
  have hs : 1 < (3/2 : ℝ)-safeRadius := by norm_num [safeRadius]
  have h := matchedSymbol_bound A h16 N y xi (fun _ => 2) (fun _ => by norm_num)
    (fun p => phase_le_two p xi) (V := 2*matchedMass)
    (by rw [← Finset.sum_mul]; unfold matchedMass
        nlinarith [sum_mass_le A hs,logMass_nonneg (by norm_num : (1 : ℝ) < 3/2)])
    (by rw [← Finset.sum_mul]; unfold matchedMass
        nlinarith [sum_logMass_le A (by norm_num : (1 : ℝ) < 3/2),mass_nonneg (3/2-safeRadius)])
  convert h using 1
  ring

theorem matchedSymbol_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y xi : ℝ) :
    ‖matchedSymbol A N (3/2+Complex.I*y) xi-separatedSymbol A N (3/2+Complex.I*y) xi‖ ≤
      2*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*matchedLogMass^2*xi^2 := by
  have hs : 1 < (3/2 : ℝ)-safeRadius := by norm_num [safeRadius]
  have hV : (∑ p ∈ A, zetaPrimeExpWeight (3/2-safeRadius) p*(|xi| *Real.log p)) ≤
      |xi| *matchedLogMass := by
    simp_rw [show ∀ p : ℕ, zetaPrimeExpWeight (3/2-safeRadius) p*(|xi| *Real.log p) =
      |xi| *(Real.log p*zetaPrimeExpWeight (3/2-safeRadius) p) from fun p => by ring]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((sum_logMass_le A hs).trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (mass_nonneg _)))) (abs_nonneg xi)
  have hPV : (4*∑ p ∈ A, Real.log p*zetaPrimeExpWeight (3/2) p*(|xi| *Real.log p)) ≤
      |xi| *matchedLogMass := by
    simp_rw [show ∀ p : ℕ, Real.log p*zetaPrimeExpWeight (3/2) p*(|xi| *Real.log p) =
      |xi| *((Real.log p)^2*zetaPrimeExpWeight (3/2) p) from fun p => by ring]
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (sum_logSquared_weight_le A) (abs_nonneg xi)
    have hlog := mul_nonneg (abs_nonneg xi) (logMass_nonneg hs)
    dsimp [matchedLogMass]
    nlinarith
  have h := matchedSymbol_bound A h16 N y xi (fun p => |xi| *Real.log p)
    (fun p => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg p))
    (fun p => phase_le_log p xi) hV hPV
  simpa only [mul_pow,sq_abs,mul_assoc,mul_comm,mul_left_comm] using h

/-- Both Riesz phases of the matched finite logarithmic response. -/
def matchedPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*matchedSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*matchedSymbol A N s (-xi)

theorem matchedPair_difference (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) :
    matchedPair A N s L xi-separatedPair A N s L xi =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*(matchedSymbol A N s xi-separatedSymbol A N s xi)+
        Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*(matchedSymbol A N s (-xi)-separatedSymbol A N s (-xi)) := by
  unfold matchedPair separatedPair
  ring

theorem matchedPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ) (y L xi : ℝ) :
    ‖(matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi)/(xi : ℂ)^2‖ ≤
      (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (4*matchedLogMass^2+16*matchedMass^2))*(1+xi^2)⁻¹ := by
  have hB := mainBudget_nonneg N (3/2-safeRadius) safeRadius_pos
  have hl : ‖matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi‖ ≤
      16*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*matchedMass^2 := by
    rw [matchedPair_difference]
    apply (norm_add_le _ _).trans
    simpa only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul] using
      (add_le_add (matchedSymbol_large A h16 N y xi)
        (matchedSymbol_large A h16 N y (-xi))).trans_eq (by ring)
  have hn : ‖matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi‖ ≤
      (4*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*matchedLogMass^2)*xi^2 := by
    rw [matchedPair_difference]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    have h := add_le_add (matchedSymbol_small A h16 N y xi) (matchedSymbol_small A h16 N y (-xi))
    simp only [neg_sq] at h
    convert h using 1
    ring
  exact (norm_div_square_profile (by positivity) (by positivity) hn hl).trans_eq (by ring)

theorem measurable_slopeMark (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p) (j : ℕ) (y : ℝ) :
    Measurable (fun xi : ℝ => slopeMark Q j (3/2+Complex.I*y) xi) := by
  cases j with
  | zero =>
    simp only [slopeMark,primeDifference]
    apply Finset.measurable_fun_sum
    intro p _hp
    unfold zetaPrimeLogKernel zetaPrimeFeature
    fun_prop
  | succ k =>
    have hm : StronglyMeasurable (fun v : ℝ × ℂ => eulerSlope Q v.1 v.2) := by
      apply Measurable.stronglyMeasurable
      unfold eulerSlope localSlope zetaPrimeFeature
      fun_prop
    have he (xi : ℝ) := ZetaRieszEulerMoments.signedTaylorMoment_eq_circleIntegral safeRadius_pos
      (f := eulerSlope Q xi) (s := 3/2+Complex.I*y) (show DiffContOnCl ℂ _ (Metric.ball _ safeRadius) from by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball _ safeRadius_pos.ne']
        intro z hz
        have hd := ZetaRieszEulerMoments.disc_re_lower_bound hz
        norm_num [safeRadius] at hd
        exact (analyticAt_eulerSlope Q h16 (by linarith) xi).differentiableAt.differentiableWithinAt) k
    simp_rw [slopeMark,he]
    exact ((ZetaRieszEulerMoments.stronglyMeasurable_parametric_circle _ hm _ _ _).const_mul _).measurable.div_const _

theorem measurable_matchedPair_difference (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    Measurable (fun xi : ℝ =>
      (matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi)/(xi : ℂ)^2) := by
  have hs : 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius := by norm_num [safeRadius]
  have htail (r : ℕ) : ∀ p ∈ tailPrimes A r, 16 ≤ p := fun p hp => h16 p (Finset.mem_filter.mp hp).1
  have hm : Measurable (fun xi : ℝ => matchedSymbol A N (3/2+Complex.I*y) xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    apply Finset.measurable_fun_sum
    intro r _hr
    apply Measurable.mul _ (measurable_quotient_moment _ (htail r) safeRadius_pos hs _).measurable
    apply (measurable_slopeMark _ (htail r) j y).mul
    simp only [coeff_leg,zetaPrimeLogKernel,zetaPrimeFeature]
    fun_prop
  have hn : Measurable (fun xi : ℝ => separatedSymbol A N (3/2+Complex.I*y) xi) :=
    (A.stronglyMeasurable_fun_sum (fun r _ => A.stronglyMeasurable_fun_sum (fun p _ =>
      measurable_rectangle_quotient _ (htail r) N p r safeRadius_pos hs))).measurable
  have hd := hm.sub hn
  have hd' := hd.comp measurable_neg
  simp_rw [matchedPair_difference]
  fun_prop

theorem integrable_matchedPair_difference (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    IntegrableOn (fun xi : ℝ =>
      (matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi)/(xi : ℂ)^2) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
      (4*matchedLogMass^2+16*matchedMass^2))).mono'
  · exact (measurable_matchedPair_difference A h16 N y L).aestronglyMeasurable
  · exact Eventually.of_forall (matchedPair_profile A h16 N y L)

theorem norm_integral_matchedPair_difference_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y L : ℝ) :
    ‖∫ xi : ℝ in Ioi 0,
      (matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi)/(xi : ℂ)^2‖ ≤
      (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (4*matchedLogMass^2+16*matchedMass^2))*(Real.pi/2) := by
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
      (4*matchedLogMass^2+16*matchedMass^2)))
    (Eventually.of_forall (matchedPair_profile A h16 N y L))
  simpa only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] using h

/-- The full signed response with its matched, finite Euler slope. -/
def matchedResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, matchedPair A N s L xi/(xi : ℂ)^2

/-- The exact full-frequency error in matching the marked slope. -/
def mismatchResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, (matchedPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2

theorem matchedResponse_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p) (y L : ℝ) :
    matchedResponse A N (3/2+Complex.I*y) L =
      separatedResponse A N (3/2+Complex.I*y) L+mismatchResponse A N (3/2+Complex.I*y) L := by
  have hs : 1 < (3/2+Complex.I*(y : ℂ)).re-safeRadius := by norm_num [safeRadius]
  have he (xi : ℝ) : matchedPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2 =
      separatedPair A N (3/2+Complex.I*y) L xi/(xi : ℂ)^2+
        (matchedPair A N (3/2+Complex.I*y) L xi-separatedPair A N (3/2+Complex.I*y) L xi)/(xi : ℂ)^2 := by ring
  unfold matchedResponse
  simp_rw [he]
  rw [integral_add (integrable_separatedPair A hA h16 N hhead safeRadius_pos hs L)
    (integrable_matchedPair_difference A h16 N y L),mul_add]
  rfl

theorem norm_mismatchResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    ‖mismatchResponse A N (3/2+Complex.I*y) L‖ ≤
      ((N : ℝ)+1)*mainBudget N (3/2-safeRadius) safeRadius*Real.exp (-(N : ℝ)/10)*
        (4*matchedLogMass^2+16*matchedMass^2)*(Real.pi/2) := by
  have hL0 : 0 < L := by linarith
  have hden : 1 ≤ 2*Real.pi*L := by nlinarith [Real.pi_gt_three]
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) hden
  unfold mismatchResponse
  rw [norm_mul]
  exact (mul_le_mul hpref (norm_integral_matchedPair_difference_le A h16 N y L)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem norm_scaled_mismatchResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (y : ℝ) {u U L : ℝ} (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*mismatchResponse A N (3/2+Complex.I*y) L‖ ≤
      ((Real.pi/2)*Real.exp (4*mass (3/2-safeRadius))*
        (4*matchedLogMass^2+16*matchedMass^2)*(U/safeRadius))*
          ((N : ℝ)+2)^3*(U/safeRadius*Real.exp (-(1 : ℝ)/10))^N := by
  have hU0 := hu.trans hU
  have hR := safeRadius_pos
  have hB := mainBudget_nonneg N (3/2-safeRadius) hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_mismatchResponse_le A h16 N y hL) (norm_nonneg _) (pow_nonneg hU0 _)).trans
  calc
    _ ≤ U^(N+1)*(((N : ℝ)+2)*mainBudget N (3/2-safeRadius) safeRadius*
        Real.exp (-(N : ℝ)/10)*(4*matchedLogMass^2+16*matchedMass^2)*(Real.pi/2)) := by
      gcongr
      linarith
    _ = _ := by
      have hexp : Real.exp (-(N : ℝ)/10) = Real.exp (-(1 : ℝ)/10)^N := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      unfold mainBudget
      rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ safeRadius]
      field_simp

/-- Uniform source-scale decay of the entire finite-range mismatch,
with arbitrary moving heights and all factorial masks retained. -/
theorem tendsto_mismatchResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p) (height length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*mismatchResponse (A N) N
      (3/2+Complex.I*height N) (length N)) atTop (nhds 0) := by
  have hr := properRate_bounds
  have hr1 : properRate < 1 := lt_trans hr.2 (by norm_num)
  have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 hr.1 hr1
  have ht1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hr.1 hr1
  have ht2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr.1 hr1
  have ht3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hr.1 hr1
  have ht : Tendsto (fun N : ℕ => ((N : ℝ)+2)^3*properRate^N) atTop (nhds 0) := by
    convert ((ht3.add (ht2.const_mul 6)).add (ht1.const_mul 12)).add (ht0.const_mul 8) using 1
    · ext N; simp only [pow_zero,pow_one]; ring
    · norm_num
  let C : ℝ := (Real.pi/2)*Real.exp (4*mass (3/2-safeRadius))*
    (4*matchedLogMass^2+16*matchedMass^2)*(ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm (a := fun N : ℕ => C*(((N : ℝ)+2)^3*properRate^N))
  · intro N
    simpa only [properRate,mul_assoc,C] using
      norm_scaled_mismatchResponse_le (A N) (h16 N) N (height N) hu hU (hL N)
  · simpa only [mul_zero] using ht.const_mul C

/-- The matched ordered response on the original physical prime set. -/
def matchedMain (u y : ℝ) (N : ℕ) : ℂ :=
  matchedResponse (roughPrimes u N) N (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N)

theorem tendsto_matched_sub_separated {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (matchedMain u (height N) N-separatedMain u (height N) N)) atTop (nhds 0) := by
  apply (tendsto_mismatchResponse (roughPrimes u) (fun _ _ hp => rough_sixteen hp) height
    (SquarefreeVaughanLogSource.length u) (ZetaRieszHeadOrders.one_le_length u) hu hU).congr
  intro N
  rw [matchedMain,separatedMain,matchedResponse_split (roughPrimes u N)
    (fun _ hp => rough_prime hp) (fun _ hp => rough_sixteen hp) N (fun _ hp => rough_head hp)]
  ring

/-- The prime-range mismatch in the complete logarithmic interface is
paid. This does not complete or bound the remaining factorial window. -/
theorem tendsto_log_sub_matched {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (logMain u (height N) N-matchedMain u (height N) N)) atTop (nhds 0) := by
  have h := ((tendsto_log_sub_completed hu hU height).add
    (tendsto_completed_sub_separated hu hU height)).sub
      (tendsto_matched_sub_separated hu.le hU height)
  simp only [zero_add,sub_zero] at h
  convert h using 1
  ext N
  ring

/-- Paid matching of the marked slope to the literal ordered Euler
cofactor, for the UNCHANGED signed dyadic target. -/
theorem tendsto_matched_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (matchedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := ((tendsto_matched_sub_separated (by linarith : 0 ≤ u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
    (tendsto_separated_sub_current hu hU y)
  simp only [zero_add] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

/-- Identifying the marked slope with the logarithmic derivative is
a neighborhood identity before taking its factorial moment. -/
theorem slopeMark_eq_logDeriv (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (k : ℕ) {s : ℂ} (hs : 1/2 < s.re) (xi : ℝ) :
    slopeMark Q (k+1) s xi =
      signedTaylorMoment k (fun z => -logDeriv (quotient Q xi) z) s/(k+1) := by
  have he : eulerSlope Q xi =ᶠ[nhds s] (fun z => -logDeriv (quotient Q xi) z) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds hs)] with z hz
    exact (neg_logDeriv_quotient Q h16 hz.le xi).symm
  rw [slopeMark,signedTaylorMoment_congr k he]

/-- The complete-minus-matched marked leg is exactly the earlier
rangeMismatch moment, with its reciprocal order still present. -/
theorem mark_difference_eq_rangeMismatch (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    logDifference (k+1) s xi-slopeMark Q (k+1) s xi =
      signedTaylorMoment k (rangeMismatch Q xi) s/(k+1) := by
  have he : rangeMismatch Q xi =ᶠ[nhds s] (fun z => completeSlope xi z-eulerSlope Q xi z) := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually
      (lt_mem_nhds (show (1/2 : ℝ) < s.re by linarith))] with z hz
    exact rangeMismatch_eq Q h16 hz.le xi
  rw [signedTaylorMoment_congr k he,signedTaylorMoment_sub k (analyticAt_completeSlope hs xi)
    (analyticAt_eulerSlope Q h16 (by linarith) xi),moment_completeSlope k hs xi,slopeMark]
  have hk : ((k+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast at hk ⊢
  field_simp

/-- The complete range discrepancy is retained inside the literal
two-slot window before integration. Its response tends to zero above. -/
theorem symbol_difference_eq_rangeMismatch (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    logSymbol A N s xi-matchedSymbol A N s xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ∑ r ∈ A, (signedTaylorMoment (j-1) (rangeMismatch (tailPrimes A r) xi) s/(j : ℂ))*
          PowerSeries.coeff h (leg s xi r)*
            signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s := by
  simp only [logSymbol,cofactor,matchedSymbol,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro r _hr
  rw [← mul_assoc,← sub_mul,← sub_mul]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (marked_order_pos hh))
  rw [mark_difference_eq_rangeMismatch (tailPrimes A r) (fun p hp => h16 p (Finset.mem_filter.mp hp).1) k hs]
  simp only [Nat.succ_sub_one,Nat.cast_succ]

end
end RiemannGaussian.ZetaRieszMatchedSlope
