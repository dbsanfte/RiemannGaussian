/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedSeparation

/-!
# Completing only the separated high-order marked prime

The ordered cofactor Euler tail stays finite. Both frequencies of the
marked prime difference are completed together; their common zero at
frequency zero is retained through the integral error estimate.
-/

namespace RiemannGaussian.ZetaRieszMarkedPrimeCompletion
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound
open ZetaRieszMainFrequency ZetaRieszMarkedSeparation ZetaRieszRoughEulerTransfer
open ZetaExposedPrimeMoments

/-- Changing the marked radius retains the actual prime logarithm. -/
theorem kernel_tilt (j p : ℕ) (s : ℂ) {R Q : ℝ} (hR : 0 < R) (hQ : 0 < Q) :
    ‖zetaPrimeLogKernel j s p‖ ≤
      Real.exp (j*Real.log (R/Q)+(Q-R)*Real.log p)*R⁻¹^j*
        zetaPrimeExpWeight (s.re-R) p := by
  apply (norm_zetaPrimeLogKernel_le j s p hQ).trans_eq
  rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log (div_pos hR hQ)]
  have hp : (R/Q)^j*R⁻¹^j = Q⁻¹^j := by
    rw [← mul_pow,show R/Q*R⁻¹ = Q⁻¹ by field_simp]
  calc
    _ = Q⁻¹^j*(Real.exp ((Q-R)*Real.log p)*zetaPrimeExpWeight (s.re-R) p) := by
      unfold zetaPrimeExpWeight
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by rw [← hp]; ring

/-- A rational logarithm enclosure with enough upper-tail margin. -/
theorem log_six_fifths_le : Real.log (6/5 : ℝ) ≤ 3/16 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/16) 3
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- Either omitted marked-prime range has an exponential order saving.
The weight is still the genuine prime weight at the common safe radius. -/
theorem omitted_kernel_bound (N j h p : ℕ)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    (hp : Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    (s : ℂ) :
    ‖zetaPrimeLogKernel j s p‖ ≤ Real.exp (-(N : ℝ)/160)*safeRadius⁻¹^j*
      zetaPrimeExpWeight (s.re-safeRadius) p := by
  have hb := (Finset.mem_filter.mp hh).2
  have hjlo : 21*(N : ℝ) ≤ 40*j := by exact_mod_cast hb.2.1
  have hjhi : 40*(j : ℝ) ≤ 23*N := by exact_mod_cast hb.2.2.1
  have hR := safeRadius_pos
  rcases hp with hp | hp
  · have he : j*Real.log (safeRadius/(2*safeRadius))+
        (2*safeRadius-safeRadius)*Real.log p ≤ -(N : ℝ)/160 := by
      rw [show safeRadius/(2*safeRadius) = (2 : ℝ)⁻¹ by field_simp,Real.log_inv]
      have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      have hj := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) j)
      have hn := mul_le_mul_of_nonneg_left hp hR.le
      norm_num [safeRadius] at hn ⊢
      norm_num at hj
      nlinarith
    exact (kernel_tilt j p s hR (show 0 < 2*safeRadius by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (inv_nonneg.mpr hR.le) _)) (Real.exp_pos _).le)
  · have he : j*Real.log (safeRadius/((5/6)*safeRadius))+
        ((5/6)*safeRadius-safeRadius)*Real.log p ≤ -(N : ℝ)/160 := by
      rw [show safeRadius/((5/6)*safeRadius) = (6/5 : ℝ) by field_simp]
      have hj := mul_le_mul_of_nonneg_left log_six_fifths_le (Nat.cast_nonneg (α := ℝ) j)
      have hn := mul_le_mul_of_nonneg_left hp (show 0 ≤ safeRadius/6 by positivity)
      norm_num [safeRadius] at hn ⊢
      nlinarith
    exact (kernel_tilt j p s hR (show 0 < (5/6)*safeRadius by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
        (pow_nonneg (inv_nonneg.mpr hR.le) _)) (Real.exp_pos _).le)

/-- Eventually the polynomial and fixed prime heads are inside the
already paid exponential head. -/
theorem eventually_rough_support {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → p ∉ roughPrimes u N →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p := by
  have hl : Tendsto (fun N : ℕ => Real.log N/((N : ℝ)+1)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_zero,pow_one,one_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 1 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : u < Real.exp (-( (11/8 : ℝ)/2)) := by
    rw [show ((11/8 : ℝ)/2) = 11/16 by norm_num]
    exact hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  filter_upwards [hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/1000)),
    eventually_ge_atTop 2000,
    ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu
      (by norm_num : (0 : ℝ) ≤ (11/8)/2) he] with N hlog hN hL
  intro p hprime hnot
  by_cases hp : Real.log p ≤ (N : ℝ)/110
  · exact Or.inl hp
  right
  have hNr : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlN := (div_lt_iff₀ (by positivity : (0 : ℝ) < N+1)).mp hlog
  have h16 : 16 ≤ p := by
    by_contra hc
    have hlp := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hprime.pos)
    have hpc : (p : ℝ) < 16 := by exact_mod_cast (not_le.mp hc)
    linarith
  have hNp : N^2 < p := by
    by_contra hc
    have hpc : (p : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast (not_lt.mp hc)
    have hlogp := Real.log_le_log (Nat.cast_pos.mpr hprime.pos) hpc
    rw [Real.log_pow] at hlogp
    norm_num only [Nat.cast_ofNat] at hlogp
    linarith
  have hX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 ≤ p := by
    by_contra hc
    apply hnot
    exact Finset.mem_filter.mpr ⟨(ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mpr
      ⟨hprime,hNp,not_le.mp hc⟩,h16,not_le.mp hp⟩
  exact le_trans (by nlinarith [hL])
    (ZetaRieszPrimeCompletion.physicalPrimeTail_log_support u N p hX)

/-- The complete marked prime difference retains both complex arguments. -/
def completeDifference (j : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ordinaryPrimeMoment j s-ordinaryPrimeMoment j (s+Complex.I*xi)

/-- The exact missing-prime difference, before any estimate. -/
def missingDifference (A : Finset ℕ) (j : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑' p : ℕ, if p.Prime ∧ p ∉ A then PowerSeries.coeff j (leg s xi p) else 0

theorem summable_prime_leg {s : ℂ} (hs : 1 < s.re) (j : ℕ) (xi : ℝ) :
    Summable (fun p : ℕ => if p.Prime then PowerSeries.coeff j (leg s xi p) else 0) := by
  have ht : 1 < (s+Complex.I*xi).re := by simpa using hs
  apply ((summable_ordinaryPrimeMoment hs j).sub (summable_ordinaryPrimeMoment ht j)).congr
  intro p
  by_cases hp : p.Prime <;> simp only [hp,if_true,if_false,sub_zero,coeff_leg_difference]

/-- Completing this difference has only the literal omitted primes as
its error. No cofactor or phase has been completed. -/
theorem difference_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {s : ℂ} (hs : 1 < s.re) (j : ℕ) (xi : ℝ) :
    completeDifference j s xi = primeDifference A j s xi+missingDifference A j s xi := by
  have ht : 1 < (s+Complex.I*xi).re := by simpa using hs
  have hc : completeDifference j s xi =
      ∑' p : ℕ, if p.Prime then PowerSeries.coeff j (leg s xi p) else 0 := by
    rw [completeDifference,ordinaryPrimeMoment,ordinaryPrimeMoment,
      ← (summable_ordinaryPrimeMoment hs j).tsum_sub (summable_ordinaryPrimeMoment ht j)]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime <;> simp only [hp,if_true,if_false,sub_zero,coeff_leg_difference]
  rw [hc,← (summable_prime_leg hs j xi).sum_add_tsum_compl (s := A)]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [if_pos (hA p hp),coeff_leg_difference]
  · unfold missingDifference
    rw [tsum_subtype (f := fun p : ℕ => if p.Prime then PowerSeries.coeff j (leg s xi p) else 0)]
    apply tsum_congr
    intro p
    by_cases hp : p ∈ A <;> by_cases hprime : p.Prime <;> simp [Set.indicator, hp, hprime]

/-- A summable envelope for the exact missing difference. The function
f still bounds its Fourier zero and need not be frequency independent. -/
theorem missing_bound (A : Finset ℕ) (N j h : ℕ)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    (s : ℂ) (xi : ℝ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hw : Summable (fun p => zetaPrimeExpWeight (s.re-safeRadius) p*f p)) :
    ‖missingDifference A j s xi‖ ≤
      (Real.exp (-(N : ℝ)/160)*safeRadius⁻¹^j)*
        ∑' p, zetaPrimeExpWeight (s.re-safeRadius) p*f p := by
  let C := Real.exp (-(N : ℝ)/160)*safeRadius⁻¹^j
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (inv_nonneg.mpr safeRadius_pos.le) _)
  have ha (p : ℕ) :
      ‖if p.Prime ∧ p ∉ A then PowerSeries.coeff j (leg s xi p) else 0‖ ≤
        C*(zetaPrimeExpWeight (s.re-safeRadius) p*f p) := by
    by_cases hp : p.Prime ∧ p ∉ A
    · rw [if_pos hp,coeff_leg,norm_mul]
      have hb := mul_le_mul (hphase p) (omitted_kernel_bound N j h p hh (hgap p hp.1 hp.2) s)
        (norm_nonneg _) (hf p)
      exact hb.trans_eq (by dsimp [C]; ring)
    · rw [if_neg hp,norm_zero]
      exact mul_nonneg hC (mul_nonneg (Real.exp_pos _).le (hf p))
  have hs := (hw.mul_left C).of_norm_bounded ha
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum ha (hw.mul_left C)).trans_eq (tsum_mul_left))

/-- Complete logarithmic mass for controlling the Fourier origin. -/
theorem summable_log_weight {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun p : ℕ => Real.log p*zetaPrimeExpWeight sigma p) := by
  apply ((summable_zetaPrimeExpWeight (show 1 < (sigma+1)/2 by linarith)).mul_left
    ((sigma-1)/2)⁻¹).of_nonneg_of_le
  · intro p
    exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  · intro p
    have h := norm_zetaPrimeLogKernel_le 1 (sigma : ℂ) p
      (show 0 < (sigma-1)/2 by linarith)
    simpa only [norm_zetaPrimeLogKernel,pow_one,Nat.factorial_one,Nat.cast_one,div_one,
      Complex.ofReal_re,show sigma-(sigma-1)/2 = (sigma+1)/2 by ring] using h

theorem tsum_log_weight_le {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' p : ℕ, Real.log p*zetaPrimeExpWeight sigma p) ≤ logMass sigma := by
  apply Real.tsum_le_of_sum_le
  · intro p
    exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  · intro A
    exact sum_logMass_le A hsigma

/-- The cofactor retains the exact least-prime ordering and total order. -/
def cofactor (A : Finset ℕ) (N j h : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ r ∈ A, PowerSeries.coeff h (leg s xi r)*
    signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s

/-- Only the high marked prime is completed. -/
def completedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    completeDifference j s xi*cofactor A N j h s xi

/-- The error is kept as a coupled signed product until estimated. -/
def completionError (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
    missingDifference A j s xi*cofactor A N j h s xi

theorem completedSymbol_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) (xi : ℝ) :
    completedSymbol A N s xi = separatedSymbol A N s xi+completionError A N s xi := by
  simp only [completedSymbol,difference_split A hA hs,add_mul,Finset.sum_add_distrib,
    completionError,separatedSymbol_factor,cofactor]

theorem cofactor_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h : ℕ) (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p) :
    ‖cofactor A N j h s xi‖ ≤
      (Real.exp (4*mass (s.re-safeRadius))*safeRadius⁻¹^(N+1-j))*
        ∑ r ∈ A, zetaPrimeExpWeight (s.re-safeRadius) r*f r := by
  have hR := safeRadius_pos
  have he : h+(N+1-j-h) = N+1-j := by
    have hh' := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  unfold cofactor
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _hr
  have hfr := hf r
  have hl := (norm_leg_le r h s xi safeRadius_pos).trans
    (mul_le_mul_of_nonneg_right (hphase r) (by unfold zetaPrimeExpWeight; positivity))
  have hm := quotient_moment_bound (tailPrimes A r)
    (fun p hp => h16 p (Finset.mem_filter.mp hp).1) safeRadius_pos hs xi (N+1-j-h)
  rw [norm_mul]
  apply (mul_le_mul hl hm (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)).trans_eq
  simp only [div_eq_mul_inv,← inv_pow]
  calc
    _ = Real.exp (4*mass (s.re-safeRadius))*
      (safeRadius⁻¹^h*safeRadius⁻¹^(N+1-j-h))*
        (zetaPrimeExpWeight (s.re-safeRadius) r*f r) := by ring
    _ = _ := by rw [← pow_add,he]

/-- Both marked Fourier zeros survive completion through the full
factorial rectangle. Only its two omitted-prime tails are bounded. -/
theorem completionError_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (xi : ℝ)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hphase : ∀ p, ‖1-zetaPrimeFeature (Complex.I*xi) p‖ ≤ f p)
    (hw : Summable (fun p => zetaPrimeExpWeight (s.re-safeRadius) p*f p))
    {V : ℝ} (hV : (∑' p, zetaPrimeExpWeight (s.re-safeRadius) p*f p) ≤ V) :
    ‖completionError A N s xi‖ ≤
      mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*V^2 := by
  have hR := safeRadius_pos
  have hv0 : 0 ≤ V := (tsum_nonneg (fun p => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  have hsum : (∑ r ∈ A, zetaPrimeExpWeight (s.re-safeRadius) r*f r) ≤ V :=
    (hw.sum_le_tsum A (fun p _ => mul_nonneg (Real.exp_pos _).le (hf p))).trans hV
  let B := Real.exp (4*mass (s.re-safeRadius))/safeRadius^(N+1)*
    Real.exp (-(N : ℝ)/160)*V^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha (j : ℕ) (hj : j ∈ Finset.range (N+2)) (h : ℕ)
      (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
      ‖missingDifference A j s xi*cofactor A N j h s xi‖ ≤ B := by
    have he : j+(N+1-j) = N+1 := by have := Finset.mem_range.mp hj; omega
    have hm := (missing_bound A N j h hh hgap s xi f hf hphase hw).trans
      (mul_le_mul_of_nonneg_left hV (by positivity))
    have hc := (cofactor_bound A h16 N j h hh hs xi f hf hphase).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
    rw [norm_mul]
    apply (mul_le_mul hm hc (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B]
    simp only [div_eq_mul_inv,← inv_pow]
    calc
      _ = Real.exp (4*mass (s.re-safeRadius))*
        (safeRadius⁻¹^j*safeRadius⁻¹^(N+1-j))*Real.exp (-(N : ℝ)/160)*V^2 := by ring
      _ = _ := by rw [← pow_add,he]; simp only [div_eq_mul_inv]
  have hc (j : ℕ) : ((ZetaRieszSkewAllocation.rectangleOrders N j).card : ℝ) ≤ (N : ℝ)+2 := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun h => j+h ∈ ZetaRieszWideOwnerAudit.ownerOrders N ∧
        21*N ≤ 40*j ∧ 40*j ≤ 23*N ∧ N ≤ 100*(h+1) ∧ 100*(h+1) ≤ 4*N)
      (Finset.range (N+1-j+1)))
    rw [Finset.card_range] at h
    exact_mod_cast (show (ZetaRieszSkewAllocation.rectangleOrders N j).card ≤ N+2 by
      dsimp [ZetaRieszSkewAllocation.rectangleOrders] at h ⊢; omega)
  unfold completionError
  calc
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        ‖missingDifference A j s xi*cofactor A N j h s xi‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ j ∈ Finset.range (N+2), ∑ _h ∈ ZetaRieszSkewAllocation.rectangleOrders N j, B :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh => ha j hj h hh))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*B := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hc j) hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];
                push_cast; dsimp [B,mainBudget]; ring

theorem completionError_large (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (xi : ℝ) :
    ‖completionError A N s xi‖ ≤
      4*mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*mass (s.re-safeRadius)^2 := by
  have h := completionError_bound A h16 N hgap hs xi (fun _ => 2) (fun _ => by norm_num)
    (fun p => phase_le_two p xi) ((summable_zetaPrimeExpWeight hs).mul_right 2)
    (V := mass (s.re-safeRadius)*2) (by rw [tsum_mul_right]; rfl)
  convert h using 1
  ring

theorem completionError_small (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (xi : ℝ) :
    ‖completionError A N s xi‖ ≤
      mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*logMass (s.re-safeRadius)^2*xi^2 := by
  have hw : Summable (fun p : ℕ => zetaPrimeExpWeight (s.re-safeRadius) p*(|xi| *Real.log p)) := by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using (summable_log_weight hs).mul_left |xi|
  have ht : (∑' p : ℕ, zetaPrimeExpWeight (s.re-safeRadius) p*(|xi| *Real.log p)) ≤
      |xi| *logMass (s.re-safeRadius) := by
    simp_rw [show ∀ p : ℕ, zetaPrimeExpWeight (s.re-safeRadius) p*(|xi| *Real.log p) =
      |xi| *(Real.log p*zetaPrimeExpWeight (s.re-safeRadius) p) from fun p => by ring]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_log_weight_le hs) (abs_nonneg xi)
  have h := completionError_bound A h16 N hgap hs xi (fun p => |xi| *Real.log p)
    (fun p => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg p))
    (fun p => phase_le_log p xi) hw ht
  simpa only [mul_pow,sq_abs,mul_assoc,mul_comm,mul_left_comm] using h

/-- The completion error has both original Fourier signs. -/
def completionPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*completionError A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*completionError A N s (-xi)

/-- A quadratic zero and a bounded numerator jointly give an
integrable profile on the ENTIRE frequency axis. -/
theorem norm_div_square_profile {f : ℂ} {xi a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsmall : ‖f‖ ≤ a*xi^2) (hlarge : ‖f‖ ≤ b) :
    ‖f/(xi : ℂ)^2‖ ≤ (a+b)*(1+xi^2)⁻¹ := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  by_cases hx : xi = 0
  · simp only [hx,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,div_zero]
    exact mul_nonneg (add_nonneg ha hb) (by positivity)
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1+xi^2)).mpr
  calc
    ‖f‖/xi^2*(1+xi^2) = ‖f‖/xi^2+‖f‖ := by field_simp
    _ ≤ a+b := add_le_add ((div_le_iff₀ (sq_pos_of_ne_zero hx)).mpr hsmall) hlarge

/-- The error's frequency integrability retains both marked zeros. -/
theorem completionPair_profile (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (L xi : ℝ) :
    ‖completionPair A N s L xi/(xi : ℂ)^2‖ ≤
      (mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*
        (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2))*(1+xi^2)⁻¹ := by
  have hB := mainBudget_nonneg N (s.re-safeRadius) safeRadius_pos
  have hl : ‖completionPair A N s L xi‖ ≤
      8*mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*mass (s.re-safeRadius)^2 := by
    unfold completionPair
    apply (norm_add_le _ _).trans
    simpa only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul] using
      (add_le_add (completionError_large A h16 N hgap hs xi)
        (completionError_large A h16 N hgap hs (-xi))).trans_eq (by ring)
  have hn : ‖completionPair A N s L xi‖ ≤
      (2*mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*logMass (s.re-safeRadius)^2)*xi^2 := by
    unfold completionPair
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    have h := add_le_add (completionError_small A h16 N hgap hs xi)
      (completionError_small A h16 N hgap hs (-xi))
    simpa only [neg_sq,two_mul,add_mul,mul_assoc] using h
  exact (norm_div_square_profile (by positivity) (by positivity) hn hl).trans_eq (by ring)

theorem measurable_missingDifference (A : Finset ℕ) (j : ℕ) (s : ℂ) :
    Measurable (fun xi : ℝ => missingDifference A j s xi) := by
  apply Measurable.tsum
  intro p
  by_cases hp : p.Prime ∧ p ∉ A
  · simp only [if_pos hp,coeff_leg,zetaPrimeLogKernel,zetaPrimeFeature]
    fun_prop
  · simp only [if_neg hp]
    exact measurable_const

theorem measurable_cofactor (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N j h : ℕ) {s : ℂ} (hs : 1 < s.re-safeRadius) :
    Measurable (fun xi : ℝ => cofactor A N j h s xi) := by
  apply Finset.measurable_fun_sum
  intro r _hr
  have hm := (measurable_quotient_moment (tailPrimes A r)
    (fun p hp => h16 p (Finset.mem_filter.mp hp).1) safeRadius_pos hs (N+1-j-h)).measurable
  apply Measurable.mul _ hm
  simp only [coeff_leg,zetaPrimeLogKernel,zetaPrimeFeature]
  fun_prop

theorem measurable_completionPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re-safeRadius) (L : ℝ) :
    Measurable (fun xi : ℝ => completionPair A N s L xi/(xi : ℂ)^2) := by
  have hm : Measurable (fun xi : ℝ => completionError A N s xi) := by
    apply Finset.measurable_fun_sum
    intro j _hj
    apply Finset.measurable_fun_sum
    intro h _hh
    exact (measurable_missingDifference A j s).mul (measurable_cofactor A h16 N j h hs)
  have hn := hm.comp measurable_neg
  unfold completionPair
  fun_prop

theorem integrable_completionPair (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => completionPair A N s L xi/(xi : ℂ)^2) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*
      (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2))).mono'
  · exact (measurable_completionPair A h16 N hs L).aestronglyMeasurable
  · exact Eventually.of_forall (completionPair_profile A h16 N hgap hs L)

/-- A full integrated completion estimate, with no frequency cutoff,
prime-phase hypothesis or independently completed cofactor. -/
theorem norm_integral_completionPair_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (L : ℝ) :
    ‖∫ xi : ℝ in Ioi 0, completionPair A N s L xi/(xi : ℂ)^2‖ ≤
      (mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*
        (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2))*(Real.pi/2) := by
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((integrable_inv_one_add_sq.integrableOn).const_mul
    (mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*
      (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2)))
    (Eventually.of_forall (completionPair_profile A h16 N hgap hs L))
  simpa only [integral_const_mul,integral_Ioi_inv_one_add_sq,Real.arctan_zero,sub_zero] using h

/-- Both signs of the response after the paid high-prime completion. -/
def completedPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*completedSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*completedSymbol A N s (-xi)

theorem completedPair_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) (L xi : ℝ) :
    completedPair A N s L xi = separatedPair A N s L xi+completionPair A N s L xi := by
  simp only [completedPair,completedSymbol_split A hA N hs,separatedPair,completionPair]
  ring

/-- The original Fourier integral with only its high prime completed. -/
def completedResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, completedPair A N s L xi/(xi : ℂ)^2

/-- The literal integrated missing-prime error. -/
def errorResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, completionPair A N s L xi/(xi : ℂ)^2

/-- All integral exchanges in the exact completion ledger are justified. -/
theorem completedResponse_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) (L : ℝ) :
    completedResponse A N s L = separatedResponse A N s L+errorResponse A N s L := by
  have hs' : 1 < s.re := by linarith [safeRadius_pos]
  unfold completedResponse separatedResponse errorResponse
  simp_rw [completedPair_split A hA N hs',add_div]
  rw [integral_add (integrable_separatedPair A hA h16 N hhead safeRadius_pos hs L)
    (integrable_completionPair A h16 N hgap hs L),mul_add]

theorem norm_errorResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) {L : ℝ} (hL : 1 ≤ L) :
    ‖errorResponse A N s L‖ ≤
      ((N : ℝ)+1)*mainBudget N (s.re-safeRadius) safeRadius*Real.exp (-(N : ℝ)/160)*
        (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2)*(Real.pi/2) := by
  have hL0 : 0 < L := by linarith
  have hden : 1 ≤ 2*Real.pi*L := by nlinarith [Real.pi_gt_three]
  have hpref : ‖((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))‖ ≤ (N : ℝ)+1 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_natCast]
    norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,abs_of_pos hL0,Nat.cast_add,Nat.cast_one]
    exact div_le_self (by positivity) hden
  unfold errorResponse
  rw [norm_mul]
  exact (mul_le_mul hpref (norm_integral_completionPair_le A h16 N hgap hs L)
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- This integrated error is bounded at the already checked geometric
rate. The stronger raw saving exp(-N/160) is only relaxed here. -/
theorem norm_scaled_errorResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hgap : ∀ p : ℕ, p.Prime → p ∉ A →
      Real.log p ≤ (N : ℝ)/110 ∨ (11/8 : ℝ)*N ≤ Real.log p)
    {s : ℂ} (hs : 1 < s.re-safeRadius) {u U L : ℝ}
    (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*errorResponse A N s L‖ ≤
      ((Real.pi/2)*Real.exp (4*mass (s.re-safeRadius))*
        (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2)*(U/safeRadius))*
          ((N : ℝ)+2)^3*(U/safeRadius*Real.exp (-(1 : ℝ)/220))^N := by
  have hU0 := hu.trans hU
  have hR := safeRadius_pos
  have hB := mainBudget_nonneg N (s.re-safeRadius) hR
  have he : Real.exp (-(N : ℝ)/160) ≤ Real.exp (-(N : ℝ)/220) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_errorResponse_le A h16 N hgap hs hL) (norm_nonneg _) (pow_nonneg hU0 _)).trans
  calc
    _ ≤ U^(N+1)*(((N : ℝ)+2)*mainBudget N (s.re-safeRadius) safeRadius*
        Real.exp (-(N : ℝ)/220)*
          (2*logMass (s.re-safeRadius)^2+8*mass (s.re-safeRadius)^2)*(Real.pi/2)) := by
      gcongr
      linarith
    _ = _ := by
      have hexp : Real.exp (-(N : ℝ)/220) = Real.exp (-(1 : ℝ)/220)^N := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      unfold mainBudget
      rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ safeRadius]
      field_simp

/-- The entire integrated completion error tends to zero for the
literal cutoffs, uniformly in an arbitrary moving evaluation height. -/
theorem tendsto_errorResponse {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*errorResponse (roughPrimes u N) N
      (3/2+Complex.I*height N) (SquarefreeVaughanLogSource.length u N)) atTop (nhds 0) := by
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
  let C : ℝ := (Real.pi/2)*Real.exp (4*mass (1+1/262144))*
    (2*logMass (1+1/262144)^2+8*mass (1+1/262144)^2)*
      (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm' (a := fun N : ℕ => C*(((N : ℝ)+2)^3*sourceRate^N))
  · filter_upwards [eventually_rough_support hu hU] with N hgap
    have h := norm_scaled_errorResponse_le (roughPrimes u N) (fun _ hp => rough_sixteen hp)
      N hgap (show 1 < (3/2+Complex.I*(height N : ℂ)).re-safeRadius by rw [hs]; norm_num)
      hu.le hU (ZetaRieszHeadOrders.one_le_length u N)
    simpa only [hs,sourceRate,mul_assoc,C] using h
  · simpa only [mul_zero] using ht.const_mul C

/-- The remaining signed main term after completing only its independent
high marked prime. The least prime and its Euler tail remain literal. -/
def completedMain (u y : ℝ) (N : ℕ) : ℂ :=
  completedResponse (roughPrimes u N) N (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N)

theorem tendsto_completed_sub_separated {u : ℝ} (hu : 0 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (completedMain u (height N) N-separatedMain u (height N) N)) atTop (nhds 0) := by
  apply (tendsto_errorResponse hu hU height).congr'
  filter_upwards [eventually_rough_support hu hU] with N hgap
  rw [completedMain,separatedMain,completedResponse_split (roughPrimes u N)
    (fun _ hp => rough_prime hp) (fun _ hp => rough_sixteen hp) N
    (fun _ hp => rough_head hp) hgap
    (show 1 < (3/2+Complex.I*(height N : ℂ)).re-safeRadius by norm_num [safeRadius])]
  ring

/-- Paid high-prime completion of the UNCHANGED signed packet. This
is an error-decay theorem, not a bound for its coupled main response. -/
theorem tendsto_completed_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (completedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := ((tendsto_completed_sub_separated (by linarith : 0 < u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder).add
    (tendsto_separated_sub_current hu hU y)
  simp only [zero_add] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszMarkedPrimeCompletion
