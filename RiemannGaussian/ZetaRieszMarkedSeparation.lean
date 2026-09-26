/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMainFrequency

/-!
# Paying the ordering obstruction at the high-order marked prime

The exact rectangle places a high factorial order on the marked prime and
a low order on the least prime. An unequal-radius estimate pays incidences
with those prime sizes reversed. No prime phase is approximated.
-/

namespace RiemannGaussian.ZetaRieszMarkedSeparation
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError ZetaRieszOrderedEulerBound
open ZetaRieszMainFrequency

/-- The actual two-order box has a uniform tilt saving. -/
theorem rectangle_tilt {N j h : ℕ} (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) :
    (2/3 : ℝ)^j*2^h ≤ Real.exp (-(N : ℝ)/10) := by
  have hb := (Finset.mem_filter.mp hh).2
  have hj : 21*(N : ℝ) ≤ 40*j := by exact_mod_cast hb.2.1
  have hh' : 100*((h : ℝ)+1) ≤ 4*N := by exact_mod_cast hb.2.2.2.2
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3/2)
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num only [inv_div,one_div] at hlog
  have he : Real.log (2/3 : ℝ) = -Real.log (3/2 : ℝ) := by
    rw [show (2/3 : ℝ) = (3/2 : ℝ)⁻¹ by norm_num,Real.log_inv]
  have hp (a : ℝ) (ha : 0 < a) (k : ℕ) : a^k = Real.exp (k*Real.log a) := by
    rw [Real.exp_nat_mul,Real.exp_log ha]
  rw [hp (2/3) (by norm_num),hp 2 (by norm_num),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg j : (0 : ℝ) ≤ j),
    mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]

/-- The two unequal marked radii cancel their weight cost in the
forbidden ordering p<=r. -/
theorem tilted_weight_le {p r : ℕ} (hp : 0 < p) (hpr : p ≤ r)
    (sigma : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    zetaPrimeExpWeight (sigma-R/2) p*zetaPrimeExpWeight (sigma+R/2) r ≤
      zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r := by
  have hlog : Real.log p ≤ Real.log r :=
    Real.log_le_log (Nat.cast_pos.mpr hp) (by exact_mod_cast hpr)
  unfold zetaPrimeExpWeight
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hR]

/-- A shared bound for each atom gives only a quadratic count cost. -/
theorem rectangle_bound_of_atoms (F : ℂ → ℂ) (N p r : ℕ) (s : ℂ) (xi : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ j ∈ Finset.range (N+2), ∀ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
      ‖PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
        signedTaylorMoment (N+1-j-h) F s‖ ≤ B) :
    ‖rectangleMoment N p r s xi F‖ ≤ ((N : ℝ)+2)^2*B := by
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
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh => hb j hj h hh))
    _ ≤ ∑ _j ∈ Finset.range (N+2), ((N : ℝ)+2)*B := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Finset.sum_const,nsmul_eq_mul] using mul_le_mul_of_nonneg_right (hc j) hB
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; push_cast; ring

/-- The low-order slot cannot hide a larger prime than the high-order
slot without an exponential factorial cost. All middle orders remain. -/
theorem wrong_order_atom (F : ℂ → ℂ) (N p r j h : ℕ) (s : ℂ) (xi : ℝ)
    (hp : 0 < p) (hpr : p ≤ r) (hj : j ∈ Finset.range (N+2))
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j)
    {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hF : ∀ k, ‖signedTaylorMoment k F s‖ ≤ M/R^k) :
    ‖PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
      signedTaylorMoment (N+1-j-h) F s‖ ≤
      (M*Real.exp (-(N : ℝ)/10)/R^(N+1))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  have he : j+h+(N+1-j-h) = N+1 := by
    have hj' := Finset.mem_range.mp hj
    have hh' := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  have htilt := rectangle_tilt hh
  have hw := tilted_weight_le hp hpr (s.re-R) hR.le
  have hpR : ((3/2 : ℝ)*R)⁻¹^j = (2/3 : ℝ)^j*R⁻¹^j := by
    rw [mul_inv_rev,mul_pow]
    norm_num
    ring
  have hrR : ((1/2 : ℝ)*R)⁻¹^h = (2 : ℝ)^h*R⁻¹^h := by
    rw [mul_inv_rev,mul_pow]
    norm_num
    ring
  have hpow : R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h) = R⁻¹^(N+1) := by
    rw [← pow_add,← pow_add,he]
  rw [norm_mul,norm_mul]
  apply (mul_le_mul
    (mul_le_mul (norm_leg_le p j s xi (by positivity : 0 < (3/2 : ℝ)*R))
      (norm_leg_le r h s xi (by positivity : 0 < (1/2 : ℝ)*R))
      (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity))
    (hF (N+1-j-h)) (norm_nonneg _) (by unfold zetaPrimeExpWeight; positivity)).trans
  rw [hpR,hrR]
  have heq : s.re-(3/2 : ℝ)*R = (s.re-R)-R/2 := by ring
  have heq' : s.re-(1/2 : ℝ)*R = (s.re-R)+R/2 := by ring
  rw [heq,heq']
  calc
    _ = (M/R^(N+1))*((2/3 : ℝ)^j*2^h)*
        (zetaPrimeExpWeight ((s.re-R)-R/2) p*zetaPrimeExpWeight ((s.re-R)+R/2) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
      simp only [div_eq_mul_inv,← inv_pow]
      calc
        _ = M*(R⁻¹^j*R⁻¹^h*R⁻¹^(N+1-j-h))*((2/3 : ℝ)^j*2^h)*
          (zetaPrimeExpWeight ((s.re-R)-R/2) p*zetaPrimeExpWeight ((s.re-R)+R/2) r)*
            (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by ring
        _ = _ := by rw [hpow]; simp only [div_eq_mul_inv]
    _ ≤ _ := by
      have hm : (M/R^(N+1))*((2/3 : ℝ)^j*2^h)*
          (zetaPrimeExpWeight ((s.re-R)-R/2) p*zetaPrimeExpWeight ((s.re-R)+R/2) r) ≤
        (M/R^(N+1))*Real.exp (-(N : ℝ)/10)*
          (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r) :=
        mul_le_mul (mul_le_mul_of_nonneg_left htilt (div_nonneg hM (pow_nonneg hR.le _))) hw
          (by unfold zetaPrimeExpWeight; positivity) (by positivity)
      apply (mul_le_mul_of_nonneg_right hm
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
      ring

theorem wrong_order_rectangle (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    (N p r : ℕ) (hp : 0 < p) (hpr : p ≤ r)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖rectangleMoment N p r s xi (quotient Q xi)‖ ≤
      (mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/10))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  have h := rectangle_bound_of_atoms (quotient Q xi) N p r s xi
    (B := (Real.exp (4*mass (s.re-R))*Real.exp (-(N : ℝ)/10)/R^(N+1))*
      (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
        (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖))
    (by unfold zetaPrimeExpWeight; positivity)
    (fun j hj h hh => wrong_order_atom (quotient Q xi) N p r j h s xi hp hpr hj hh hR
      (Real.exp_pos _).le (quotient_moment_bound Q h16 hR hs xi))
  convert h using 1
  unfold mainBudget
  ring

/-- The cofactor Euler tail is ordered only by the least prime. -/
def tailPrimes (A : Finset ℕ) (r : ℕ) : Finset ℕ := A.filter (fun q => r < q)

theorem middle_eq_erase (A : Finset ℕ) (p r : ℕ) :
    middlePrimes A p r = (tailPrimes A r).erase p := by
  ext q
  simp only [middlePrimes,tailPrimes,Finset.mem_filter,Finset.mem_erase]
  tauto

/-- Reinstating the marked prime in the cofactor product creates an
extra occurrence of that actual prime, not a free completion. -/
def collision (Q : Finset ℕ) (p : ℕ) (xi : ℝ) (s : ℂ) : ℂ :=
  quotient (Q.erase p) xi s-quotient Q xi s

theorem quotient_insert_factor (Q : Finset ℕ) {p : ℕ} (hp : p ∈ Q) (xi : ℝ) (s : ℂ) :
    quotient Q xi s = ((1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/
      (1-zetaPrimeFeature s p))*quotient (Q.erase p) xi s := by
  exact (Finset.mul_prod_erase Q _ hp).symm

theorem norm_local_sub_one {q z : ℂ} (hq : ‖q‖ ≤ 1/4) (hz : ‖z‖ ≤ 1) :
    ‖(1-q*z)/(1-q)-1‖ ≤ 4*‖q‖ := by
  have hd : 3/4 ≤ ‖1-q‖ := by
    simpa only [mul_one] using ZetaRieszEulerQuotient.local_denominator_bound hq
      (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)
  have hd0 : 1-q ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : (1-q*z)/(1-q)-1 = q*(1-z)/(1-q) := by field_simp; ring
  have hz2 : ‖1-z‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num; linarith)
  rw [he,norm_div,norm_mul]
  apply (div_le_iff₀ (by linarith : 0 < ‖1-q‖)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hz2 (norm_nonneg q),norm_nonneg q]

theorem norm_collision_le (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    {p : ℕ} (hp : p ∈ Q) (N : ℕ) (hhead : (N : ℝ)/110 ≤ Real.log p)
    {sigma : ℝ} (hsigma : 1 < sigma) {s : ℂ} (hs : sigma ≤ s.re) (xi : ℝ) :
    ‖collision Q p xi s‖ ≤ 4*Real.exp (4*mass sigma)*Real.exp (-(N : ℝ)/220) := by
  have hq := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
    (by linarith : 1/2 ≤ s.re) (h16 p hp)
  have hfeat : ‖zetaPrimeFeature s p‖ ≤ Real.exp (-(N : ℝ)/220) := by
    rw [norm_zetaPrimeFeature,zetaPrimeExpWeight]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_natCast_nonneg p]
  unfold collision
  rw [quotient_insert_factor Q hp xi s,
    show quotient (Q.erase p) xi s-((1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/
      (1-zetaPrimeFeature s p))*quotient (Q.erase p) xi s =
      (1-(1-zetaPrimeFeature s p*zetaPrimeFeature (Complex.I*xi) p)/(1-zetaPrimeFeature s p))*
        quotient (Q.erase p) xi s by ring,norm_mul,norm_sub_rev]
  have h := (norm_local_sub_one hq (norm_character_phase xi p).le).trans
    (mul_le_mul_of_nonneg_left hfeat (by norm_num : (0 : ℝ) ≤ 4))
  apply (mul_le_mul h (norm_quotient_le (Q.erase p)
    (fun q hq => h16 q (Finset.mem_of_mem_erase hq)) hsigma hs xi)
    (norm_nonneg _) (by positivity)).trans_eq
  unfold mass
  ring

theorem analyticAt_collision (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    (p : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) : AnalyticAt ℂ (collision Q p xi) s :=
  (analyticAt_quotient (Q.erase p) (fun q hq => h16 q (Finset.mem_of_mem_erase hq)) hs xi).sub
    (analyticAt_quotient Q h16 hs xi)

theorem collision_moment_bound (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    {p : ℕ} (hp : p ∈ Q) (N : ℕ) (hhead : (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) (k : ℕ) :
    ‖signedTaylorMoment k (collision Q p xi) s‖ ≤
      (4*Real.exp (4*mass (s.re-R))*Real.exp (-(N : ℝ)/220))/R^k := by
  apply norm_signedTaylorMoment_le hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hR.ne']
    intro z hz
    exact (analyticAt_collision Q h16 p
      (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt
  · intro z hz
    exact norm_collision_le Q h16 hp N hhead hs
      (ZetaRieszEulerMoments.disc_re_lower_bound (Metric.sphere_subset_closedBall hz)) xi

theorem collision_rectangle_bound (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    {p : ℕ} (hp : p ∈ Q) (N r : ℕ) (hhead : (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖rectangleMoment N p r s xi (collision Q p xi)‖ ≤
      (4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  have h := rectangle_bound (collision Q p xi) N p r s xi hR (by positivity)
    (collision_moment_bound Q h16 hp N hhead hR hs xi)
  convert h using 1
  unfold mainBudget
  ring

theorem rectangle_erase_ledger (Q : Finset ℕ) (h16 : ∀ q ∈ Q, 16 ≤ q)
    (N p r : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (xi : ℝ) :
    rectangleMoment N p r s xi (quotient (Q.erase p) xi) =
      rectangleMoment N p r s xi (quotient Q xi)+
        rectangleMoment N p r s xi (collision Q p xi) := by
  have hm (k : ℕ) : signedTaylorMoment k (collision Q p xi) s =
      signedTaylorMoment k (quotient (Q.erase p) xi) s-signedTaylorMoment k (quotient Q xi) s :=
    signedTaylorMoment_sub k
      (analyticAt_quotient (Q.erase p) (fun q hq => h16 q (Finset.mem_of_mem_erase hq)) hs xi)
      (analyticAt_quotient Q h16 hs xi)
  simp only [rectangleMoment,hm,mul_sub,Finset.sum_sub_distrib]
  ring

/-- The marked prime runs independently of the least-prime tail. The
errors from doing this are separately estimated below. -/
def separatedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ r ∈ A, ∑ p ∈ A, rectangleMoment N p r s xi (quotient (tailPrimes A r) xi)

/-- The signed error at one ordered-prime incidence, including the
newly admitted incidences where the high-order prime is not larger. -/
def incidenceDifference (A : Finset ℕ) (N p r : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (if r < p then rectangleMoment N p r s xi (quotient (middlePrimes A p r) xi) else 0)-
    rectangleMoment N p r s xi (quotient (tailPrimes A r) xi)

theorem symbol_difference_ledger (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    quotientSymbol A N s xi-separatedSymbol A N s xi =
      ∑ r ∈ A, ∑ p ∈ A, incidenceDifference A N p r s xi := by
  simp only [quotientSymbol,separatedSymbol,incidenceDifference,
    Finset.sum_sub_distrib,Finset.sum_filter]

theorem incidence_difference_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {p r : ℕ} (hp : p ∈ A)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖incidenceDifference A N p r s xi‖ ≤
      (4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220))*
        (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
          (‖1-zetaPrimeFeature (Complex.I*xi) p‖*‖1-zetaPrimeFeature (Complex.I*xi) r‖) := by
  have htail : ∀ q ∈ tailPrimes A r, 16 ≤ q := fun q hq => h16 q (Finset.mem_filter.mp hq).1
  unfold incidenceDifference
  by_cases hpr : r < p
  · rw [if_pos hpr,middle_eq_erase,rectangle_erase_ledger _ htail N p r (by linarith) xi,
      add_sub_cancel_left]
    exact collision_rectangle_bound _ htail (Finset.mem_filter.mpr ⟨hp,hpr⟩) N r (hhead p hp) hR hs xi
  · rw [if_neg hpr,zero_sub,norm_neg]
    apply (wrong_order_rectangle _ htail N p r (by have := h16 p hp; omega)
      (Nat.le_of_not_gt hpr) hR hs xi).trans
    have he : Real.exp (-(N : ℝ)/10) ≤ Real.exp (-(N : ℝ)/220) :=
      Real.exp_le_exp.mpr (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    have hb := mainBudget_nonneg N (s.re-R) hR
    have hc : mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/10) ≤
        4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220) := by
      nlinarith [mul_le_mul_of_nonneg_left he hb,Real.exp_pos (-(N : ℝ)/220)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by unfold zetaPrimeExpWeight; positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A finite positive majorant for both marked Fourier zeros. It is
used only on the already isolated incidence error. -/
def phaseMass (A : Finset ℕ) (sigma xi : ℝ) : ℝ :=
  ∑ p ∈ A, zetaPrimeExpWeight sigma p*(1-Real.cos (Real.log p*xi))

theorem phaseMass_nonneg (A : Finset ℕ) (sigma xi : ℝ) : 0 ≤ phaseMass A sigma xi := by
  apply Finset.sum_nonneg
  intro p _hp
  exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))

theorem phaseMass_neg (A : Finset ℕ) (sigma xi : ℝ) : phaseMass A sigma (-xi) = phaseMass A sigma xi := by
  simp only [phaseMass,mul_neg,Real.cos_neg]

theorem pair_phase_sum (A : Finset ℕ) (sigma xi : ℝ) :
    (∑ r ∈ A, ∑ p ∈ A,
      (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*
        ((1-Real.cos (Real.log p*xi))+(1-Real.cos (Real.log r*xi)))) =
      2*(∑ p ∈ A, zetaPrimeExpWeight sigma p)*phaseMass A sigma xi := by
  have he (p r : ℕ) : (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*
      ((1-Real.cos (Real.log p*xi))+(1-Real.cos (Real.log r*xi))) =
      zetaPrimeExpWeight sigma r*(zetaPrimeExpWeight sigma p*(1-Real.cos (Real.log p*xi)))+
        (zetaPrimeExpWeight sigma r*(1-Real.cos (Real.log r*xi)))*zetaPrimeExpWeight sigma p := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,phaseMass]
  ring

theorem symbol_difference_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (xi : ℝ) :
    ‖quotientSymbol A N s xi-separatedSymbol A N s xi‖ ≤
      8*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*
        mass (s.re-R)*phaseMass A (s.re-R) xi := by
  have hB := mainBudget_nonneg N (s.re-R) hR
  rw [symbol_difference_ledger]
  calc
    _ ≤ ∑ r ∈ A, ∑ p ∈ A, ‖incidenceDifference A N p r s xi‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ r ∈ A, ∑ p ∈ A,
        (4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220))*
          (zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
            ((1-Real.cos (Real.log p*xi))+(1-Real.cos (Real.log r*xi))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro p hp
      exact (incidence_difference_bound A h16 N hhead hp hR hs xi).trans
        (mul_le_mul_of_nonneg_left (marked_phase_bound p r xi)
          (by unfold zetaPrimeExpWeight; positivity))
    _ = (4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220))*
        (2*(∑ p ∈ A, zetaPrimeExpWeight (s.re-R) p)*phaseMass A (s.re-R) xi) := by
      rw [← pair_phase_sum]
      simp only [Finset.mul_sum,mul_assoc]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sum_mass_le A hs) (by norm_num : (0 : ℝ) ≤ 2))
        (phaseMass_nonneg A (s.re-R) xi)
      apply (mul_le_mul_of_nonneg_left h
        (show 0 ≤ 4*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220) by positivity)).trans_eq
      ring

/-- The high-order prime factor remains a difference at the TWO actual
complex frequencies. Neither phase is replaced by a source limit. -/
def primeDifference (A : Finset ℕ) (j : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ p ∈ A, (zetaPrimeLogKernel j s p-zetaPrimeLogKernel j (s+Complex.I*xi) p)

theorem coeff_leg_difference (j p : ℕ) (s : ℂ) (xi : ℝ) :
    PowerSeries.coeff j (leg s xi p) =
      zetaPrimeLogKernel j s p-zetaPrimeLogKernel j (s+Complex.I*xi) p := by
  rw [coeff_leg]
  unfold zetaPrimeLogKernel zetaPrimeFeature
  rw [add_mul,neg_add,Complex.exp_add]
  ring

/-- The complete middle count product is kept in the ordered cofactor
factor. The large prime sum is now independent, at its exact finite cutoff. -/
theorem separatedSymbol_factor (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    separatedSymbol A N s xi =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        primeDifference A j s xi*
          ∑ r ∈ A, PowerSeries.coeff h (leg s xi r)*
            signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s := by
  have hr (r : ℕ) : (∑ p ∈ A, rectangleMoment N p r s xi (quotient (tailPrimes A r) xi)) =
      ∑ j ∈ Finset.range (N+2), ∑ h ∈ ZetaRieszSkewAllocation.rectangleOrders N j,
        primeDifference A j s xi*(PowerSeries.coeff h (leg s xi r)*
          signedTaylorMoment (N+1-j-h) (quotient (tailPrimes A r) xi) s) := by
    unfold rectangleMoment
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _hh
    simp only [primeDifference,Finset.sum_mul,coeff_leg_difference,mul_assoc]
  unfold separatedSymbol
  simp_rw [hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [Finset.mul_sum]

/-- Pair the separated symbol at both original Fourier signs before
division by the frequency square. -/
def separatedPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*separatedSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*separatedSymbol A N s (-xi)

theorem pair_difference_bound (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L xi : ℝ) :
    ‖(quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2‖ ≤
      (16*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R))*
        (phaseMass A (s.re-R) xi/xi^2) := by
  have he : quotientPair A N s L xi-separatedPair A N s L xi =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*(quotientSymbol A N s xi-separatedSymbol A N s xi)+
        Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*(quotientSymbol A N s (-xi)-separatedSymbol A N s (-xi)) := by
    unfold quotientPair separatedPair
    ring
  have hb : ‖quotientPair A N s L xi-separatedPair A N s L xi‖ ≤
      16*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R)*phaseMass A (s.re-R) xi := by
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    have hp := symbol_difference_bound A h16 N hhead hR hs xi
    have hm := symbol_difference_bound A h16 N hhead hR hs (-xi)
    rw [phaseMass_neg] at hm
    linarith
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  apply (div_le_div_of_nonneg_right hb (sq_nonneg xi)).trans_eq
  ring

theorem integrable_phaseMass_div (A : Finset ℕ) (sigma : ℝ) :
    IntegrableOn (fun xi : ℝ => phaseMass A sigma xi/xi^2) (Ioi 0) := by
  simp only [phaseMass,Finset.sum_div,mul_div_assoc]
  exact integrable_finsetSum _ (fun p _ =>
    (CosineHinge.integrable_one_sub_cos_div_sq (Real.log p)).const_mul _)

theorem integral_phaseMass_div (A : Finset ℕ) (sigma : ℝ) :
    (∫ xi : ℝ in Ioi 0, phaseMass A sigma xi/xi^2) =
      (Real.pi/2)*(∑ p ∈ A, Real.log p*zetaPrimeExpWeight sigma p) := by
  simp only [phaseMass,Finset.sum_div,mul_div_assoc]
  rw [integral_finsetSum _ (fun (p : ℕ) _ =>
    (CosineHinge.integrable_one_sub_cos_div_sq (Real.log p)).const_mul (zetaPrimeExpWeight sigma p))]
  simp only [integral_const_mul,CosineHinge.integral_one_sub_cos_div_sq,
    abs_of_nonneg (Real.log_natCast_nonneg _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem measurable_quotient_moment (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (k : ℕ) :
    StronglyMeasurable (fun xi : ℝ => signedTaylorMoment k (quotient Q xi) s) := by
  have hf : StronglyMeasurable (fun v : ℝ × ℂ => quotient Q v.1 v.2) := by
    apply Measurable.stronglyMeasurable
    unfold quotient zetaPrimeFeature
    fun_prop
  have he (xi : ℝ) := ZetaRieszEulerMoments.signedTaylorMoment_eq_circleIntegral hR
    (f := quotient Q xi) (s := s) (show DiffContOnCl ℂ _ (Metric.ball s R) from by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball s hR.ne']
      intro z hz
      exact (analyticAt_quotient Q h16
        (by linarith [ZetaRieszEulerMoments.disc_re_lower_bound hz]) xi).differentiableAt.differentiableWithinAt) k
  simp_rw [he]
  exact (ZetaRieszEulerMoments.stronglyMeasurable_parametric_circle _ hf s R k).const_mul _

theorem measurable_rectangle_quotient (Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (N p r : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) :
    StronglyMeasurable (fun xi : ℝ => rectangleMoment N p r s xi (quotient Q xi)) := by
  have hm := fun k => measurable_quotient_moment Q h16 hR hs k
  simp only [rectangleMoment,coeff_leg]
  unfold zetaPrimeFeature
  fun_prop

theorem measurable_symbol_difference (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) :
    StronglyMeasurable (fun xi : ℝ => quotientSymbol A N s xi-separatedSymbol A N s xi) := by
  have hm (p r : ℕ) := measurable_rectangle_quotient (middlePrimes A p r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r hR hs
  have ht (p r : ℕ) := measurable_rectangle_quotient (tailPrimes A r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r hR hs
  unfold quotientSymbol separatedSymbol
  exact (A.stronglyMeasurable_fun_sum (fun r _ =>
    (A.filter (fun p => r < p)).stronglyMeasurable_fun_sum (fun p _ => hm p r))).sub
      (A.stronglyMeasurable_fun_sum (fun r _ => A.stronglyMeasurable_fun_sum (fun p _ => ht p r)))

theorem measurable_pair_difference (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ) :
    StronglyMeasurable (fun xi : ℝ =>
      (quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2) := by
  have hm := (measurable_symbol_difference A h16 N hR hs).measurable
  have hn := hm.comp measurable_neg
  have he (xi : ℝ) : quotientPair A N s L xi-separatedPair A N s L xi =
      Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*(quotientSymbol A N s xi-separatedSymbol A N s xi)+
        Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*(quotientSymbol A N s (-xi)-separatedSymbol A N s (-xi)) := by
    unfold quotientPair separatedPair
    ring
  simp_rw [he]
  apply Measurable.stronglyMeasurable
  fun_prop

theorem integrable_pair_difference (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ) :
    IntegrableOn (fun xi : ℝ =>
      (quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2) (Ioi 0) := by
  apply ((integrable_phaseMass_div A (s.re-R)).const_mul
    (16*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R))).mono'
  · exact (measurable_pair_difference A h16 N hR hs L).aestronglyMeasurable
  · exact Eventually.of_forall (pair_difference_bound A h16 N hhead hR hs L)

theorem norm_integral_pair_difference_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ) :
    ‖∫ xi : ℝ in Ioi 0, (quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2‖ ≤
      8*Real.pi*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R)*logMass (s.re-R) := by
  have hB := mainBudget_nonneg N (s.re-R) hR
  have hM := mass_nonneg (s.re-R)
  have h := norm_integral_le_of_norm_le
    ((integrable_phaseMass_div A (s.re-R)).const_mul
      (16*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R)))
    (Eventually.of_forall (pair_difference_bound A h16 N hhead hR hs L))
  rw [integral_const_mul,integral_phaseMass_div] at h
  apply h.trans
  have h' := mul_le_mul_of_nonneg_left (sum_logMass_le A hs)
    (show 0 ≤ (16*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R))*(Real.pi/2) by positivity)
  convert h' using 1 <;> ring

/-- The genuinely integrated separated response, with its original
physical length and logarithmic mark. -/
def separatedResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, separatedPair A N s L xi/(xi : ℂ)^2

theorem integrable_separatedPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => separatedPair A N s L xi/(xi : ℂ)^2) (Ioi 0) := by
  have he (xi : ℝ) : separatedPair A N s L xi/(xi : ℂ)^2 =
      quotientPair A N s L xi/(xi : ℂ)^2-
        (quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2 := by ring
  simp_rw [he]
  exact (integrable_quotientPair A hA h16 N hhead hR hs L).sub
    (integrable_pair_difference A h16 N hhead hR hs L)

theorem response_difference_eq (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) (L : ℝ) :
    quotientResponse A N s L-separatedResponse A N s L =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Ioi 0, (quotientPair A N s L xi-separatedPair A N s L xi)/(xi : ℂ)^2 := by
  simp only [sub_div]
  rw [integral_sub (integrable_quotientPair A hA h16 N hhead hR hs L)
    (integrable_separatedPair A hA h16 N hhead hR hs L),mul_sub]
  rfl

/-- Both incidence errors are paid after the actual paired Fourier
integral; no signed main bound is assumed. -/
theorem norm_response_difference_le (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hs : 1 < s.re-R) {L : ℝ} (hL : 0 < L) :
    ‖quotientResponse A N s L-separatedResponse A N s L‖ ≤
      (4*((N : ℝ)+1)*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*
        mass (s.re-R)*logMass (s.re-R))/L := by
  rw [response_difference_eq A hA h16 N hhead hR hs L,
    norm_mul,norm_div,norm_mul,norm_mul,Complex.norm_natCast]
  norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left (norm_integral_pair_difference_le A h16 N hhead hR hs L)
    (by positivity)).trans_eq
  push_cast
  field_simp
  ring

theorem norm_scaled_response_difference_le (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R u U L : ℝ} (hR : 0 < R) (hs : 1 < s.re-R)
    (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*(quotientResponse A N s L-separatedResponse A N s L)‖ ≤
      (4*Real.exp (4*mass (s.re-R))*mass (s.re-R)*logMass (s.re-R)*(U/R))*
        ((N : ℝ)+2)^3*(U/R*Real.exp (-(1 : ℝ)/220))^N := by
  have hU0 : 0 ≤ U := hu.trans hU
  have hM := mass_nonneg (s.re-R)
  have hH := logMass_nonneg hs
  have hB := mainBudget_nonneg N (s.re-R) hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_response_difference_le A hA h16 N hhead hR hs (by linarith : 0 < L))
    (norm_nonneg _) (pow_nonneg hU0 _)).trans
  have hdiv : (4*((N : ℝ)+1)*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*
      mass (s.re-R)*logMass (s.re-R))/L ≤
      4*((N : ℝ)+2)*mainBudget N (s.re-R) R*Real.exp (-(N : ℝ)/220)*mass (s.re-R)*logMass (s.re-R) := by
    apply (div_le_self (by positivity) hL).trans
    gcongr
    linarith
  apply (mul_le_mul_of_nonneg_left hdiv (pow_nonneg hU0 _)).trans_eq
  have hexp : Real.exp (-(N : ℝ)/220) = Real.exp (-(1 : ℝ)/220)^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold mainBudget
  rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ R]
  field_simp

/-- Uniform arithmetic separation at source scale, including every
incidence and both signs of the Fourier frequency. -/
theorem tendsto_response_difference (A : ℕ → Finset ℕ)
    (hA : ∀ N p, p ∈ A N → p.Prime) (h16 : ∀ N p, p ∈ A N → 16 ≤ p)
    (hhead : ∀ N p, p ∈ A N → (N : ℝ)/110 ≤ Real.log p)
    (height length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (quotientResponse (A N) N (3/2+Complex.I*height N) (length N)-
        separatedResponse (A N) N (3/2+Complex.I*height N) (length N))) atTop (nhds 0) := by
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
  let C : ℝ := 4*Real.exp (4*mass (1+1/262144))*mass (1+1/262144)*logMass (1+1/262144)*
    (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm (a := fun N : ℕ => C*(((N : ℝ)+2)^3*sourceRate^N))
  · intro N
    have h := norm_scaled_response_difference_le (A N) (hA N) (h16 N) N (hhead N) safeRadius_pos
      (show 1 < (3/2+Complex.I*(height N : ℂ)).re-safeRadius by rw [hs]; norm_num) hu hU (hL N)
    simpa only [hs,sourceRate,mul_assoc,C] using h
  · simpa only [mul_zero] using ht.const_mul C

/-- The separated main response at the original actual prime cutoffs. -/
def separatedMain (u y : ℝ) (N : ℕ) : ℂ :=
  separatedResponse (ZetaRieszRoughEulerTransfer.roughPrimes u N) N
    (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N)

theorem tendsto_main_sub_separated {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (height : ℕ → ℝ) :
    Tendsto (fun N => (u : ℂ)^(N+1)*
      (ZetaRieszRoughEulerTransfer.mainQuotient u (height N) N-separatedMain u (height N) N))
      atTop (nhds 0) :=
  tendsto_response_difference (ZetaRieszRoughEulerTransfer.roughPrimes u)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_prime hp)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_sixteen hp)
    (fun _ _ hp => ZetaRieszRoughEulerTransfer.rough_head hp)
    height (SquarefreeVaughanLogSource.length u) (ZetaRieszHeadOrders.one_le_length u) hu hU

/-- The original signed packet is source-equivalent to the separated
high-prime difference times the ordered cofactor response. The separation
is paid; the remaining signed product is NOT asserted to be small. -/
theorem tendsto_separated_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (separatedMain u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      atTop (nhds 0) := by
  have h := (ZetaRieszRoughEulerTransfer.tendsto_main_sub_current hu hU y).sub
    ((tendsto_main_sub_separated (by linarith : 0 ≤ u) hU (fun _ => y)).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder)
  simp only [sub_self] at h
  convert h using 1
  ext j
  simp only [Function.comp_def]
  ring

end
end RiemannGaussian.ZetaRieszMarkedSeparation
