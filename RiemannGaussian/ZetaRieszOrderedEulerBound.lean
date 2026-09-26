/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedEulerError

/-!
# A paid correction for the ordered marked Euler response

The leading quotient stays inside the error estimate. The arithmetic
prime-pair sums, exact factorial rectangle and paired Fourier integral
are all included. This bounds the correction, not the signed main quotient.
-/

namespace RiemannGaussian.ZetaRieszOrderedEulerBound
noncomputable section
open scoped BigOperators Classical
open Complex Filter MeasureTheory Set Topology
open ZetaRieszMarkedEuler ZetaRieszMarkedEulerError

/-- The retained ordered main quotient, acted on by the literal
two-coordinate factorial rectangle. -/
def quotientSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
    rectangleMoment N p r s xi (quotient (middlePrimes A p r) xi)

/-- Both Fourier signs of the retained quotient, at the original
physical Riesz length. -/
def quotientPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*quotientSymbol A N s xi+
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*quotientSymbol A N s (-xi)

/-- This is the full difference of the original and leading responses,
with their prime ordering and marked slots unchanged. -/
def pairedError (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
    rectanglePairError (middlePrimes A p r) N p r s L xi

theorem orderedPair_split (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) {s : ℂ} (hs : 1/2 ≤ s.re) (L xi : ℝ) :
    orderedPair A N s L xi = quotientPair A N s L xi+pairedError A N s L xi := by
  have he (r p : ℕ) (t : ℝ) := rectangle_split (middlePrimes A p r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r hs t
  simp only [orderedPair,orderedSymbol,middleEuler,he,quotientPair,quotientSymbol,
    pairedError,rectanglePairError,Finset.sum_add_distrib,Finset.mul_sum,mul_add]
  ring

theorem integrable_pairedError (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => pairedError A N s L xi/(xi : ℂ)^2) (Ioi 0) := by
  simp only [pairedError,Finset.sum_div]
  apply integrable_finsetSum
  intro r _hr
  apply integrable_finsetSum
  intro p _hp
  exact integrable_rectanglePairError_div (middlePrimes A p r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r
    (fun q hq => hhead q (Finset.mem_filter.mp hq).1) hR hhalf L

/-- The unnormalized integrated difference, before the original
logarithmic-mark factor (N+1)/(2*pi*L). -/
def errorIntegral (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ∫ xi : ℝ in Ioi 0, pairedError A N s L xi/(xi : ℂ)^2

/-- A finite complete mass for all marked prime pairs. -/
def mass (sigma : ℝ) : ℝ := ∑' n, zetaPrimeExpWeight sigma n

/-- A finite logarithmic mass at every strictly safe exponent. -/
def logMass (sigma : ℝ) : ℝ :=
  ((sigma-1)/2)⁻¹*mass ((sigma+1)/2)

theorem mass_nonneg (sigma : ℝ) : 0 ≤ mass sigma :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem logMass_nonneg {sigma : ℝ} (hsigma : 1 < sigma) : 0 ≤ logMass sigma := by
  unfold logMass
  exact mul_nonneg (inv_nonneg.mpr (by linarith)) (mass_nonneg _)

theorem sum_mass_le (A : Finset ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑ p ∈ A, zetaPrimeExpWeight sigma p) ≤ mass sigma :=
  (summable_zetaPrimeExpWeight hsigma).sum_le_tsum A (fun _ _ => (Real.exp_pos _).le)

theorem sum_logMass_le (A : Finset ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑ p ∈ A, Real.log p*zetaPrimeExpWeight sigma p) ≤ logMass sigma := by
  have hp (p : ℕ) : Real.log p*zetaPrimeExpWeight sigma p ≤
      ((sigma-1)/2)⁻¹*zetaPrimeExpWeight ((sigma+1)/2) p := by
    have h := norm_zetaPrimeLogKernel_le 1 (sigma : ℂ) p
      (show 0 < (sigma-1)/2 by linarith)
    simpa only [norm_zetaPrimeLogKernel,pow_one,Nat.factorial_one,Nat.cast_one,div_one,
      Complex.ofReal_re,show sigma-(sigma-1)/2 = (sigma+1)/2 by ring] using h
  apply (Finset.sum_le_sum (fun p _ => hp p)).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_mass_le A (by linarith : 1 < (sigma+1)/2))
    (inv_nonneg.mpr (by linarith))

/-- Prime ordering may be enlarged for this already isolated error;
its full logarithmic pair mass has a cutoff-independent bound. -/
theorem pair_mass_le (A : Finset ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
      (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*
        (Real.log p+Real.log r)) ≤ 2*mass sigma*logMass sigma := by
  have he : (∑ r ∈ A, ∑ p ∈ A,
      (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*
        (Real.log p+Real.log r)) =
      2*(∑ p ∈ A, zetaPrimeExpWeight sigma p)*
        (∑ p ∈ A, Real.log p*zetaPrimeExpWeight sigma p) := by
    have hp (r p : ℕ) : (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*
        (Real.log p+Real.log r) =
      zetaPrimeExpWeight sigma r*(Real.log p*zetaPrimeExpWeight sigma p)+
        (Real.log r*zetaPrimeExpWeight sigma r)*zetaPrimeExpWeight sigma p := by ring
    simp only [hp,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
    ring
  calc
    _ ≤ ∑ r ∈ A, ∑ p ∈ A,
        (zetaPrimeExpWeight sigma p*zetaPrimeExpWeight sigma r)*(Real.log p+Real.log r) := by
      apply Finset.sum_le_sum
      intro r _hr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ =>
        mul_nonneg (by unfold zetaPrimeExpWeight; positivity)
          (add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)))
    _ = _ := he
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left (sum_mass_le A hsigma) (by norm_num : (0 : ℝ) ≤ 2))
      (sum_logMass_le A hsigma)
      (Finset.sum_nonneg (fun p _ => mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le))
      (mul_nonneg (by norm_num) (mass_nonneg sigma))

/-- The full ordered correction is bounded after both marked-prime
sums and Fourier integration. The leading quotient is already included. -/
theorem norm_errorIntegral_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    ‖errorIntegral A N s L‖ ≤
      Real.pi*rectangleBudget N (s.re-R) R*(2*mass (s.re-R)*logMass (s.re-R)) := by
  have hi (r p : ℕ) := integrable_rectanglePairError_div (middlePrimes A p r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r
    (fun q hq => hhead q (Finset.mem_filter.mp hq).1) hR hhalf L
  have hb (r p : ℕ) := integral_norm_rectanglePairError_div_le (middlePrimes A p r)
    (fun q hq => h16 q (Finset.mem_filter.mp hq).1) N p r
    (fun q hq => hhead q (Finset.mem_filter.mp hq).1) hR hhalf L
  have hC : 0 ≤ Real.pi*rectangleBudget N (s.re-R) R :=
    mul_nonneg Real.pi_pos.le (rectangleBudget_nonneg N (s.re-R) hR)
  unfold errorIntegral
  simp only [pairedError,Finset.sum_div]
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun p _ => hi r p))]
  simp_rw [integral_finsetSum _ (fun p _ => hi _ p)]
  calc
    _ ≤ ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
        ‖∫ xi : ℝ in Ioi 0, rectanglePairError (middlePrimes A p r) N p r s L xi/(xi : ℂ)^2‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
        Real.pi*rectangleBudget N (s.re-R) R*
          ((zetaPrimeExpWeight (s.re-R) p*zetaPrimeExpWeight (s.re-R) r)*
            (Real.log p+Real.log r)) := by
      apply Finset.sum_le_sum
      intro r _hr
      apply Finset.sum_le_sum
      intro p _hp
      simpa only [mul_assoc] using (norm_integral_le_integral_norm _).trans (hb r p)
    _ ≤ _ := by
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (pair_mass_le A hhalf) hC

/-- Restore the original logarithmic mark and physical normalization. -/
def errorResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*errorIntegral A N s L

/-- The main quotient after its genuine paired Fourier integral and
the original logarithmic-mark normalization. -/
def quotientResponse (A : Finset ℕ) (N : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
    ∫ xi : ℝ in Ioi 0, quotientPair A N s L xi/(xi : ℂ)^2

theorem integrable_quotientPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => quotientPair A N s L xi/(xi : ℂ)^2) (Ioi 0) := by
  have he (xi : ℝ) : quotientPair A N s L xi/(xi : ℂ)^2 =
      orderedPair A N s L xi/(xi : ℂ)^2-pairedError A N s L xi/(xi : ℂ)^2 := by
    rw [orderedPair_split A h16 N (by linarith) L xi,add_div]
    ring
  simp_rw [he]
  exact (ZetaRieszOrderedEulerCompletion.integrable_orderedPair A hA N s L).sub
    (integrable_pairedError A h16 N hhead hR hhalf L)

/-- An exact integrated split, with both integrals genuinely convergent. -/
theorem response_split (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (h16 : ∀ p ∈ A, 16 ≤ p) (N : ℕ)
    (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) (L : ℝ) :
    ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
      (∫ xi : ℝ in Ioi 0, orderedPair A N s L xi/(xi : ℂ)^2) =
      quotientResponse A N s L+errorResponse A N s L := by
  simp_rw [orderedPair_split A h16 N (s := s) (by linarith) L,add_div]
  rw [integral_add (integrable_quotientPair A hA h16 N hhead hR hhalf L)
    (integrable_pairedError A h16 N hhead hR hhalf L),mul_add]
  rfl

theorem norm_errorResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R) {L : ℝ} (hL : 0 < L) :
    ‖errorResponse A N s L‖ ≤
      (((N : ℝ)+1)*rectangleBudget N (s.re-R) R*mass (s.re-R)*logMass (s.re-R))/L := by
  unfold errorResponse
  rw [norm_mul,norm_div,norm_mul,norm_mul,Complex.norm_natCast]
  norm_num only [norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left (norm_errorIntegral_le A h16 N hhead hR hhalf L)
    (by positivity)).trans_eq
  push_cast
  field_simp

/-- A single fixed rate controls the correction uniformly in all prime
cutoffs, heights and lengths at least one. -/
theorem norm_scaled_errorResponse_le (A : Finset ℕ) (h16 : ∀ p ∈ A, 16 ≤ p)
    (N : ℕ) (hhead : ∀ p ∈ A, (N : ℝ)/110 ≤ Real.log p)
    {s : ℂ} {R u U L : ℝ} (hR : 0 < R) (hhalf : 1 < s.re-R)
    (hu : 0 ≤ u) (hU : u ≤ U) (hL : 1 ≤ L) :
    ‖(u : ℂ)^(N+1)*errorResponse A N s L‖ ≤
      (cost (s.re-R)*mass (s.re-R)*logMass (s.re-R)*(U/R))*
        ((N : ℝ)+2)^3*(U/R*Real.exp (-(1 : ℝ)/220))^N := by
  have hU0 : 0 ≤ U := hu.trans hU
  have hC := cost_nonneg (s.re-R)
  have hM := mass_nonneg (s.re-R)
  have hH := logMass_nonneg hhalf
  have hB := rectangleBudget_nonneg N (s.re-R) hR
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu]
  apply (mul_le_mul (pow_le_pow_left₀ hu hU (N+1))
    (norm_errorResponse_le A h16 N hhead hR hhalf (by linarith : 0 < L))
    (norm_nonneg _) (pow_nonneg hU0 _)).trans
  have hn : (N : ℝ)+1 ≤ N+2 := by linarith
  have hdiv : (((N : ℝ)+1)*rectangleBudget N (s.re-R) R*mass (s.re-R)*logMass (s.re-R))/L ≤
      ((N : ℝ)+2)*rectangleBudget N (s.re-R) R*mass (s.re-R)*logMass (s.re-R) := by
    apply (div_le_self (by positivity) hL).trans
    gcongr
  apply (mul_le_mul_of_nonneg_left hdiv (pow_nonneg hU0 _)).trans_eq
  have hexp : Real.exp (-(N : ℝ)/220) = Real.exp (-(1 : ℝ)/220)^N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold rectangleBudget
  rw [hexp,mul_pow,div_pow,pow_succ U,pow_succ R]
  field_simp

/-- The contour remains strictly inside absolute arithmetic convergence. -/
def safeRadius : ℝ := 3/2-(1+1/262144)

/-- The full prime-head saving after the correlated Cauchy cost, at
the largest source radius in the current restricted campaign. -/
def sourceRate : ℝ :=
  ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius*Real.exp (-(1 : ℝ)/220)

theorem safeRadius_pos : 0 < safeRadius := by norm_num [safeRadius]

/-- The deliberately crude full-product bound still leaves a fixed
geometric saving after normalization at the largest source radius. -/
theorem sourceRate_bounds : 0 ≤ sourceRate ∧ sourceRate < 249/250 := by
  constructor
  · unfold sourceRate ZetaRieszWideOwnerAudit.radiusCeiling
    exact mul_nonneg (div_nonneg (by norm_num) safeRadius_pos.le) (Real.exp_pos _).le
  · unfold sourceRate
    rw [show -(1 : ℝ)/220 = -(1/220 : ℝ) by ring,Real.exp_neg,← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos (1/220))).mpr
    calc
      _ < (249/250 : ℝ)*(1/220+1) := by norm_num [safeRadius,ZetaRieszWideOwnerAudit.radiusCeiling]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1/220)) (by norm_num)

/-- Uniform source-scale decay of the full coupled Euler correction.
No zero hypothesis, prime-density replacement or separate-leg phase
limit is used. The signed main quotient is not estimated by this theorem. -/
theorem tendsto_errorResponse (A : ℕ → Finset ℕ)
    (h16 : ∀ N p, p ∈ A N → 16 ≤ p)
    (hhead : ∀ N p, p ∈ A N → (N : ℝ)/110 ≤ Real.log p)
    (height length : ℕ → ℝ) (hL : ∀ N, 1 ≤ length N)
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N => (u : ℂ)^(N+1)*errorResponse (A N) N
      (3/2+Complex.I*height N) (length N)) atTop (nhds 0) := by
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
  let C : ℝ := cost (1+1/262144)*mass (1+1/262144)*logMass (1+1/262144)*
    (ZetaRieszWideOwnerAudit.radiusCeiling/safeRadius)
  apply squeeze_zero_norm (a := fun N : ℕ => C*(((N : ℝ)+2)^3*sourceRate^N))
  · intro N
    have h := norm_scaled_errorResponse_le (A N) (h16 N) N (hhead N) safeRadius_pos
      (show 1 < (3/2+Complex.I*(height N : ℂ)).re-safeRadius by rw [hs]; norm_num) hu hU (hL N)
    simpa only [hs,sourceRate,mul_assoc,C] using h
  · simpa only [mul_zero] using ht.const_mul C

end
end RiemannGaussian.ZetaRieszOrderedEulerBound
