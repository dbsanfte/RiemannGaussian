/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelectedGamma
import RiemannGaussian.ZetaRieszUnshiftedCharacter
import RiemannGaussian.ZetaSquarefreeRieszWindows

/-!
# Exact physical inversion of the selected shifted resonance

The Gamma kernel translates the Riesz cutoff, retaining both frequencies
and the complex cofactor weights. Absolute estimates below justify Fubini
only; they are not a payment of the selected source.
-/

namespace RiemannGaussian.ZetaRieszSelectedPhysical
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical
open ZetaRieszSelectedGamma ZetaRieszMarkedEulerError

/-- The original cutoff Fourier phase, without a conjugation of the cofactor. -/
def phase (L xi : ℝ) : ℂ := Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)

theorem norm_phase (L xi : ℝ) : ‖phase L xi‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- Both signed frequencies of the same complex cofactor. -/
def pair (C : ℝ → ℂ) (L xi : ℝ) : ℂ :=
  phase L xi*C xi+phase L (-xi)*C (-xi)

/-- A finite two-prime difference already has two Fourier zeros. -/
def twoPrimeCharacter (p q : ℕ) (xi : ℝ) : ℂ :=
  (1-zetaPrimeFeature (Complex.I*xi) p)*(1-zetaPrimeFeature (Complex.I*xi) q)

theorem integrable_twoPrimeCharacter (p q : ℕ) :
    IntegrableOn (fun xi : ℝ => twoPrimeCharacter p q xi/(xi : ℂ)^2) (Ioi 0) := by
  apply ((CosineHinge.integrable_one_sub_cos_div_sq (-Real.log p)).add
    (CosineHinge.integrable_one_sub_cos_div_sq (-Real.log q))).mono'
  · unfold twoPrimeCharacter zetaPrimeFeature
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with xi
    have hp := ZetaPrimeCharacterRemainder.norm_character_difference_sq (-Real.log p*xi)
    have hq := ZetaPrimeCharacterRemainder.norm_character_difference_sq (-Real.log q*xi)
    have he (r : ℕ) : zetaPrimeFeature (Complex.I*xi) r =
        Complex.exp (((-Real.log r*xi : ℝ) : ℂ)*Complex.I) := by
      unfold zetaPrimeFeature; congr 1; push_cast; ring
    rw [← he p] at hp
    rw [← he q] at hq
    have hh : ‖1-zetaPrimeFeature (Complex.I*xi) p‖*
        ‖1-zetaPrimeFeature (Complex.I*xi) q‖ ≤
        (1-Real.cos (-Real.log p*xi))+(1-Real.cos (-Real.log q*xi)) := by
      nlinarith [sq_nonneg (‖1-zetaPrimeFeature (Complex.I*xi) p‖-
        ‖1-zetaPrimeFeature (Complex.I*xi) q‖)]
    simp only [twoPrimeCharacter,norm_div,norm_mul,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,sq_abs]
    simpa only [add_div,Pi.add_apply] using div_le_div_of_nonneg_right hh (sq_nonneg xi)

theorem integrable_twoPrimeCharacter_neg (p q : ℕ) :
    IntegrableOn (fun xi : ℝ => twoPrimeCharacter p q (-xi)/(xi : ℂ)^2) (Ioi 0) := by
  apply (integrable_twoPrimeCharacter p q).norm.mono'
  · unfold twoPrimeCharacter zetaPrimeFeature
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards with xi
    have he (r : ℕ) : zetaPrimeFeature (Complex.I*(-xi)) r =
        (starRingEnd ℂ) (zetaPrimeFeature (Complex.I*xi) r) := by
      unfold zetaPrimeFeature
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_neg,map_mul,Complex.conj_I,Complex.conj_ofReal]
      ring
    have hw : twoPrimeCharacter p q (-xi) =
        (starRingEnd ℂ) (twoPrimeCharacter p q xi) := by
      simp only [twoPrimeCharacter,Complex.ofReal_neg,he,map_mul,map_sub,map_one]
    simp only [hw,norm_div,Complex.norm_conj,le_refl]

/-- The genuine product-space integrability needed for the selected
Laplace/Fourier exchange. Both signed frequency terms remain together. -/
theorem gamma_pair_integrable {u : ℝ} (hu : 0 < u) (j : ℕ)
    (C : ℝ → ℂ) (hC : Measurable C)
    (hp : IntegrableOn (fun xi : ℝ => C xi/(xi : ℂ)^2) (Ioi 0))
    (hm : IntegrableOn (fun xi : ℝ => C (-xi)/(xi : ℂ)^2) (Ioi 0)) (L : ℝ) :
    Integrable (fun v : ℝ × ℝ => (gammaKernel u j v.1 : ℂ)*
      (pair C (L-v.1) v.2/(v.2 : ℂ)^2))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply ((gammaKernel_integrable hu j).norm.mul_prod (hp.norm.add hm.norm)).mono'
  · unfold gammaKernel pair phase
    fun_prop
  · filter_upwards with v
    rw [norm_mul,Complex.norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold pair
    rw [add_div]
    apply (norm_add_le _ _).trans
    simp only [mul_div_assoc,norm_mul,norm_phase,one_mul,Pi.add_apply,le_refl]

/-- Both phases of precisely the selected shifted mark. -/
def selectedPair (C : ℝ → ℂ) (u : ℝ) (j : ℕ) (L xi : ℝ) : ℂ :=
  phase L xi*ZetaRieszShiftedExterior.shiftedMark (-(u : ℂ)) j xi*C xi+
    phase L (-xi)*ZetaRieszShiftedExterior.shiftedMark (-(u : ℂ)) j (-xi)*C (-xi)

theorem phase_sub (L t xi : ℝ) :
    phase (L-t) xi = phase L xi*Complex.exp (-(Complex.I*xi)*(t : ℂ)) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gamma_pair_integral {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j)
    (C : ℝ → ℂ) (L xi : ℝ) :
    (1/(j : ℂ))*(∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*pair C (L-t) xi) =
      (u : ℂ)^j*selectedPair C u j L xi := by
  have hi (x : ℝ) := (gammaKernel_fourier hu hj x).1
  have he (t : ℝ) : (gammaKernel u j t : ℂ)*pair C (L-t) xi =
      (phase L xi*C xi)*((gammaKernel u j t : ℂ)*Complex.exp (-(Complex.I*xi)*(t : ℂ)))+
      (phase L (-xi)*C (-xi))*((gammaKernel u j t : ℂ)*Complex.exp (-(Complex.I*((-xi : ℝ) : ℂ))*(t : ℂ))) := by
    simp only [pair,phase_sub,Complex.ofReal_neg]
    ring
  simp_rw [he]
  rw [integral_add ((hi xi).const_mul _) ((hi (-xi)).const_mul _),
    integral_const_mul,integral_const_mul]
  have hp := selected_shiftedMark_eq_laplace hu hj xi
  have hm := selected_shiftedMark_eq_laplace hu hj (-xi)
  unfold selectedPair
  linear_combination -(phase L xi*C xi)*hp-(phase L (-xi)*C (-xi))*hm

/-- Exact Fubini inversion; the right side is ready for the finite Riesz
identity at the translated cutoff. The source is preserved, not bounded. -/
theorem selected_pair_eq_gamma_average {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j)
    (C : ℝ → ℂ) (hC : Measurable C)
    (hp : IntegrableOn (fun xi : ℝ => C xi/(xi : ℂ)^2) (Ioi 0))
    (hm : IntegrableOn (fun xi : ℝ => C (-xi)/(xi : ℂ)^2) (Ioi 0)) (L : ℝ) :
    (u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
      (∫ xi : ℝ in Ioi 0, selectedPair C u j L xi/(xi : ℂ)^2) =
    (1/(j : ℂ))*(∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*
      (-1/(2*(Real.pi : ℂ))*(∫ xi : ℝ in Ioi 0, pair C (L-t) xi/(xi : ℂ)^2))) := by
  have hs := integral_integral_swap
    (f := fun t xi : ℝ => (gammaKernel u j t : ℂ)*(pair C (L-t) xi/(xi : ℂ)^2))
    (gamma_pair_integrable hu j C hC hp hm L)
  have hf (xi : ℝ) :
      (1/(j : ℂ))*(∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*
        (pair C (L-t) xi/(xi : ℂ)^2)) =
      (u : ℂ)^j*(selectedPair C u j L xi/(xi : ℂ)^2) := by
    simp_rw [← mul_div_assoc]
    rw [integral_div]
    calc
      _ = ((1/(j : ℂ))*(∫ t : ℝ in Ioi 0,
          (gammaKernel u j t : ℂ)*pair C (L-t) xi))/(xi : ℂ)^2 := by ring
      _ = _ := by rw [gamma_pair_integral hu hj]
  calc
    _ = (-1/(2*(Real.pi : ℂ)))*
        (∫ xi : ℝ in Ioi 0, (1/(j : ℂ))*(∫ t : ℝ in Ioi 0,
          (gammaKernel u j t : ℂ)*(pair C (L-t) xi/(xi : ℂ)^2))) := by
      simp_rw [hf]
      rw [integral_const_mul]
      ring
    _ = (-1/(2*(Real.pi : ℂ)))*((1/(j : ℂ))*(∫ t : ℝ in Ioi 0,
        ∫ xi : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*(pair C (L-t) xi/(xi : ℂ)^2))) := by
      rw [integral_const_mul,← hs]
    _ = _ := by
      simp_rw [integral_const_mul]
      rw [show (fun t : ℝ => (gammaKernel u j t : ℂ)*
        (-1/(2*(Real.pi : ℂ))*(∫ xi : ℝ in Ioi 0, pair C (L-t) xi/(xi : ℂ)^2))) =
        (fun t : ℝ => (-1/(2*(Real.pi : ℂ)))*((gammaKernel u j t : ℂ)*
          (∫ xi : ℝ in Ioi 0, pair C (L-t) xi/(xi : ℂ)^2))) by
          funext t; ring, integral_const_mul]
      ring

theorem selected_pair_integrable {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j)
    (C : ℝ → ℂ) (hC : Measurable C)
    (hp : IntegrableOn (fun xi : ℝ => C xi/(xi : ℂ)^2) (Ioi 0))
    (hm : IntegrableOn (fun xi : ℝ => C (-xi)/(xi : ℂ)^2) (Ioi 0)) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => selectedPair C u j L xi/(xi : ℂ)^2) (Ioi 0) := by
  have hi := (gamma_pair_integrable hu j C hC hp hm L).integral_prod_right
  apply (hi.const_mul ((u : ℂ)^j)⁻¹).const_mul (1/(j : ℂ)) |>.congr
  filter_upwards with xi
  have hf : (∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*(pair C (L-t) xi/(xi : ℂ)^2)) =
      (∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*pair C (L-t) xi)/(xi : ℂ)^2 := by
    simp_rw [← mul_div_assoc]
    rw [integral_div]
  rw [hf]
  calc
    _ = ((u : ℂ)^j)⁻¹*((1/(j : ℂ))*(∫ t : ℝ in Ioi 0,
        (gammaKernel u j t : ℂ)*pair C (L-t) xi))/(xi : ℂ)^2 := by ring
    _ = _ := by
      rw [gamma_pair_integral hu hj C L xi,← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hu.ne')),one_mul]

open ZetaSquarefreeRieszWindows

theorem twoPrimeCharacter_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (xi : ℝ) : twoPrimeCharacter p q xi = ZetaRieszPrimeFourier.primeProduct (p*q) xi := by
  simp [twoPrimeCharacter,ZetaRieszPrimeFourier.primeProduct,
    Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors,hq.primeFactors,hpq]

/-- The actual two-prime cofactor has the compact positive tent inverse,
at every translated cutoff, including negative cutoffs. -/
theorem twoPrime_pair_integral {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (L : ℝ) :
    -1/(2*(Real.pi : ℂ))*(∫ xi : ℝ in Ioi 0,
      pair (twoPrimeCharacter p q) L xi/(xi : ℂ)^2) =
    (primePairTent (Real.log p) (Real.log q) L : ℂ) := by
  have hsf := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr (by simpa [Nat.dvd_prime hq] using And.intro hp.ne_one hpq),
      hp.squarefree,hq.squarefree⟩
  have he (xi : ℝ) : pair (twoPrimeCharacter p q) L xi =
      ZetaRieszPrimeFourier.primePair (p*q) L xi := by
    simp only [pair,twoPrimeCharacter_eq hp hq hpq,phase,ZetaRieszPrimeFourier.primePair]
  simp_rw [he]
  rw [show (-1 : ℂ)/(2*Real.pi) = -(1/(2*Real.pi)) by ring,
    ← ZetaRieszPrimeFourier.riesz_eq_primePair_integral L hsf
      (by nlinarith [hp.two_le,hq.two_le]) (Nat.not_prime_mul hp.ne_one hq.ne_one)]
  have ht := riesz_two_primes_eq_tent L hp hq hpq
    (show ¬p ∣ 1 by simpa using hp.ne_one) (show ¬q ∣ 1 by simpa using hq.ne_one)
  simpa using congrArg (fun x : ℝ => (x : ℂ)) ht

/-- A positive Gamma average of the literal two-prime Riesz tent. -/
def gammaTent (u : ℝ) (j p q : ℕ) (L : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi 0, gammaKernel u j t*
    primePairTent (Real.log p) (Real.log q) (L-t)

theorem gammaTent_integrable {u : ℝ} (hu : 0 < u) (j p q : ℕ) (L : ℝ) :
    IntegrableOn (fun t => gammaKernel u j t*
      primePairTent (Real.log p) (Real.log q) (L-t)) (Ioi 0) := by
  apply ((gammaKernel_integrable hu j).mul_const (min (Real.log p) (Real.log q))).mono'
  · unfold gammaKernel primePairTent
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h := primePairTent_bounds (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) (L-t)
    rw [Real.norm_of_nonneg (mul_nonneg (gammaKernel_nonneg hu.le ht.le j) h.1)]
    exact mul_le_mul_of_nonneg_left h.2 (gammaKernel_nonneg hu.le ht.le j)

theorem gammaTent_bounds {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j) (p q : ℕ) (L : ℝ) :
    0 ≤ gammaTent u j p q L ∧ gammaTent u j p q L ≤ min (Real.log p) (Real.log q) := by
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (gammaKernel_nonneg hu.le ht.le j)
      (primePairTent_bounds (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) (L-t)).1
  · have hm := (gammaKernel_integrable hu j).mul_const (min (Real.log p) (Real.log q))
    have h := integral_mono_ae (gammaTent_integrable hu j p q L) hm
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_le_mul_of_nonneg_left
          (primePairTent_bounds (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) (L-t)).2
          (gammaKernel_nonneg hu.le ht.le j))
    simpa only [gammaTent,integral_mul_const,integral_gammaKernel hu hj,one_mul] using h

/-- The cheap fixed-atom test has a physical answer: exactly a positive
Gamma average of translated tents, multiplied by the unchanged complex
cofactor coefficient. This is not a bound on that coefficient's real part. -/
theorem selected_twoPrime_eq_gammaTent {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (L : ℝ) :
    (u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
      (∫ xi : ℝ in Ioi 0, selectedPair (twoPrimeCharacter p q) u j L xi/(xi : ℂ)^2) =
    (gammaTent u j p q L : ℂ)/(j : ℂ) := by
  rw [selected_pair_eq_gamma_average hu hj (twoPrimeCharacter p q)
    (by unfold twoPrimeCharacter zetaPrimeFeature; fun_prop)
    (integrable_twoPrimeCharacter p q) (integrable_twoPrimeCharacter_neg p q)]
  simp_rw [twoPrime_pair_integral hp hq hpq,← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  unfold gammaTent
  ring

/-- The exact Euler quotient coefficient. Its denominator is retained. -/
def eulerOdds (p : ℕ) (s : ℂ) : ℂ := zetaPrimeFeature s p/(1-zetaPrimeFeature s p)

theorem eulerOdds_analytic {p : ℕ} (hp : 16 ≤ p) {s : ℂ} (hs : 1/2 ≤ s.re) :
    AnalyticAt ℂ (eulerOdds p) s := by
  have hf : AnalyticAt ℂ (fun z => zetaPrimeFeature z p) s := by
    unfold zetaPrimeFeature; fun_prop
  apply hf.div (analyticAt_const.sub hf)
  have hb := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs hp
  intro he
  change 1-zetaPrimeFeature s p = 0 at he
  have hh : zetaPrimeFeature s p = 1 := by linear_combination -he
  rw [hh,norm_one] at hb
  norm_num at hb

theorem quotient_singleton_moment {p : ℕ} (hp : 16 ≤ p) {s : ℂ} (hs : 1/2 ≤ s.re)
    {k : ℕ} (hk : 0 < k) (xi : ℝ) :
    signedTaylorMoment k (quotient {p} xi) s =
      (1-zetaPrimeFeature (Complex.I*xi) p)*signedTaylorMoment k (eulerOdds p) s := by
  have hb := ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs hp
  have hd : 1-zetaPrimeFeature s p ≠ 0 := by
    intro he
    have hh : zetaPrimeFeature s p = 1 := by linear_combination -he
    rw [hh,norm_one] at hb
    norm_num at hb
  have he : (quotient {p} xi) =ᶠ[nhds s]
      (fun z => 1+(1-zetaPrimeFeature (Complex.I*xi) p)*eulerOdds p z) := by
    have hc : Continuous (fun z : ℂ => 1-zetaPrimeFeature z p) := by
      unfold zetaPrimeFeature; fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hd] with z hz
    simp only [quotient,Finset.prod_singleton,eulerOdds]
    field_simp
    ring
  have ha : AnalyticAt ℂ (fun z => (1-zetaPrimeFeature (Complex.I*xi) p)*eulerOdds p z) s :=
    analyticAt_const.mul (eulerOdds_analytic hp hs)
  rw [signedTaylorMoment_congr k he,signedTaylorMoment_add k analyticAt_const ha,
    signedTaylorMoment_const_mul,moment_one]
  simp [PowerSeries.coeff_one,Nat.ne_of_gt hk]

/-- The cofactor coefficient keeps the actual least-prime derivative and
the correlated remaining order. No prime/cofactor is completed here. -/
def twoPrimeWeight (N j h p q : ℕ) (s : ℂ) : ℂ :=
  zetaPrimeLogKernel h s p*signedTaylorMoment (N+1-j-h) (eulerOdds q) s

theorem cofactor_two_primes {p q : ℕ} (hpq : p < q) (hq : 16 ≤ q)
    {s : ℂ} (hs : 1/2 ≤ s.re) {N j h : ℕ}
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (xi : ℝ) :
    ZetaRieszMarkedPrimeCompletion.cofactor {p,q} N j h s xi =
      twoPrimeWeight N j h p q s*twoPrimeCharacter p q xi := by
  have hk : 0 < N+1-j-h := by
    have hb := (Finset.mem_filter.mp hh).2
    omega
  have htp : ZetaRieszMarkedSeparation.tailPrimes {p,q} p = {q} := by
    ext a
    simp only [ZetaRieszMarkedSeparation.tailPrimes,Finset.mem_filter,Finset.mem_insert,
      Finset.mem_singleton]
    omega
  have htq : ZetaRieszMarkedSeparation.tailPrimes {p,q} q = ∅ := by
    ext a
    simp only [ZetaRieszMarkedSeparation.tailPrimes,Finset.mem_filter,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,iff_false,not_and]
    omega
  simp only [ZetaRieszMarkedPrimeCompletion.cofactor,Finset.sum_pair hpq.ne,
    htp,htq,ZetaRieszMarkedEuler.coeff_leg,quotient_singleton_moment hq hs hk]
  have he : quotient ∅ xi = fun _ => (1 : ℂ) := by ext z; simp [quotient]
  rw [he,moment_one]
  simp only [PowerSeries.coeff_one,if_neg (Nat.ne_of_gt hk),mul_zero,add_zero]
  unfold twoPrimeWeight twoPrimeCharacter
  ring

/-- The fixed rectangle atom of the ACTUAL ordered quotient, with both
Fourier phases and its unchanged complex arithmetic coefficient. -/
theorem selected_cofactor_two_primes_eq_gammaTent {u : ℝ} (hu : 0 < u)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq16 : 16 ≤ q)
    {s : ℂ} (hs : 1/2 ≤ s.re) {N j h : ℕ} (hj : 0 < j)
    (hh : h ∈ ZetaRieszSkewAllocation.rectangleOrders N j) (L : ℝ) :
    (u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
      (∫ xi : ℝ in Ioi 0, selectedPair
        (ZetaRieszMarkedPrimeCompletion.cofactor {p,q} N j h s) u j L xi/(xi : ℂ)^2) =
      twoPrimeWeight N j h p q s*(gammaTent u j p q L : ℂ)/(j : ℂ) := by
  have he (xi : ℝ) : selectedPair
      (ZetaRieszMarkedPrimeCompletion.cofactor {p,q} N j h s) u j L xi/(xi : ℂ)^2 =
      twoPrimeWeight N j h p q s*
        (selectedPair (twoPrimeCharacter p q) u j L xi/(xi : ℂ)^2) := by
    simp only [selectedPair,cofactor_two_primes hpq hq16 hs hh]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ = twoPrimeWeight N j h p q s*((u : ℂ)^j*(-1/(2*(Real.pi : ℂ)))*
        (∫ xi : ℝ in Ioi 0, selectedPair (twoPrimeCharacter p q) u j L xi/(xi : ℂ)^2)) := by ring
    _ = _ := by rw [selected_twoPrime_eq_gammaTent hu hj hp hq hpq.ne]; ring

end
end RiemannGaussian.ZetaRieszSelectedPhysical
