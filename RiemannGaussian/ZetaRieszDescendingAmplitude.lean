/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCenteredPhase
import RiemannGaussian.ZetaRieszExtremePrimeCount

/-!
# Exact factorial amplitude bounds beyond the stationary points

Keep the actual cutoff, full polynomial, local pair interval and phase.
The resulting pair costs are independently proved; aggregate cancellation
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszDescendingAmplitude
noncomputable section
open Set Filter Topology
open scoped BigOperators Classical

/-- The extra physical logarithm times a factorial monomial's exponential
shape, before its coefficient and factorial normalization. -/
def momentShape (m : ℕ) (sigma v : ℝ) : ℝ := v ^ (m + 1) * Real.exp (-sigma * v)

/-- The exact derivative keeps the cancellation between polynomial
growth and exponential decay. -/
theorem hasDerivAt_momentShape (m : ℕ) (sigma v : ℝ) :
    HasDerivAt (momentShape m sigma)
      (v ^ m * Real.exp (-sigma * v) * ((m + 1 : ℕ) - sigma * v)) v := by
  have hp := (hasDerivAt_id v).pow (m + 1)
  have he := ((hasDerivAt_id v).const_mul (-sigma)).exp
  have h := hp.mul he
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, pow_succ]
  ring

/-- Past its actual stationary point the complete monomial decreases.
No Taylor-series envelope or auxiliary exponential tilt is used. -/
theorem momentShape_antitoneOn (m : ℕ) {sigma A : ℝ} (hs : 0 ≤ sigma) (hA : 0 ≤ A)
    (hdesc : (m + 1 : ℕ) ≤ sigma * A) : AntitoneOn (momentShape m sigma) (Ici A) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici A)
  · unfold momentShape
    fun_prop
  · unfold momentShape
    fun_prop
  · intro v hv
    rw [interior_Ici, mem_Ioi] at hv
    rw [(hasDerivAt_momentShape m sigma v).deriv]
    have hv0 : 0 ≤ v := hA.trans hv.le
    have hc : ((m + 1 : ℕ) : ℝ) - sigma * v ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hv.le hs]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hc

/-- The entire descending interval has its exact endpoint allowance. -/
theorem momentShape_le_left (m : ℕ) {sigma A v : ℝ} (hs : 0 ≤ sigma) (hA : 0 ≤ A)
    (hdesc : (m + 1 : ℕ) ≤ sigma * A) (hv : A ≤ v) :
    momentShape m sigma v ≤ momentShape m sigma A :=
  momentShape_antitoneOn m hs hA hdesc (le_refl A) hv hv

/-- The complete coefficient and factorial sum at one real logarithmic
coordinate, with no exponential-series relaxation. -/
def amplitudeMajorant (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (sigma v : ℝ) : ℝ :=
  ∑ k ∈ P.support, ‖P.coeff k‖ / (L * (N + k).factorial) * momentShape (N + k) sigma v

/-- The literal complex amplitude is bounded by the exact positive
factorial majorant, retaining every coefficient of the fixed polynomial. -/
theorem norm_logAmplitude_le_majorant {L v : ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (P : Polynomial ℂ) (N : ℕ) (s : ℂ) :
    ‖ZetaRieszPrimeReplacement.logAmplitude L P N s v‖ ≤ amplitudeMajorant L P N s.re v := by
  have hpoly : ‖zetaFactorialPolynomial P N (v : ℂ)‖ ≤
      ∑ k ∈ P.support, ‖P.coeff k‖ * (v ^ (N + k) / (N + k).factorial) := by
    unfold zetaFactorialPolynomial Polynomial.sum
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro k _
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hv, Complex.norm_natCast]
  rw [ZetaRieszPrimeReplacement.logAmplitude, zetaPrimeFilterKernel, Real.log_exp,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg hv, abs_of_pos hL, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-s.re * v)).le) (div_nonneg hv hL.le)).trans_eq
  rw [Finset.sum_mul, Finset.mul_sum]
  unfold amplitudeMajorant
  apply Finset.sum_congr rfl
  intro k _
  simp only [momentShape, pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Beyond every actual polynomial stationary point, the complete
positive majorant is bounded by its exact value at the left endpoint. -/
theorem amplitudeMajorant_le_left (P : Polynomial ℂ) (N : ℕ) {L sigma A v : ℝ}
    (hL : 0 < L) (hs : 0 ≤ sigma) (hA : 0 ≤ A) (hv : A ≤ v)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ sigma * A) :
    amplitudeMajorant L P N sigma v ≤ amplitudeMajorant L P N sigma A := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (momentShape_le_left (N + k) hs hA (hdesc k hk) hv)
    (by positivity)

/-- The full complex amplitude has an exact descending endpoint
allowance whenever the original interval lies beyond all stationary points. -/
theorem norm_logAmplitude_le_left (P : Polynomial ℂ) (N : ℕ) (s : ℂ) {L A v : ℝ}
    (hL : 0 < L) (hs : 0 ≤ s.re) (hA : 0 ≤ A) (hv : A ≤ v)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ s.re * A) :
    ‖ZetaRieszPrimeReplacement.logAmplitude L P N s v‖ ≤ amplitudeMajorant L P N s.re A :=
  (norm_logAmplitude_le_majorant hL (hA.trans hv) P N s).trans
    (amplitudeMajorant_le_left P N hL hs hA hv hdesc)

/-- In the descending region the exact slope costs at most sigma times
the same monomial, rather than a sum of growth and decay costs. -/
theorem abs_momentShape_derivative_le (m : ℕ) {sigma v : ℝ} (hv : 0 ≤ v)
    (hdesc : (m + 1 : ℕ) ≤ sigma * v) :
    |v ^ m * Real.exp (-sigma * v) * ((m + 1 : ℕ) - sigma * v)| ≤
      sigma * momentShape m sigma v := by
  have hE : 0 ≤ v ^ m * Real.exp (-sigma * v) := by positivity
  rw [abs_mul, abs_of_nonneg hE, abs_of_nonpos (sub_nonpos.mpr hdesc)]
  calc
    _ ≤ (v ^ m * Real.exp (-sigma * v)) * (sigma * v) :=
      mul_le_mul_of_nonneg_left (by have hm0 : (0 : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_nonneg _; linarith) hE
    _ = _ := by unfold momentShape; rw [pow_succ]; ring

/-- The slope is uniformly bounded by the same exact endpoint majorant. -/
theorem abs_momentShape_derivative_le_left (m : ℕ) {sigma A v : ℝ}
    (hs : 0 ≤ sigma) (hA : 0 ≤ A) (hv : A ≤ v)
    (hdesc : (m + 1 : ℕ) ≤ sigma * A) :
    |v ^ m * Real.exp (-sigma * v) * ((m + 1 : ℕ) - sigma * v)| ≤
      sigma * momentShape m sigma A := by
  have hvdesc : (m + 1 : ℕ) ≤ sigma * v :=
    hdesc.trans (mul_le_mul_of_nonneg_left hv hs)
  exact (abs_momentShape_derivative_le m (hA.trans hv) hvdesc).trans
    (mul_le_mul_of_nonneg_left (momentShape_le_left m hs hA hdesc hv) hs)

/-- The full real-line amplitude is exactly the coefficient-weighted
monomial sum. No phase of a polynomial coefficient is replaced by a norm. -/
theorem logAmplitude_real_eq_shape_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (sigma v : ℝ) :
    ZetaRieszPrimeReplacement.logAmplitude L P N (sigma : ℂ) v =
      ∑ k ∈ P.support, (-P.coeff k / ((L * (N + k).factorial : ℝ) : ℂ)) *
        (momentShape (N + k) sigma v : ℂ) := by
  unfold ZetaRieszPrimeReplacement.logAmplitude zetaPrimeFilterKernel
    zetaFactorialPolynomial Polynomial.sum
  rw [Real.log_exp, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [momentShape, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv,
    mul_inv_rev, pow_succ]
  ring

/-- The full amplitude derivative keeps the signed growth-decay
factor in every monomial of the actual complex polynomial. -/
theorem hasDerivAt_logAmplitude_shape_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (sigma v : ℝ) :
    HasDerivAt (ZetaRieszPrimeReplacement.logAmplitude L P N (sigma : ℂ))
      (∑ k ∈ P.support, (-P.coeff k / ((L * (N + k).factorial : ℝ) : ℂ)) *
        ((v ^ (N + k) * Real.exp (-sigma * v) * ((N + k + 1 : ℕ) - sigma * v) : ℝ) : ℂ)) v := by
  have he : ZetaRieszPrimeReplacement.logAmplitude L P N (sigma : ℂ) =
      fun x => ∑ k ∈ P.support, (-P.coeff k / ((L * (N + k).factorial : ℝ) : ℂ)) *
        (momentShape (N + k) sigma x : ℂ) := funext (logAmplitude_real_eq_shape_sum L P N sigma)
  rw [he]
  exact HasDerivAt.fun_sum (fun k _ => ((hasDerivAt_momentShape (N + k) sigma v).ofReal_comp).const_mul _)

/-- The actual complete derivative pays sigma times the exact endpoint
majorant, with no exponential-series or lost growth-decay cancellation. -/
theorem norm_shape_derivative_sum_le (P : Polynomial ℂ) (N : ℕ) {L sigma A v : ℝ}
    (hL : 0 < L) (hs : 0 ≤ sigma) (hA : 0 ≤ A) (hv : A ≤ v)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ sigma * A) :
    ‖∑ k ∈ P.support, (-P.coeff k / ((L * (N + k).factorial : ℝ) : ℂ)) *
        ((v ^ (N + k) * Real.exp (-sigma * v) * ((N + k + 1 : ℕ) - sigma * v) : ℝ) : ℂ)‖ ≤
      sigma * amplitudeMajorant L P N sigma A := by
  unfold amplitudeMajorant
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, norm_div, norm_neg]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : (0 : ℝ) < L * (N + k).factorial)]
  exact (mul_le_mul_of_nonneg_left
    (abs_momentShape_derivative_le_left (N + k) hs hA hv (hdesc k hk))
    (by positivity : 0 ≤ ‖P.coeff k‖ / (L * (N + k).factorial))).trans_eq (by ring)

/-- Every two points beyond the stationary region have a full-amplitude
difference bound using the exact endpoint sum and its signed derivative. -/
theorem norm_logAmplitude_sub_le_endpoint (P : Polynomial ℂ) (N : ℕ)
    {L sigma A x y : ℝ} (hL : 0 < L) (hs : 0 ≤ sigma) (hA : 0 ≤ A)
    (hx : A ≤ x) (hy : A ≤ y)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ sigma * A) :
    ‖ZetaRieszPrimeReplacement.logAmplitude L P N (sigma : ℂ) y -
      ZetaRieszPrimeReplacement.logAmplitude L P N (sigma : ℂ) x‖ ≤
      (sigma * amplitudeMajorant L P N sigma A) * |y - x| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_hv : v ∈ Ici A) => (hasDerivAt_logAmplitude_shape_sum L P N sigma v).hasDerivWithinAt)
    (fun v (hv : v ∈ Ici A) => norm_shape_derivative_sum_le P N hL hs hA hv hdesc)
    (convex_Ici A) hx hy

/-- The complete opposite-phase amplitude sum retains its exact cosine
and pays the descending endpoint allowance instead of a Taylor envelope. -/
theorem norm_logAmplitude_add_le_endpoint_phase (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L sigma A x y : ℝ} (hL : 0 < L) (hs : 0 ≤ sigma) (hA : 0 ≤ A)
    (hx : A ≤ x) (hy : A ≤ y)
    (hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ sigma * A) :
    ‖ZetaRieszPrimeReplacement.logAmplitude L P N (sigma + Complex.I * t) y +
      ZetaRieszPrimeReplacement.logAmplitude L P N (sigma + Complex.I * t) x‖ ≤
      amplitudeMajorant L P N sigma A *
        (sigma * |y - x| + 2 * |Real.cos (t * (y - x) / 2)|) := by
  rw [ZetaRieszReplacementPhase.logAmplitude_add_imag,
    ZetaRieszReplacementPhase.logAmplitude_add_imag]
  have he (a b u v : ℂ) : a * u + b * v = (a - b) * u + b * (u + v) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, ZetaArithmeticBandCorrelation.norm_unitPhase, mul_one,
    ZetaRieszOppositePrimes.norm_unitPhase_add_eq]
  have hang : (-t * y - -t * x) / 2 = -(t * (y - x) / 2) := by ring
  rw [hang, Real.cos_neg]
  have hdiff := norm_logAmplitude_sub_le_endpoint P N hL hs hA hx hy hdesc
  have hamp := norm_logAmplitude_le_left P N (sigma : ℂ) hL hs hA hx hdesc
  simp only [Complex.ofReal_re] at hamp
  exact (add_le_add hdiff (mul_le_mul_of_nonneg_right hamp (by positivity))).trans_eq (by ring)

/-- At the actual damped cutoff all stationary-point conditions are
eventually discharged for every coefficient of any fixed polynomial.
This is independent of a hypothetical zero and uniform in the height. -/
theorem eventually_stationary_below_length (P : Polynomial ℂ) {u : ℝ} (hu : 0 < u)
    (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ P.support,
      (N + k + 1 : ℕ) ≤ (3 / 2 : ℝ) * SquarefreeVaughanLogSource.length u N := by
  filter_upwards [ZetaRieszExtremePrimeCount.eventually_length_ge_order hu hcontact,
    eventually_ge_atTop (2 * (P.natDegree + 1))] with N hLN hN k hk
  have hkN : (k : ℝ) ≤ P.natDegree := by
    exact_mod_cast Polynomial.le_natDegree_of_mem_supp k hk
  have hNR : (2 : ℝ) * ((P.natDegree : ℝ) + 1) ≤ N := by exact_mod_cast hN
  push_cast
  nlinarith

/-- Every actual pair interval above the moving cutoff eventually has
the exact phase allowance, with all stationary-point conditions paid.
The height remains arbitrary and the endpoint stays local to the pair. -/
theorem eventually_norm_logAmplitude_pair_above_length (P : Polynomial ℂ) {u : ℝ}
    (hu : 0 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ t A x y : ℝ,
      SquarefreeVaughanLogSource.length u N ≤ A → A ≤ x → A ≤ y →
      ‖ZetaRieszPrimeReplacement.logAmplitude (SquarefreeVaughanLogSource.length u N)
          P N (3 / 2 + Complex.I * t) y +
        ZetaRieszPrimeReplacement.logAmplitude (SquarefreeVaughanLogSource.length u N)
          P N (3 / 2 + Complex.I * t) x‖ ≤
      amplitudeMajorant (SquarefreeVaughanLogSource.length u N) P N (3 / 2) A *
        ((3 / 2) * |y - x| + 2 * |Real.cos (t * (y - x) / 2)|) := by
  filter_upwards [eventually_stationary_below_length P hu hcontact] with N hN
  intro t A x y hLA hx hy
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hdesc : ∀ k ∈ P.support, (N + k + 1 : ℕ) ≤ (3 / 2 : ℝ) * A := by
    intro k hk
    exact (hN k hk).trans (mul_le_mul_of_nonneg_left hLA (by norm_num))
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    norm_logAmplitude_add_le_endpoint_phase P N t hL (by norm_num : (0 : ℝ) ≤ 3 / 2)
      (hL.le.trans hLA) hx hy hdesc

end
end RiemannGaussian.ZetaRieszDescendingAmplitude
