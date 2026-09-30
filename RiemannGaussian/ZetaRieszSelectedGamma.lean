/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SignedLaplaceMoments
import RiemannGaussian.ZetaPrimeKernelLaplace
import RiemannGaussian.ZetaRieszShiftedExterior

/-!
# Exact positive Gamma kernel of the selected shifted mode

This identity preserves the source resonance. It is an exact Laplace
formula, not a norm payment or an assertion of arithmetic cancellation.
-/

namespace RiemannGaussian.ZetaRieszSelectedGamma
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical

/-- The real Gamma density on the positive half-line. The useful orders
are positive; the zero-order convention is never used in its mass theorem. -/
def gammaKernel (u : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  u^j*t^(j-1)*Real.exp (-u*t)/((j-1).factorial : ℝ)

theorem gammaKernel_nonneg {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (j : ℕ) :
    0 ≤ gammaKernel u j t := by
  unfold gammaKernel
  positivity

theorem gammaKernel_integrable {u : ℝ} (hu : 0 < u) (j : ℕ) :
    IntegrableOn (gammaKernel u j) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := ((j-1 : ℕ) : ℝ))
    (p := 1) (by linarith [Nat.cast_nonneg (α := ℝ) (j-1)]) (by norm_num) hu
  simp only [Real.rpow_natCast,Real.rpow_one] at h
  apply ((h.const_mul (u^j)).div_const (((j-1).factorial : ℝ))).congr
  filter_upwards with t
  unfold gammaKernel
  ring

private theorem reciprocal_moment (s : ℂ) (n : ℕ) :
    signedTaylorMoment n (fun z : ℂ => z⁻¹) s = (s⁻¹)^(n+1) := by
  have ht := congrFun (iteratedDeriv_comp_const_add n (fun z : ℂ => z⁻¹) s) 0
  simp only [add_zero] at ht
  rw [signedTaylorMoment,← ht]
  have he : (fun z : ℂ => (s+z)⁻¹) = (fun z => (1*z+s)⁻¹) := by
    ext z; congr 1; ring
  rw [he]
  simpa only [signedTaylorMoment,one_pow,one_mul] using signedTaylorMoment_inv_linear n 1 s

/-- The factorial Laplace formula holds for every complex damping with
positive real part, with genuine integrability at every order. -/
theorem complex_factorial_laplace {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^n/(n.factorial : ℂ)*
      Complex.exp (-z*t)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t : ℂ)^n/(n.factorial : ℂ)*
      Complex.exp (-z*t)) = (z⁻¹)^(n+1) := by
  have h := signed_real_laplace_moments (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun _ => (1 : ℝ)) (b := 0) aemeasurable_const
    (fun x hx => by
      simpa only [one_mul,IntegrableOn] using integrableOn_exp_mul_Ioi (by linarith : -x < 0) 0) hz
  simp only [Complex.ofReal_one,one_mul] at h
  have he : (fun w : ℂ => ∫ t : ℝ in Ioi 0, Complex.exp (-w*t)) =ᶠ[nhds z]
      (fun w => w⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hz]
      with w hw
    simpa using integral_exp_mul_complex_Ioi
        (a := -w) (by simpa only [Complex.neg_re] using neg_neg_of_pos hw) 0
  have hi := ((h.2 n).1.div_const (n.factorial : ℂ))
  have hv := (h.2 n).2
  rw [signedTaylorMoment_congr n he,reciprocal_moment] at hv
  constructor
  · apply hi.congr
    filter_upwards with t
    ring
  · convert hv.symm using 1
    congr 1
    ext t
    ring

theorem gammaKernel_phase (u xi t : ℝ) (n : ℕ) :
    (gammaKernel u (n+1) t : ℂ)*Complex.exp (-(Complex.I*xi)*(t : ℂ)) =
      (u : ℂ)^(n+1)*((t : ℂ)^n/(n.factorial : ℂ)*
        Complex.exp (-((u : ℂ)+Complex.I*xi)*(t : ℂ))) := by
  simp only [gammaKernel,Nat.add_sub_cancel,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_natCast]
  rw [show -((u : ℂ)+Complex.I*xi)*(t : ℂ) =
    -(u : ℂ)*t+(-(Complex.I*xi)*(t : ℂ)) by ring,Complex.exp_add]
  ring

/-- The normalized selected denominator is exactly the Fourier transform
of a positive Gamma probability kernel. No frequency window is imposed. -/
theorem gammaKernel_fourier {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j) (xi : ℝ) :
    IntegrableOn (fun t : ℝ => (gammaKernel u j t : ℂ)*
      Complex.exp (-(Complex.I*xi)*(t : ℂ))) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*
      Complex.exp (-(Complex.I*xi)*(t : ℂ))) =
        (u : ℂ)^j*(((u : ℂ)+Complex.I*xi)⁻¹)^j := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hz : 0 < ((u : ℂ)+Complex.I*xi).re := by simpa using hu
  simp_rw [gammaKernel_phase]
  exact ⟨((complex_factorial_laplace hz n).1.const_mul _),by
    rw [integral_const_mul,(complex_factorial_laplace hz n).2]⟩

/-- Every positive order has total probability mass exactly one. -/
theorem integral_gammaKernel {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 0 < j) :
    (∫ t : ℝ in Ioi 0, gammaKernel u j t) = 1 := by
  have h := (gammaKernel_fourier hu hj 0).2
  simp only [Complex.ofReal_zero,mul_zero,neg_zero,zero_mul,Complex.exp_zero,
    mul_one,add_zero,← mul_pow] at h
  rw [mul_inv_cancel₀ (by exact_mod_cast hu.ne'),one_pow,integral_complex_ofReal] at h
  exact_mod_cast h

/-- The repository's selected shifted principal part, with its exact
marked-order divisor and residue convention. -/
theorem selected_shiftedMark_eq_laplace {u : ℝ} (hu : 0 < u)
    {j : ℕ} (hj : 0 < j) (xi : ℝ) :
    (u : ℂ)^j*ZetaRieszShiftedExterior.shiftedMark (-(u : ℂ)) j xi =
      (1/(j : ℂ))*(∫ t : ℝ in Ioi 0, (gammaKernel u j t : ℂ)*
        Complex.exp (-(Complex.I*xi)*(t : ℂ))) := by
  rw [(gammaKernel_fourier hu hj xi).2]
  unfold ZetaRieszShiftedExterior.shiftedMark
  rw [sub_neg_eq_add,add_comm (Complex.I*(xi : ℂ)) (u : ℂ)]
  ring

end
end RiemannGaussian.ZetaRieszSelectedGamma
