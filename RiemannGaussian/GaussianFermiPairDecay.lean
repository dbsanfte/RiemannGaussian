/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiDerivativeBounds

/-!
# Quantitative decay of the exact coupled Gaussian Fermi transform

Two genuine integrations by parts give inverse-square decay with an
explicit cost. The complex estimate applies to the analytic reflection.
For the physical same-phase reflected-zero pair, only its real part is
identified with that analytic reflection; no false complex norm estimate
is obtained by dropping this conjugation.
-/

namespace RiemannGaussian.GaussianFermiPairDecay

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open FermiLaplaceReflection GaussianFermiZeroPair GaussianFermiDerivativeBounds

/-- The literal oscillatory integral, using angular rather than cyclic frequency. -/
def oscillatory (f : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, (f t : ℂ) * Complex.exp (-((y : ℂ) * I) * (t : ℂ))

/-- Multiplication by the unit oscillatory phase preserves integrability. -/
theorem integrable_oscillatory {f : ℝ → ℝ} (hf : Integrable f) (y : ℝ) :
    Integrable (fun t : ℝ => (f t : ℂ) * Complex.exp (-((y : ℂ) * I) * (t : ℂ))) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => (f t : ℂ)) := hf.ofReal.aestronglyMeasurable
  apply hf.norm.mono' (hm.mul (by fun_prop))
  filter_upwards with t
  simp [Complex.norm_real, Complex.norm_exp, Complex.mul_re]

/-- The original real amplitude bounds its oscillatory integral. -/
theorem norm_oscillatory_le {f : ℝ → ℝ} (hf : Integrable f) (y : ℝ) :
    ‖oscillatory f y‖ ≤ ∫ t : ℝ, |f t| := by
  apply norm_integral_le_of_norm_le hf.abs
  filter_upwards with t
  simp [Complex.norm_real, Complex.norm_exp, Complex.mul_re]

/-- A full-line integration by parts retains the exact complex phase and
has no unstated boundary limit: integrability supplies both endpoint limits. -/
theorem oscillatory_derivative {f f' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hf : Integrable f) (hf' : Integrable f') (y : ℝ) :
    oscillatory f' y = ((y : ℂ) * I) * oscillatory f y := by
  have hi := integrable_oscillatory hf y
  have hi' := integrable_oscillatory hf' y
  have hphase (t : ℝ) : HasDerivAt
      (fun u : ℝ => Complex.exp (-((y : ℂ) * I) * (u : ℂ)))
      (Complex.exp (-((y : ℂ) * I) * (t : ℂ)) * -((y : ℂ) * I)) t := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (((hasDerivAt_id t).ofReal_comp).const_mul (-((y : ℂ) * I))).cexp
  have hdprod (t : ℝ) : HasDerivAt
      (fun u : ℝ => (f u : ℂ) * Complex.exp (-((y : ℂ) * I) * (u : ℂ)))
      ((f' t : ℂ) * Complex.exp (-((y : ℂ) * I) * (t : ℂ)) +
        -((y : ℂ) * I) * ((f t : ℂ) * Complex.exp (-((y : ℂ) * I) * (t : ℂ)))) t := by
    apply ((hd t).ofReal_comp.mul (hphase t)).congr_deriv
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hdprod
    (hi'.add (hi.const_mul (-((y : ℂ) * I)))) hi
  rw [integral_add hi' (hi.const_mul (-((y : ℂ) * I))), integral_const_mul] at hz
  change oscillatory f' y + -((y : ℂ) * I) * oscillatory f y = 0 at hz
  linear_combination hz

/-- Two integrations by parts give the exact second-order frequency identity. -/
theorem oscillatory_second_derivative {f f' f'' : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt f (f' t) t) (hd' : ∀ t, HasDerivAt f' (f'' t) t)
    (hf : Integrable f) (hf' : Integrable f') (hf'' : Integrable f'') (y : ℝ) :
    oscillatory f'' y = ((y : ℂ) * I) ^ 2 * oscillatory f y := by
  rw [oscillatory_derivative hd' hf' hf'', oscillatory_derivative hd hf hf']
  ring

/-- The exact complex analytic pair is the Fourier integral of the
retained damped amplitude, including both time directions. -/
theorem pair_eq_oscillatory {b : ℝ} (hb : 0 < b) (a : ℝ) (z : ℂ) :
    transform a (window b) z + transform a (window b) ((a : ℂ) - z) =
      oscillatory (damped a b z.re) z.im := by
  rw [gaussian_pair_eq_bilateral hb]
  unfold oscillatory
  apply integral_congr_ae
  filter_upwards with t
  rw [damped_eq_weight, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  congr 1
  conv_lhs => rw [← Complex.re_add_im z]
  push_cast
  ring

/-- The whole complex analytic pair has an explicit inverse-square bound
on the enlarged strip. The undivided statement includes zero frequency. -/
theorem im_sq_mul_norm_pair_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδb : δ ^ 2 ≤ b) {z : ℂ}
    (hz0 : -δ ≤ z.re) (hza : z.re ≤ a + δ) :
    z.im ^ 2 * ‖transform a (window b) z + transform a (window b) ((a : ℂ) - z)‖ ≤
      integralCost a b δ := by
  obtain ⟨h0, h1, h2⟩ := integrable_damped_orders ha hb hδ hδb hz0 hza
  have he := oscillatory_second_derivative (hasDerivAt_damped a b z.re)
    (hasDerivAt_dampedOne a b z.re) h0 h1 h2 z.im
  have hn := congrArg norm he
  have hn' : ‖oscillatory (dampedTwo a b z.re) z.im‖ =
      z.im ^ 2 * ‖oscillatory (damped a b z.re) z.im‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs, sq_abs] using hn
  rw [pair_eq_oscillatory hb, ← hn']
  exact (norm_oscillatory_le h2 z.im).trans (integral_abs_dampedTwo_le ha hb hδ hδb hz0 hza)

/-- The physical reflected-zero pair has the same real part as the
analytic reflection. The conjugation is retained explicitly upstream. -/
theorem physical_pair_re_eq (a b : ℝ) (z : ℂ) :
    (transform a (window b) z + transform a (window b) ((a : ℂ) - starRingEnd ℂ z)).re =
      (transform a (window b) z + transform a (window b) ((a : ℂ) - z)).re := by
  rw [transform_reflected_partner]
  simp only [Complex.add_re, Complex.conj_re]

/-- Both signs of the physical pair's real contribution are controlled
outside the positivity strip; its complex norm is not identified with the
analytic reflection's norm. -/
theorem abs_physical_pair_re_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδb : δ ^ 2 ≤ b) {z : ℂ}
    (hz0 : -δ ≤ z.re) (hza : z.re ≤ a + δ) (hy : z.im ≠ 0) :
    |(transform a (window b) z +
      transform a (window b) ((a : ℂ) - starRingEnd ℂ z)).re| ≤
      integralCost a b δ / z.im ^ 2 := by
  rw [physical_pair_re_eq]
  apply (Complex.abs_re_le_norm _).trans
  apply (le_div_iff₀ (sq_pos_of_ne_zero hy)).mpr
  simpa only [mul_comm] using im_sq_mul_norm_pair_le ha hb hδ hδb hz0 hza

end
end RiemannGaussian.GaussianFermiPairDecay
