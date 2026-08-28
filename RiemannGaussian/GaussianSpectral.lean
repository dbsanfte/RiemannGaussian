import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannGaussian.GaussianHeat

/-!
# Complex spectral Gaussians

The unconditional Weil criterion evaluates analytic test functions away from
the critical line.  Ordinary real Schwartz functions do not carry those
off-line values.  This file therefore records the entire extension of the
translated Gaussian and its exact response to a conjugate pair away from the
real spectral axis.

In the spectral coordinate `z = (ρ - 1/2) / i`, an off-critical pair has
coordinates `γ ± a i`.  Its contribution to one translated Gaussian is a
real Gaussian envelope multiplied by a cosine.  In particular, every single
off-axis conjugate pair can be made strictly negative by a suitable translate.
Controlling the simultaneous contribution of the full infinite zero divisor
is a separate, genuinely global step.
-/

namespace RiemannGaussian

noncomputable section

open Filter Topology

/-! ## The critical-line spectral coordinate -/

/-- Rotate the critical line to the real spectral axis.  This is
`(ρ - 1/2) / i`, written without division. -/
def zetaSpectralCoordinate (s : ℂ) : ℂ :=
  -Complex.I * (s - (1 / 2 : ℝ))

@[simp]
theorem zetaSpectralCoordinate_re (s : ℂ) :
    (zetaSpectralCoordinate s).re = s.im := by
  simp [zetaSpectralCoordinate, Complex.mul_re]

@[simp]
theorem zetaSpectralCoordinate_im (s : ℂ) :
    (zetaSpectralCoordinate s).im = 1 / 2 - s.re := by
  simp [zetaSpectralCoordinate, Complex.mul_im]

theorem zetaSpectralCoordinate_im_eq_zero_iff (s : ℂ) :
    (zetaSpectralCoordinate s).im = 0 ↔ s.re = 1 / 2 := by
  rw [zetaSpectralCoordinate_im]
  constructor <;> intro h <;> linarith

@[simp]
theorem zetaSpectralCoordinate_conj (s : ℂ) :
    zetaSpectralCoordinate (starRingEnd ℂ s) =
      -starRingEnd ℂ (zetaSpectralCoordinate s) := by
  apply Complex.ext <;> simp [zetaSpectralCoordinate]

@[simp]
theorem zetaSpectralCoordinate_one_sub (s : ℂ) :
    zetaSpectralCoordinate (1 - s) = -zetaSpectralCoordinate s := by
  apply Complex.ext
  · simp [zetaSpectralCoordinate]
  · simp [zetaSpectralCoordinate]
    ring

theorem zetaSpectralCoordinate_one_sub_conj (s : ℂ) :
    zetaSpectralCoordinate (1 - starRingEnd ℂ s) =
      starRingEnd ℂ (zetaSpectralCoordinate s) := by
  rw [zetaSpectralCoordinate_one_sub, zetaSpectralCoordinate_conj]
  simp

/-- Mathlib's `RiemannHypothesis` is exactly the assertion that every
nontrivial zeta zero has real spectral coordinate. -/
theorem riemannHypothesis_iff_spectralCoordinate_real :
    RiemannHypothesis ↔
      ∀ (s : ℂ), riemannZeta s = 0 →
        (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
          (zetaSpectralCoordinate s).im = 0 := by
  unfold RiemannHypothesis
  constructor
  · intro h s hs hnontrivial hone
    exact (zetaSpectralCoordinate_im_eq_zero_iff s).2
      (h s hs hnontrivial hone)
  · intro h s hs hnontrivial hone
    exact (zetaSpectralCoordinate_im_eq_zero_iff s).1
      (h s hs hnontrivial hone)

/-- Entire extension of `translatedGaussian` to the complex spectral
coordinate. -/
def complexTranslatedGaussian (ε t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((ε : ℂ) * (z - (t : ℂ)) ^ 2))

/-- Entire extension of the even translated Gaussian used by the arithmetic
certificates. -/
def complexSymmetricGaussian (ε t : ℝ) (z : ℂ) : ℂ :=
  complexTranslatedGaussian ε t z + complexTranslatedGaussian ε (-t) z

/-- Half of the exponent in `complexTranslatedGaussian`.  On the real axis,
the full Gaussian is its pointwise squared modulus; this is the elementary
factorization behind its role as a Weil convolution square. -/
def complexHalfGaussian (ε t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(((ε / 2 : ℝ) : ℂ) * (z - (t : ℂ)) ^ 2))

theorem complexTranslatedGaussian_eq_half_mul_half (ε t : ℝ) (z : ℂ) :
    complexTranslatedGaussian ε t z =
      complexHalfGaussian ε t z * complexHalfGaussian ε t z := by
  rw [complexTranslatedGaussian, complexHalfGaussian, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Product of two half-Gaussian factors.  Thus the off-diagonal entry for
centers `t` and `s` is a positive real factor times a translated Gaussian at
their midpoint. -/
theorem complexHalfGaussian_mul_complexHalfGaussian
    (ε t s : ℝ) (z : ℂ) :
    complexHalfGaussian ε t z * complexHalfGaussian ε s z =
      (Real.exp (-ε * (t - s) ^ 2 / 4) : ℂ) *
        complexTranslatedGaussian ε ((t + s) / 2) z := by
  rw [complexHalfGaussian, complexHalfGaussian, complexTranslatedGaussian,
    ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
theorem complexHalfGaussian_ofReal (ε t r : ℝ) :
    complexHalfGaussian ε t (r : ℂ) =
      (Real.exp (-(ε / 2) * (r - t) ^ 2) : ℝ) := by
  rw [complexHalfGaussian, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

@[simp]
theorem complexTranslatedGaussian_ofReal (ε t r : ℝ) :
    complexTranslatedGaussian ε t (r : ℂ) = translatedGaussian ε t r := by
  rw [complexTranslatedGaussian, translatedGaussian, Complex.ofReal_exp]
  push_cast
  congr 1
  ring

@[simp]
theorem complexSymmetricGaussian_ofReal (ε t r : ℝ) :
    complexSymmetricGaussian ε t (r : ℂ) = symmetricGaussian ε t r := by
  have hreflect :
      translatedGaussian ε (-t) r = translatedGaussian ε t (-r) := by
    unfold translatedGaussian
    congr 1
    ring
  rw [complexSymmetricGaussian, complexTranslatedGaussian_ofReal,
    complexTranslatedGaussian_ofReal, symmetricGaussian, hreflect]
  push_cast
  rfl

@[simp]
theorem complexSymmetricGaussian_neg_center (ε t : ℝ) (z : ℂ) :
    complexSymmetricGaussian ε (-t) z = complexSymmetricGaussian ε t z := by
  simp [complexSymmetricGaussian, add_comm]

@[simp]
theorem complexHalfGaussian_conj (ε t : ℝ) (z : ℂ) :
    starRingEnd ℂ (complexHalfGaussian ε t z) =
      complexHalfGaussian ε t (starRingEnd ℂ z) := by
  unfold complexHalfGaussian
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_neg, map_mul, map_sub, map_pow, Complex.conj_ofReal]

/-- On the real spectral axis, the translated Gaussian is exactly the norm
square of its analytic half-Gaussian factor. -/
theorem complexTranslatedGaussian_ofReal_eq_normSq_half
    (ε t r : ℝ) :
    translatedGaussian ε t r = Complex.normSq (complexHalfGaussian ε t r) := by
  rw [← Complex.ofReal_inj, Complex.normSq_eq_conj_mul_self,
    ← complexTranslatedGaussian_ofReal,
    complexTranslatedGaussian_eq_half_mul_half]
  congr 1
  rw [complexHalfGaussian_conj]
  simp

@[simp]
theorem complexTranslatedGaussian_conj (ε t : ℝ) (z : ℂ) :
    starRingEnd ℂ (complexTranslatedGaussian ε t z) =
      complexTranslatedGaussian ε t (starRingEnd ℂ z) := by
  unfold complexTranslatedGaussian
  rw [← Complex.exp_conj]
  apply congrArg Complex.exp
  simp

/-- Reflecting the center is equivalent to reflecting the spectral point. -/
theorem complexTranslatedGaussian_neg_center (ε t : ℝ) (z : ℂ) :
    complexTranslatedGaussian ε (-t) z =
      complexTranslatedGaussian ε t (-z) := by
  unfold complexTranslatedGaussian
  congr 1
  push_cast
  ring

/-- The absolute size of an entire translated Gaussian is its real Gaussian
envelope, amplified by the squared distance from the real spectral axis. -/
theorem norm_complexTranslatedGaussian (ε t : ℝ) (z : ℂ) :
    ‖complexTranslatedGaussian ε t z‖ =
      Real.exp (ε * z.im ^ 2 - ε * (z.re - t) ^ 2) := by
  rw [complexTranslatedGaussian, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, sub_zero,
    pow_two]
  ring

/-- Exact contribution of the off-axis conjugate pair `γ ± a i`.

The right side is real.  The factor `exp (ε a²)` is the off-critical
amplification; the cosine is the sign-changing phase that a global Gaussian
criterion must control. -/
theorem complexTranslatedGaussian_conjugate_pair
    (ε t γ a : ℝ) :
    complexTranslatedGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexTranslatedGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I) =
      (2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
        Real.cos (2 * ε * a * (γ - t)) : ℝ) := by
  have hzre :
      (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)).re = γ - t := by
    simp
  have hzim :
      (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)).im = a := by
    simp
  let w : ℂ := -((ε : ℂ) *
    (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)) ^ 2)
  have hre : w.re = ε * a ^ 2 - ε * (γ - t) ^ 2 := by
    simp only [w, Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, mul_one, zero_sub, pow_two]
    rw [hzim]
    ring
  have him : w.im = -(2 * ε * a * (γ - t)) := by
    simp only [w, Complex.neg_im, Complex.mul_im, Complex.sub_im, Complex.add_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, mul_one, add_zero, zero_add, pow_two]
    rw [hzre]
    ring
  have hconj :
      complexTranslatedGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I) =
        starRingEnd ℂ
          (complexTranslatedGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I)) := by
    simp [sub_eq_add_neg]
  rw [hconj, Complex.add_conj]
  norm_cast
  change 2 * (Complex.exp w).re =
    2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
      Real.cos (2 * ε * a * (γ - t))
  rw [Complex.exp_re, hre, him, Real.cos_neg]
  ring

/-- The real contribution of one conjugate off-axis packet. -/
def offAxisPacketContribution (ε t γ a : ℝ) : ℝ :=
  2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
    Real.cos (2 * ε * a * (γ - t))

/-- Real part contributed by one spectral point `γ + a i`.  A conjugate
packet consists of two equal such real parts. -/
def offAxisSingleContribution (ε t γ a : ℝ) : ℝ :=
  Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
    Real.cos (2 * ε * a * (γ - t))

theorem offAxisPacketContribution_eq_two_mul_single
    (ε t γ a : ℝ) :
    offAxisPacketContribution ε t γ a =
      2 * offAxisSingleContribution ε t γ a := by
  unfold offAxisPacketContribution offAxisSingleContribution
  ring

/-- The single-point formula is the real part of the entire Gaussian. -/
theorem complexTranslatedGaussian_re_eq_offAxisSingleContribution
    (ε t γ a : ℝ) :
    (complexTranslatedGaussian ε t
      ((γ : ℂ) + (a : ℂ) * Complex.I)).re =
        offAxisSingleContribution ε t γ a := by
  have hzre :
      (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)).re = γ - t := by
    simp
  have hzim :
      (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)).im = a := by
    simp
  let w : ℂ := -((ε : ℂ) *
    (((γ : ℂ) + (a : ℂ) * Complex.I) - (t : ℂ)) ^ 2)
  have hre : w.re = ε * a ^ 2 - ε * (γ - t) ^ 2 := by
    simp only [w, Complex.neg_re, Complex.mul_re, Complex.sub_re,
      Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, zero_sub, pow_two]
    rw [hzim]
    ring
  have him : w.im = -(2 * ε * a * (γ - t)) := by
    simp only [w, Complex.neg_im, Complex.mul_im, Complex.sub_im,
      Complex.add_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, mul_one, add_zero, zero_add, pow_two]
    rw [hzre]
    ring
  change (Complex.exp w).re = offAxisSingleContribution ε t γ a
  rw [Complex.exp_re, hre, him, Real.cos_neg]
  rfl

/-- A single real contribution is bounded above by its Gaussian envelope. -/
theorem offAxisSingleContribution_le_envelope (ε t γ a : ℝ) :
    offAxisSingleContribution ε t γ a ≤
      Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by
  unfold offAxisSingleContribution
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left (Real.cos_le_one _)
      (Real.exp_pos _).le)

/-- Absolute-value envelope bound for one spectral point. -/
theorem abs_offAxisSingleContribution_le_envelope (ε t γ a : ℝ) :
    |offAxisSingleContribution ε t γ a| ≤
      Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by
  unfold offAxisSingleContribution
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
    (Real.exp_pos _).le

@[simp]
theorem offAxisSingleContribution_neg_height (ε t γ a : ℝ) :
    offAxisSingleContribution ε t γ (-a) =
      offAxisSingleContribution ε t γ a := by
  unfold offAxisSingleContribution
  rw [neg_sq]
  rw [show 2 * ε * -a * (γ - t) =
    -(2 * ε * a * (γ - t)) by ring, Real.cos_neg]

/-- Real contribution of one conjugate off-axis packet to the symmetric
Gaussian used by the arithmetic certificates. -/
def offAxisSymmetricPacketContribution (ε t γ a : ℝ) : ℝ :=
  offAxisPacketContribution ε t γ a +
    offAxisPacketContribution ε (-t) γ a

/-- Reflecting the Gaussian center is the same as reflecting the packet
ordinate. -/
theorem offAxisPacketContribution_neg_center (ε t γ a : ℝ) :
    offAxisPacketContribution ε (-t) γ a =
      offAxisPacketContribution ε t (-γ) a := by
  unfold offAxisPacketContribution
  rw [show 2 * ε * a * (γ - -t) =
      -(2 * ε * a * (-γ - t)) by ring, Real.cos_neg]
  rw [show ε * a ^ 2 - ε * (γ - -t) ^ 2 =
      ε * a ^ 2 - ε * (-γ - t) ^ 2 by ring]

/-- Exact conjugate-pair formula for the symmetric certified test family. -/
theorem complexSymmetricGaussian_conjugate_pair_eq_packetContribution
    (ε t γ a : ℝ) :
    complexSymmetricGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexSymmetricGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I) =
      (offAxisSymmetricPacketContribution ε t γ a : ℝ) := by
  calc
    complexSymmetricGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexSymmetricGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I) =
      (complexTranslatedGaussian ε t
          ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexTranslatedGaussian ε t
          ((γ : ℂ) - (a : ℂ) * Complex.I)) +
      (complexTranslatedGaussian ε (-t)
          ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexTranslatedGaussian ε (-t)
          ((γ : ℂ) - (a : ℂ) * Complex.I)) := by
      unfold complexSymmetricGaussian
      ring
    _ = (offAxisSymmetricPacketContribution ε t γ a : ℝ) := by
      rw [complexTranslatedGaussian_conjugate_pair,
        complexTranslatedGaussian_conjugate_pair]
      unfold offAxisSymmetricPacketContribution offAxisPacketContribution
      push_cast
      rfl

theorem complexTranslatedGaussian_conjugate_pair_eq_packetContribution
    (ε t γ a : ℝ) :
    complexTranslatedGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexTranslatedGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I) =
      (offAxisPacketContribution ε t γ a : ℝ) := by
  exact complexTranslatedGaussian_conjugate_pair ε t γ a

/-- A packet is bounded above by its positive Gaussian envelope. -/
theorem offAxisPacketContribution_le_envelope (ε t γ a : ℝ) :
    offAxisPacketContribution ε t γ a ≤
      2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by
  unfold offAxisPacketContribution
  have hnonneg :
      0 ≤ 2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by positivity
  calc
    2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
          Real.cos (2 * ε * a * (γ - t))
        ≤ (2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.cos_le_one _) hnonneg
    _ = 2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by ring

/-- Absolute-value version of the packet envelope bound. -/
theorem abs_offAxisPacketContribution_le_envelope (ε t γ a : ℝ) :
    |offAxisPacketContribution ε t γ a| ≤
      2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by
  unfold offAxisPacketContribution
  have hnonneg :
      0 ≤ 2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by positivity
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc
    2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) *
          |Real.cos (2 * ε * a * (γ - t))| ≤
        (2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hnonneg
    _ = 2 * Real.exp (ε * a ^ 2 - ε * (γ - t) ^ 2) := by ring

/-- A translate which puts the off-axis pair exactly at cosine phase `π`. -/
def offAxisDetectionCenter (ε γ a : ℝ) : ℝ :=
  γ - Real.pi / (2 * ε * a)

/-- The exponent gap between a target off-axis packet `(γ, a)` and another
packet `(η, b)` when the target is evaluated at its detection center.  A
positive gap means that the other packet's Gaussian envelope is
exponentially smaller as `ε → ∞`. -/
def offAxisPacketGap (γ a η b : ℝ) : ℝ :=
  a ^ 2 - b ^ 2 + (η - γ) ^ 2

/-- A packet of no greater off-axis height has positive gap unless it has
both the same ordinate and the same squared height as the target. -/
theorem offAxisPacketGap_pos_of_sq_le_of_not_duplicate
    (γ a η b : ℝ) (hheight : b ^ 2 ≤ a ^ 2)
    (hdistinct : b ^ 2 < a ^ 2 ∨ η ≠ γ) :
    0 < offAxisPacketGap γ a η b := by
  unfold offAxisPacketGap
  rcases hdistinct with hstrict | hcenter
  · nlinarith [sq_nonneg (η - γ)]
  · have hsq : 0 < (η - γ) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hcenter)
    nlinarith

theorem offAxisDetectionCenter_phase
    (ε γ a : ℝ) (hε : ε ≠ 0) (ha : a ≠ 0) :
    2 * ε * a * (γ - offAxisDetectionCenter ε γ a) = Real.pi := by
  unfold offAxisDetectionCenter
  have hdenom : 2 * ε * a ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hε) ha
  field_simp
  ring

/-- Exact relative exponent of another off-axis packet at the target
detection center.  Besides the exponentially scaled packet gap, only a
constant displacement factor remains. -/
theorem offAxisDetectionCenter_exponent_difference
    (ε γ a η b : ℝ) (hε : ε ≠ 0) (ha : a ≠ 0) :
    (ε * b ^ 2 - ε * (η - offAxisDetectionCenter ε γ a) ^ 2) -
        (ε * a ^ 2 - ε * (γ - offAxisDetectionCenter ε γ a) ^ 2) =
      -ε * offAxisPacketGap γ a η b -
        (Real.pi / a) * (η - γ) := by
  unfold offAxisDetectionCenter offAxisPacketGap
  field_simp [hε, ha]
  ring

/-- Under a positive packet gap, the competing exponent minus the target
exponent tends to `-∞`. -/
theorem tendsto_offAxis_exponentDifference_atBot
    (γ a η b : ℝ) (ha : a ≠ 0)
    (hgap : 0 < offAxisPacketGap γ a η b) :
    Tendsto
      (fun ε : ℝ =>
        (ε * b ^ 2 - ε * (η - offAxisDetectionCenter ε γ a) ^ 2) -
          (ε * a ^ 2 - ε * (γ - offAxisDetectionCenter ε γ a) ^ 2))
      atTop atBot := by
  have hlinear :
      Tendsto
        (fun ε : ℝ =>
          -ε * offAxisPacketGap γ a η b -
            (Real.pi / a) * (η - γ))
        atTop atBot := by
    have hmul :
        Tendsto
          (fun ε : ℝ => -ε * offAxisPacketGap γ a η b)
          atTop atBot :=
      by
        simpa [id_eq, mul_comm] using
          (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap))
    have hadd := tendsto_atBot_add_const_right atTop
      (-((Real.pi / a) * (η - γ))) hmul
    simpa only [sub_eq_add_neg] using hadd
  refine hlinear.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ε hε
  rw [offAxisDetectionCenter_exponent_difference ε γ a η b hε.ne' ha]

/-- If the packet gap is positive, the other packet's Gaussian envelope,
relative to the selected target packet at the target's detection center,
tends to zero as the Gaussian narrows (`ε → ∞`). -/
theorem tendsto_offAxis_relativeEnvelope
    (γ a η b : ℝ) (ha : a ≠ 0)
    (hgap : 0 < offAxisPacketGap γ a η b) :
    Tendsto
      (fun ε : ℝ => Real.exp
        ((ε * b ^ 2 - ε * (η - offAxisDetectionCenter ε γ a) ^ 2) -
          (ε * a ^ 2 - ε * (γ - offAxisDetectionCenter ε γ a) ^ 2)))
      atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp
    (tendsto_offAxis_exponentDifference_atBot γ a η b ha hgap)).congr' ?_
  exact Eventually.of_forall fun _ => rfl

/-- Exact negative value of an isolated off-axis conjugate pair at its
detection center. -/
theorem complexTranslatedGaussian_conjugate_pair_at_detectionCenter
    (ε γ a : ℝ) (hε : ε ≠ 0) (ha : a ≠ 0) :
    complexTranslatedGaussian ε (offAxisDetectionCenter ε γ a)
        ((γ : ℂ) + (a : ℂ) * Complex.I) +
      complexTranslatedGaussian ε (offAxisDetectionCenter ε γ a)
        ((γ : ℂ) - (a : ℂ) * Complex.I) =
      (-2 * Real.exp (ε * a ^ 2 -
        ε * (γ - offAxisDetectionCenter ε γ a) ^ 2) : ℝ) := by
  rw [complexTranslatedGaussian_conjugate_pair,
    offAxisDetectionCenter_phase ε γ a hε ha, Real.cos_pi]
  push_cast
  ring

/-- Real form of the target packet's exact negative value. -/
theorem offAxisPacketContribution_at_detectionCenter
    (ε γ a : ℝ) (hε : ε ≠ 0) (ha : a ≠ 0) :
    offAxisPacketContribution ε (offAxisDetectionCenter ε γ a) γ a =
      -2 * Real.exp (ε * a ^ 2 -
        ε * (γ - offAxisDetectionCenter ε γ a) ^ 2) := by
  unfold offAxisPacketContribution
  rw [offAxisDetectionCenter_phase ε γ a hε ha, Real.cos_pi]
  ring

/-- With a positive gap, a selected off-axis packet eventually dominates
one competing packet at its explicit detection center. -/
theorem eventually_offAxisPacketContribution_add_negative
    (γ a η b : ℝ) (ha : a ≠ 0)
    (hgap : 0 < offAxisPacketGap γ a η b) :
    ∀ᶠ ε : ℝ in atTop,
      0 < ε ∧
        offAxisPacketContribution ε (offAxisDetectionCenter ε γ a) γ a +
          offAxisPacketContribution ε (offAxisDetectionCenter ε γ a) η b < 0 := by
  have hdiff :=
    (tendsto_offAxis_exponentDifference_atBot γ a η b ha hgap).eventually_lt_atBot 0
  filter_upwards [eventually_gt_atTop (0 : ℝ), hdiff] with ε hε hdiffε
  refine ⟨hε, ?_⟩
  let t := offAxisDetectionCenter ε γ a
  let targetExponent := ε * a ^ 2 - ε * (γ - t) ^ 2
  let otherExponent := ε * b ^ 2 - ε * (η - t) ^ 2
  have hexp : Real.exp otherExponent < Real.exp targetExponent := by
    rw [Real.exp_lt_exp]
    exact sub_neg.mp hdiffε
  have hother :
      offAxisPacketContribution ε t η b ≤ 2 * Real.exp otherExponent := by
    exact offAxisPacketContribution_le_envelope ε t η b
  have htarget :
      offAxisPacketContribution ε t γ a = -2 * Real.exp targetExponent := by
    exact offAxisPacketContribution_at_detectionCenter ε γ a hε.ne' ha
  change offAxisPacketContribution ε t γ a +
    offAxisPacketContribution ε t η b < 0
  rw [htarget]
  linarith

/-- The even Gaussian family used by the certificates still detects every
isolated off-axis conjugate packet.  If the packet ordinate is nonzero, the
reflected-center term is exponentially negligible; at ordinate zero it is a
second copy of the same negative detector. -/
theorem eventually_offAxisSymmetricPacketContribution_negative
    (γ a : ℝ) (ha : a ≠ 0) :
    ∀ᶠ ε : ℝ in atTop,
      0 < ε ∧
        offAxisSymmetricPacketContribution ε
          (offAxisDetectionCenter ε γ a) γ a < 0 := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ε hε
    refine ⟨hε, ?_⟩
    unfold offAxisSymmetricPacketContribution
    rw [offAxisPacketContribution_neg_center]
    simp only [neg_zero]
    rw [offAxisPacketContribution_at_detectionCenter ε 0 a hε.ne' ha]
    nlinarith [Real.exp_pos (ε * a ^ 2 -
      ε * (0 - offAxisDetectionCenter ε 0 a) ^ 2)]
  · have hgap : 0 < offAxisPacketGap γ a (-γ) a := by
      unfold offAxisPacketGap
      nlinarith [sq_pos_of_ne_zero hγ]
    filter_upwards [eventually_offAxisPacketContribution_add_negative
      γ a (-γ) a ha hgap] with ε hε
    refine ⟨hε.1, ?_⟩
    unfold offAxisSymmetricPacketContribution
    rw [offAxisPacketContribution_neg_center]
    exact hε.2

/-- Finite-divisor separation.  If one selected off-axis packet has positive
gap against every packet in a finite competing family, then sufficiently
narrow translated Gaussians make the selected packet plus the entire family
strictly negative.

This theorem isolates why the unresolved zeta step is genuinely about the
infinite divisor and its uniform tails: no finite masking phenomenon is
possible under the stated geometric gap. -/
theorem eventually_offAxisPacketContribution_add_finiteFamily_negative
    {ι : Type*} [Fintype ι]
    (γ a : ℝ) (η b : ι → ℝ) (ha : a ≠ 0)
    (hgap : ∀ i, 0 < offAxisPacketGap γ a (η i) (b i)) :
    ∀ᶠ ε : ℝ in atTop,
      0 < ε ∧
        offAxisPacketContribution ε (offAxisDetectionCenter ε γ a) γ a +
          ∑ i, offAxisPacketContribution ε
            (offAxisDetectionCenter ε γ a) (η i) (b i) < 0 := by
  have hrelative :
      Tendsto
        (fun ε : ℝ =>
          ∑ i, Real.exp
            ((ε * (b i) ^ 2 - ε * (η i - offAxisDetectionCenter ε γ a) ^ 2) -
              (ε * a ^ 2 - ε * (γ - offAxisDetectionCenter ε γ a) ^ 2)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_finsetSum Finset.univ fun i _ =>
        tendsto_offAxis_relativeEnvelope γ a (η i) (b i) ha (hgap i))
  have hsmall := hrelative.eventually_lt_const zero_lt_one
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with ε hε hsmallε
  refine ⟨hε, ?_⟩
  let t := offAxisDetectionCenter ε γ a
  let targetExponent := ε * a ^ 2 - ε * (γ - t) ^ 2
  let otherExponent : ι → ℝ := fun i =>
    ε * (b i) ^ 2 - ε * (η i - t) ^ 2
  let relativeEnvelope : ι → ℝ := fun i =>
    Real.exp (otherExponent i - targetExponent)
  have hother :
      ∑ i, offAxisPacketContribution ε t (η i) (b i) ≤
        ∑ i, 2 * Real.exp (otherExponent i) := by
    exact Finset.sum_le_sum fun i _ =>
      offAxisPacketContribution_le_envelope ε t (η i) (b i)
  have henvelope (i : ι) :
      2 * Real.exp (otherExponent i) =
        (2 * Real.exp targetExponent) * relativeEnvelope i := by
    unfold relativeEnvelope
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have henvelopeSum :
      ∑ i, 2 * Real.exp (otherExponent i) =
        (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i := by
    calc
      ∑ i, 2 * Real.exp (otherExponent i) =
          ∑ i, (2 * Real.exp targetExponent) * relativeEnvelope i := by
        exact Finset.sum_congr rfl fun i _ => henvelope i
      _ = (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i := by
        rw [Finset.mul_sum]
  have hsmall' : ∑ i, relativeEnvelope i < 1 := by
    exact hsmallε
  have hfamily :
      ∑ i, offAxisPacketContribution ε t (η i) (b i) <
        2 * Real.exp targetExponent := by
    calc
      ∑ i, offAxisPacketContribution ε t (η i) (b i) ≤
          ∑ i, 2 * Real.exp (otherExponent i) := hother
      _ = (2 * Real.exp targetExponent) * ∑ i, relativeEnvelope i :=
        henvelopeSum
      _ < (2 * Real.exp targetExponent) * 1 :=
        mul_lt_mul_of_pos_left hsmall' (by positivity)
      _ = 2 * Real.exp targetExponent := by ring
  have htarget :
      offAxisPacketContribution ε t γ a = -2 * Real.exp targetExponent := by
    exact offAxisPacketContribution_at_detectionCenter ε γ a hε.ne' ha
  change offAxisPacketContribution ε t γ a +
    ∑ i, offAxisPacketContribution ε t (η i) (b i) < 0
  rw [htarget]
  linarith

/-- Geometric specialization of finite-divisor separation: it is enough for
the target to have maximal squared off-axis height, after exact duplicate
packets have been grouped together. -/
theorem eventually_maximalOffAxisPacket_add_finiteFamily_negative
    {ι : Type*} [Fintype ι]
    (γ a : ℝ) (η b : ι → ℝ) (ha : a ≠ 0)
    (hheight : ∀ i, (b i) ^ 2 ≤ a ^ 2)
    (hnoduplicate : ∀ i, (b i) ^ 2 < a ^ 2 ∨ η i ≠ γ) :
    ∀ᶠ ε : ℝ in atTop,
      0 < ε ∧
        offAxisPacketContribution ε (offAxisDetectionCenter ε γ a) γ a +
          ∑ i, offAxisPacketContribution ε
            (offAxisDetectionCenter ε γ a) (η i) (b i) < 0 := by
  exact eventually_offAxisPacketContribution_add_finiteFamily_negative
    γ a η b ha fun i =>
      offAxisPacketGap_pos_of_sq_le_of_not_duplicate
        γ a (η i) (b i) (hheight i) (hnoduplicate i)

/-- The exact remaining obligation for a global zero-divisor argument: if
the real contribution of every other zero is smaller than the detected
pair's magnitude, the complete value is negative. -/
theorem complexTranslatedGaussian_pair_add_remainder_negative
    (ε γ a remainder : ℝ) (hε : ε ≠ 0) (ha : a ≠ 0)
    (hrem : remainder < 2 * Real.exp (ε * a ^ 2 -
      ε * (γ - offAxisDetectionCenter ε γ a) ^ 2)) :
    (complexTranslatedGaussian ε (offAxisDetectionCenter ε γ a)
        ((γ : ℂ) + (a : ℂ) * Complex.I) +
      complexTranslatedGaussian ε (offAxisDetectionCenter ε γ a)
        ((γ : ℂ) - (a : ℂ) * Complex.I)).re + remainder < 0 := by
  rw [complexTranslatedGaussian_conjugate_pair_at_detectionCenter ε γ a hε ha]
  simp only [Complex.ofReal_re]
  linarith

/-- A single non-real conjugate pair is detected by a translated Gaussian:
at an explicit center its combined contribution is strictly negative.

This is a local detector theorem, not yet a theorem about the sum over every
zeta zero. -/
theorem exists_complexTranslatedGaussian_conjugate_pair_negative
    (ε γ a : ℝ) (hε : 0 < ε) (ha : a ≠ 0) :
    ∃ t : ℝ,
      (complexTranslatedGaussian ε t ((γ : ℂ) + (a : ℂ) * Complex.I) +
        complexTranslatedGaussian ε t ((γ : ℂ) - (a : ℂ) * Complex.I)).re < 0 := by
  refine ⟨offAxisDetectionCenter ε γ a, ?_⟩
  rw [complexTranslatedGaussian_conjugate_pair_at_detectionCenter ε γ a hε.ne' ha]
  simp only [Complex.ofReal_re]
  nlinarith [Real.exp_pos (ε * a ^ 2 -
    ε * (γ - offAxisDetectionCenter ε γ a) ^ 2)]

end

end RiemannGaussian
