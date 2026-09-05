import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Zeta23.ExplicitFormula

/-!
# Phase twists compatible with the Zeta23 zero side

The zero-side conjugation law does not require a real-even window.  It is
enough that the logarithmic window obey the Hermitian symmetry
`g(-u) = conj (g u)`.  This permits nontrivial unit phases while keeping the
Fourier samples real on the real axis and preserving their squared mass.
-/

namespace RiemannGaussian

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

/-- Hermitian symmetry in logarithmic time. -/
def IsHermitianWindow (g : ℝ → ℂ) : Prop :=
  ∀ u, g (-u) = conj (g u)

lemma ef_tilde_eq_self_of_isHermitianWindow {g : ℝ → ℂ}
    (hg : IsHermitianWindow g) : Zeta23.EF.tilde g = g := by
  funext u
  simp only [Zeta23.EF.tilde]
  rw [hg]
  simp

/-- A Hermitian logarithmic window has exactly the conjugation law consumed
by the Zeta23 reflection block. -/
theorem paperFT_conj_of_isHermitianWindow {g : ℝ → ℂ}
    (hg : IsHermitianWindow g) (z : ℂ) :
    Zeta23.paperFT g (conj z) = conj (Zeta23.paperFT g z) := by
  have ht := Zeta23.EF.paperFT_tilde g (conj z)
  rw [ef_tilde_eq_self_of_isHermitianWindow hg] at ht
  simpa using ht

/-- In particular, every real-axis Fourier sample is real. -/
theorem paperFT_ofReal_of_isHermitianWindow {g : ℝ → ℂ}
    (hg : IsHermitianWindow g) (r : ℝ) :
    Zeta23.paperFT g r = ((Zeta23.paperFT g r).re : ℂ) := by
  have hconj := paperFT_conj_of_isHermitianWindow hg (r : ℂ)
  rw [Complex.conj_ofReal] at hconj
  have him : (Zeta23.paperFT g r).im = 0 :=
    Complex.conj_eq_iff_im.mp hconj.symm
  apply Complex.ext
  · simp
  · simp [him]

/-- Multiply a real base window by a complex phase. -/
def phaseTwist (φ : ℝ → ℝ) (c : ℝ → ℂ) (u : ℝ) : ℂ :=
  (φ u : ℂ) * c u

lemma phaseTwist_isHermitianWindow {φ : ℝ → ℝ} {c : ℝ → ℂ}
    (hφ : ∀ u, φ (-u) = φ u) (hc : IsHermitianWindow c) :
    IsHermitianWindow (phaseTwist φ c) := by
  intro u
  unfold phaseTwist
  rw [hφ, hc]
  simp

/-- A unit phase leaves the pointwise quadratic mass of the real base window
unchanged. -/
lemma normSq_phaseTwist {φ : ℝ → ℝ} {c : ℝ → ℂ}
    (hc : ∀ u, ‖c u‖ = 1) (u : ℝ) :
    ‖phaseTwist φ c u‖ ^ 2 = φ u ^ 2 := by
  rw [phaseTwist, norm_mul, hc, mul_one, norm_real, Real.norm_eq_abs, sq_abs]

theorem integral_normSq_phaseTwist {φ : ℝ → ℝ} {c : ℝ → ℂ}
    (hc : ∀ u, ‖c u‖ = 1) :
    (∫ u : ℝ, ‖phaseTwist φ c u‖ ^ 2) = ∫ u : ℝ, φ u ^ 2 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (normSq_phaseTwist hc)

/-- A scalar Hermitian unit phase cancels in the reflected product used by
the Gabor--Poisson contraction.  Thus scalar window chirping alone cannot
alter the main Zeta23 trace moments; a successful colour must survive as a
relative (multi-channel or arithmetic) phase. -/
lemma phaseTwist_mul_reflection_eq_sq {φ : ℝ → ℝ} {c : ℝ → ℂ}
    (hφ : ∀ u, φ (-u) = φ u) (hcHerm : IsHermitianWindow c)
    (hcNorm : ∀ u, ‖c u‖ = 1) (u : ℝ) :
    phaseTwist φ c u * phaseTwist φ c (-u) = ((φ u ^ 2 : ℝ) : ℂ) := by
  rw [phaseTwist, phaseTwist, hφ, hcHerm]
  have hunit : c u * conj (c u) = 1 := by
    rw [mul_conj]
    rw [Complex.normSq_eq_norm_sq, hcNorm]
    norm_num
  rw [show (φ u : ℂ) * c u * ((φ u : ℂ) * conj (c u)) =
      ((φ u : ℂ) * (φ u : ℂ)) * (c u * conj (c u)) by ring,
    hunit, mul_one]
  push_cast
  ring

/-- An explicit smooth, non-affine Hermitian phase.  Its cubic curvature is
the simplest scalar carrier capable of producing nontrivial four-cycle
holonomy. -/
def cubicPhase (α u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((α * u ^ 3 : ℝ) : ℂ))

lemma cubicPhase_norm (α u : ℝ) : ‖cubicPhase α u‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal (α * u ^ 3)

lemma cubicPhase_isHermitianWindow (α : ℝ) :
    IsHermitianWindow (cubicPhase α) := by
  intro u
  unfold cubicPhase
  have he : Complex.I * ((α * (-u) ^ 3 : ℝ) : ℂ) =
      conj (Complex.I * ((α * u ^ 3 : ℝ) : ℂ)) := by
    rw [map_mul, conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [he, Complex.exp_conj]

lemma cubicPhase_contDiff (α : ℝ) : ContDiff ℝ ⊤ (cubicPhase α) := by
  unfold cubicPhase
  apply Complex.contDiff_exp.comp
  apply ContDiff.mul contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.pow 3))

/-- Two different cubic channels retain exactly their relative phase under
reflection.  The same-channel case is the gauge cancellation above. -/
lemma cubicPhase_mul_reflection (α β u : ℝ) :
    cubicPhase α u * cubicPhase β (-u) = cubicPhase (α - β) u := by
  unfold cubicPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Cubic phase defect around an oriented four-cycle. -/
def cubicHolonomy (a b c d : ℝ) : ℝ :=
  a ^ 3 + b ^ 3 - c ^ 3 - d ^ 3

/-- The oriented cubic colour carried by a quartic term.  The two conjugated
coordinates are the negative orientation of the four-cycle. -/
def quarticCubicPhase (α a b c d : ℝ) : ℂ :=
  cubicPhase α a * cubicPhase α b *
    conj (cubicPhase α c) * conj (cubicPhase α d)

/-- A quartic cubic colour is exactly the exponential of its holonomy.  This
is the bridge that lets phase-parameter averaging act directly on each
four-prime term. -/
theorem quarticCubicPhase_eq_exp_holonomy (α a b c d : ℝ) :
    quarticCubicPhase α a b c d =
      Complex.exp (Complex.I * ((α * cubicHolonomy a b c d : ℝ) : ℂ)) := by
  unfold quarticCubicPhase cubicPhase cubicHolonomy
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_mul, conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On the product-lock hyperplane (additive after taking logarithms), cubic
holonomy factorizes into the two pairing gaps. -/
theorem cubicHolonomy_factor_of_add_eq {a b c d : ℝ}
    (hsum : a + b = c + d) :
    cubicHolonomy a b c d = 3 * (a + b) * (a - c) * (a - d) := by
  have hd : d = a + b - c := by linarith
  rw [hd]
  unfold cubicHolonomy
  ring

/-- Consequently a positive-sum locked cycle has zero cubic holonomy exactly
at the two Wick pairings. -/
theorem cubicHolonomy_ne_zero_of_add_eq_of_not_pairing {a b c d : ℝ}
    (hsum : a + b = c + d) (hpos : 0 < a + b)
    (hac : a ≠ c) (had : a ≠ d) :
    cubicHolonomy a b c d ≠ 0 := by
  rw [cubicHolonomy_factor_of_add_eq hsum]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpos.ne')
    (sub_ne_zero.mpr hac)) (sub_ne_zero.mpr had)

/-- Away from zero, sinc has the reciprocal bound that exposes the two
Hilbert kernels hidden in cubic holonomy. -/
lemma abs_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    |Real.sinc x| ≤ |x|⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, abs_div, div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one x)
    (inv_nonneg.mpr (abs_nonneg x))

/-- On the product-lock hyperplane, phase averaging gains the product of the
two pairing gaps.  This is the precise tensor-Hilbert kernel that any
non-gauge realization may feed to a double Montgomery--Vaughan estimate. -/
theorem abs_sinc_cubicHolonomy_le {A a b c d : ℝ}
    (hA : 0 < A) (hsum : a + b = c + d) (hpos : 0 < a + b)
    (hac : a ≠ c) (had : a ≠ d) :
    |Real.sinc (A * cubicHolonomy a b c d)| ≤
      (3 * A * (a + b) * |a - c| * |a - d|)⁻¹ := by
  have hhol : cubicHolonomy a b c d ≠ 0 :=
    cubicHolonomy_ne_zero_of_add_eq_of_not_pairing hsum hpos hac had
  calc
    |Real.sinc (A * cubicHolonomy a b c d)| ≤
        |A * cubicHolonomy a b c d|⁻¹ :=
      abs_sinc_le_inv_abs (mul_ne_zero hA.ne' hhol)
    _ = (3 * A * (a + b) * |a - c| * |a - d|)⁻¹ := by
      rw [cubicHolonomy_factor_of_add_eq hsum]
      simp only [abs_mul, abs_of_pos hA, abs_of_pos hpos]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring

/-- Prime-product version: cubic logarithmic colour separates every exact
product lock except literal exchange of the two factors. -/
theorem cubicLogHolonomy_ne_zero_of_product_eq
    {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    (hxy : 1 < x * y) (hprod : x * y = z * w)
    (hxz : x ≠ z) (hxw : x ≠ w) :
    cubicHolonomy (Real.log x) (Real.log y) (Real.log z) (Real.log w) ≠ 0 := by
  have hsum : Real.log x + Real.log y = Real.log z + Real.log w := by
    rw [← Real.log_mul hx.ne' hy.ne', ← Real.log_mul hz.ne' hw.ne', hprod]
  have hpos : 0 < Real.log x + Real.log y := by
    rw [← Real.log_mul hx.ne' hy.ne']
    exact Real.log_pos hxy
  have hlogxz : Real.log x ≠ Real.log z := by
    intro h
    apply hxz
    have he := congrArg Real.exp h
    simpa [Real.exp_log hx, Real.exp_log hz] using he
  have hlogxw : Real.log x ≠ Real.log w := by
    intro h
    apply hxw
    have he := congrArg Real.exp h
    simpa [Real.exp_log hx, Real.exp_log hw] using he
  exact cubicHolonomy_ne_zero_of_add_eq_of_not_pairing hsum hpos hlogxz hlogxw

/-- Uniform averaging of the cubic-phase parameter produces the sinc kernel
of the holonomy defect. -/
def phaseParameterAverage (A D : ℝ) : ℂ :=
  ((2 * A : ℝ)⁻¹ : ℂ) *
    ∫ α in -A..A, Complex.exp (Complex.I * ((α * D : ℝ) : ℂ))

theorem phaseParameterAverage_eq_sinc {A D : ℝ} (hA : A ≠ 0) :
    phaseParameterAverage A D = (Real.sinc (A * D) : ℂ) := by
  by_cases hD : D = 0
  · subst D
    simp [phaseParameterAverage]
    field_simp [ofReal_ne_zero.mpr hA]
    norm_num
  · have hscale := intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (a := -A) (b := A) D
    have hsinc := integral_exp_mul_I_eq_sinc (A * D)
    simp only [Complex.real_smul] at hscale
    have hleft : D * -A = -(A * D) := by ring
    have hright : D * A = A * D := by ring
    rw [hleft, hright] at hscale
    rw [hsinc] at hscale
    unfold phaseParameterAverage
    have hint :
        (∫ α in -A..A, Complex.exp (Complex.I * ((α * D : ℝ) : ℂ))) =
          ∫ α in -A..A, Complex.exp (((D * α : ℝ) : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro α _
      push_cast
      congr 1
      ring
    rw [hint]
    have hDcomplex : (D : ℂ) ≠ 0 := ofReal_ne_zero.mpr hD
    have hAcomplex : (A : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA
    have hscaleC :
        (D : ℂ) * (∫ α in -A..A,
          Complex.exp (((D * α : ℝ) : ℂ) * Complex.I)) =
          (2 * (A * D) * Real.sinc (A * D) : ℝ) := by
      exact_mod_cast hscale
    have hI :
        (∫ α in -A..A, Complex.exp (((D * α : ℝ) : ℂ) * Complex.I)) =
          (2 * A : ℂ) * (Real.sinc (A * D) : ℂ) := by
      apply mul_left_cancel₀ hDcomplex
      calc
        (D : ℂ) * (∫ α in -A..A,
            Complex.exp (((D * α : ℝ) : ℂ) * Complex.I)) =
            (2 * (A * D) * Real.sinc (A * D) : ℝ) := hscaleC
        _ = (D : ℂ) * ((2 * A : ℂ) * (Real.sinc (A * D) : ℂ)) := by
          push_cast
          ring
    rw [hI]
    field_simp [hAcomplex]
    push_cast
    ring

end

end RiemannGaussian
