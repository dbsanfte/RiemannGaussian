import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionHighOrdinateRigidity

/-!
# Boundary rigidity of the eta reflection multiplier

This module evaluates the eta-completed reflection multiplier on the outer
boundary `Re s = 1`.  Away from the central point `t = 0` and the dyadic
resonances `cos (t * log 2) = 1`, its squared norm is

`((1 + t²) / (2 * pi * t)) * tanh (pi * t / 2) *
  ((5 - 4 * cos (t * log 2)) / (2 - 2 * cos (t * log 2)))`.

Exact Taylor inequalities, hyperbolic estimates, and a rational polynomial
certificate prove that this expression is strictly greater than one for every
nonzero real ordinate.  The singular exclusions are explicit because the
underlying quotient is totalized at zero denominators.

This is boundary data for a future maximum-principle argument.  It does not
propagate the inequality into the open strip and does not prove that the
multiplier has unit norm at a zeta zero.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Exact squared norm of `Gammaℝ (1 + it)` on the vertical line `Re s = 1`. -/
theorem normSq_Gammaℝ_one_add_mul_I (t : ℝ) :
    Complex.normSq (Complex.Gammaℝ (1 + (t : ℂ) * Complex.I)) =
      1 / Real.cosh (Real.pi * t / 2) := by
  have href := Complex.Gammaℝ_one_sub_mul_Gammaℝ_one_add ((t : ℂ) * Complex.I)
  have hleft :
      Complex.Gammaℝ (1 - (t : ℂ) * Complex.I) =
        starRingEnd ℂ (Complex.Gammaℝ (1 + (t : ℂ) * Complex.I)) := by
    rw [← Gammaℝ_conj]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hleft, ← Complex.normSq_eq_conj_mul_self] at href
  have hcos :
      Complex.cos (Real.pi * ((t : ℂ) * Complex.I) / 2) =
        (Real.cosh (Real.pi * t / 2) : ℝ) := by
    rw [show (Real.pi : ℂ) * ((t : ℂ) * Complex.I) / 2 =
        ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [hcos] at href
  have hreal : Complex.normSq
      (Complex.Gammaℝ (1 + (t : ℂ) * Complex.I)) =
        (Real.cosh (Real.pi * t / 2))⁻¹ := by
    exact_mod_cast href
  simpa [one_div] using hreal

/-- Exact squared norm of `Gammaℝ (-it)` away from its pole at `t = 0`. -/
theorem normSq_Gammaℝ_neg_mul_I {t : ℝ} (ht : t ≠ 0) :
    Complex.normSq (Complex.Gammaℝ (-(t : ℂ) * Complex.I)) =
      2 * Real.pi / (t * Real.sinh (Real.pi * t / 2)) := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have href := Complex.Gammaℝ_one_sub_mul_Gammaℝ_one_add (1 + z)
  have hadd : Complex.Gammaℝ (1 + (1 + z)) =
      Complex.Gammaℝ z * z / 2 / Real.pi := by
    convert Complex.Gammaℝ_add_two hz using 1
    ring_nf
  have hconj : Complex.Gammaℝ z =
      starRingEnd ℂ (Complex.Gammaℝ (-z)) := by
    rw [← Gammaℝ_conj]
    congr 1
    simp [z]
  rw [show 1 - (1 + z) = -z by ring, hadd, hconj] at href
  have hleft :
      Complex.Gammaℝ (-z) *
          (starRingEnd ℂ (Complex.Gammaℝ (-z)) * z / 2 / Real.pi) =
        (Complex.normSq (Complex.Gammaℝ (-z)) : ℂ) * z / 2 / Real.pi := by
    rw [← Complex.mul_conj (Complex.Gammaℝ (-z))]
    ring
  rw [hleft] at href
  have hcos :
      Complex.cos (Real.pi * (1 + z) / 2) =
        -(Real.sinh (Real.pi * t / 2) : ℝ) * Complex.I := by
    rw [show (Real.pi : ℂ) * (1 + z) / 2 =
        (Real.pi / 2 : ℝ) + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I by
          dsimp [z]
          push_cast
          ring,
      Complex.cos_add_mul_I]
    push_cast
    simp
  rw [hcos] at href
  have hsinh : Real.sinh (Real.pi * t / 2) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero ht) (by norm_num)
  have hinv :
      (-(Real.sinh (Real.pi * t / 2) : ℝ) * Complex.I)⁻¹ =
        ((Real.sinh (Real.pi * t / 2))⁻¹ : ℝ) * Complex.I := by
    field_simp [hsinh]
    simp
  have hcoeff :
      (Complex.normSq (Complex.Gammaℝ (-z)) : ℂ) * z / 2 / Real.pi =
        ((Complex.normSq (Complex.Gammaℝ (-z)) * t / 2 / Real.pi : ℝ) : ℂ) *
          Complex.I := by
    dsimp [z]
    push_cast
    ring
  rw [hinv, hcoeff] at href
  have hcoeffEq :
      Complex.normSq (Complex.Gammaℝ (-z)) * t / 2 / Real.pi =
        (Real.sinh (Real.pi * t / 2))⁻¹ := by
    have hcast := mul_right_cancel₀ Complex.I_ne_zero href
    exact_mod_cast hcast
  -- The imaginary part of the reflection identity is the desired real formula.
  field_simp [ht, Real.pi_ne_zero, hsinh] at hcoeffEq ⊢
  nlinarith [hcoeffEq]

/-- Exact squared norm of the completed-Gamma boundary ratio. -/
theorem normSq_Gammaℝ_boundary_ratio {t : ℝ} (ht : t ≠ 0) :
    Complex.normSq
        (Complex.Gammaℝ (1 + (t : ℂ) * Complex.I) /
          Complex.Gammaℝ (-(t : ℂ) * Complex.I)) =
      t * Real.tanh (Real.pi * t / 2) / (2 * Real.pi) := by
  rw [Complex.normSq_div, normSq_Gammaℝ_one_add_mul_I,
    normSq_Gammaℝ_neg_mul_I ht, Real.tanh_eq_sinh_div_cosh]
  have hsinh : Real.sinh (Real.pi * t / 2) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero ht) (by norm_num)
  have hcosh : Real.cosh (Real.pi * t / 2) ≠ 0 :=
    (Real.cosh_pos _).ne'
  field_simp [ht, Real.pi_ne_zero, hsinh, hcosh]

/-- Fourier form of the purely imaginary complex power `2 ^ (it)`. -/
theorem two_cpow_mul_I (t : ℝ) :
    (2 : ℂ) ^ ((t : ℂ) * Complex.I) =
      (Real.cos (t * Real.log 2) : ℝ) +
        (Real.sin (t * Real.log 2) : ℝ) * Complex.I := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℝ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  have hmul :
      (Real.log 2 : ℂ) * ((t : ℂ) * Complex.I) =
        ((t * Real.log 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hmul, Complex.exp_mul_I]
  push_cast
  rfl

/-- Exact squared norm of the paired eta factor on the line `Re s = 0`. -/
theorem normSq_pairedEtaFactor_neg_mul_I (t : ℝ) :
    Complex.normSq (pairedEtaFactor (-(t : ℂ) * Complex.I)) =
      5 - 4 * Real.cos (t * Real.log 2) := by
  unfold pairedEtaFactor
  rw [show -(-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I by ring,
    two_cpow_mul_I]
  rw [show (1 : ℂ) - 2 *
        ((Real.cos (t * Real.log 2) : ℝ) +
          (Real.sin (t * Real.log 2) : ℝ) * Complex.I) =
      ((1 - 2 * Real.cos (t * Real.log 2) : ℝ) : ℂ) +
        ((-2 * Real.sin (t * Real.log 2) : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
    Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq (t * Real.log 2)]

/-- Exact squared norm of the paired eta factor on the line `Re s = 1`. -/
theorem normSq_pairedEtaFactor_one_add_mul_I (t : ℝ) :
    Complex.normSq
        (pairedEtaFactor (1 + (t : ℂ) * Complex.I)) =
      2 - 2 * Real.cos (t * Real.log 2) := by
  have hpow :
      (2 : ℂ) ^ (-(1 + (t : ℂ) * Complex.I)) =
        (1 / 2 : ℂ) * (2 : ℂ) ^ ((-t : ℝ) * Complex.I) := by
    rw [show -(1 + (t : ℂ) * Complex.I) =
        (-1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
      Complex.cpow_neg_one]
    norm_num
  unfold pairedEtaFactor
  rw [hpow, two_cpow_mul_I]
  rw [show -t * Real.log 2 = -(t * Real.log 2) by ring,
    Real.cos_neg, Real.sin_neg]
  rw [show (1 : ℂ) - 2 *
        ((1 / 2 : ℂ) *
          ((Real.cos (t * Real.log 2) : ℝ) +
            (-Real.sin (t * Real.log 2) : ℝ) * Complex.I)) =
      (((1 - Real.cos (t * Real.log 2) : ℝ) : ℂ) +
        ((Real.sin (t * Real.log 2) : ℝ) : ℂ) * Complex.I) by
          push_cast
          ring,
    Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq (t * Real.log 2)]

/-- The paired eta factor has no zero on the imaginary axis. -/
theorem pairedEtaFactor_neg_mul_I_ne_zero (t : ℝ) :
    pairedEtaFactor (-(t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hnorm := normSq_pairedEtaFactor_neg_mul_I t
  rw [hzero, Complex.normSq_zero] at hnorm
  nlinarith [Real.cos_le_one (t * Real.log 2)]

/-- The paired eta factor's zeros on `Re s = 1` are exactly the dyadic resonances. -/
theorem pairedEtaFactor_one_add_mul_I_ne_zero_iff (t : ℝ) :
    pairedEtaFactor (1 + (t : ℂ) * Complex.I) ≠ 0 ↔
      Real.cos (t * Real.log 2) ≠ 1 := by
  rw [← Complex.normSq_pos, normSq_pairedEtaFactor_one_add_mul_I]
  constructor <;> intro h
  · nlinarith
  · have hlt : Real.cos (t * Real.log 2) < 1 :=
      lt_of_le_of_ne (Real.cos_le_one _) h
    linarith

/-- The completed Gamma factor is nonzero at `-it` for nonzero `t`. -/
theorem Gammaℝ_neg_mul_I_ne_zero {t : ℝ} (ht : t ≠ 0) :
    Complex.Gammaℝ (-(t : ℂ) * Complex.I) ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  have him := congrArg Complex.im hn
  simp at him
  exact ht (by linarith)

/-- Expands the reflection multiplier into spectral, Gamma, and eta ratios
when every denominator in the defining quotient is nonzero. -/
theorem pairedEtaLaplaceReflectionMultiplier_eq_explicit_of_ne
    {s : ℂ} (hs0 : s ≠ 0) (h1s : 1 - s ≠ 0)
    (hfactorS : pairedEtaFactor s ≠ 0)
    (hfactorPartner : pairedEtaFactor (1 - s) ≠ 0)
    (hgammaPartner : Complex.Gammaℝ (1 - s) ≠ 0) :
    pairedEtaLaplaceReflectionMultiplier s =
      (s / (1 - s)) *
        (Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)) *
        (pairedEtaFactor (1 - s) / pairedEtaFactor s) := by
  unfold pairedEtaLaplaceReflectionMultiplier
    pairedEtaCompletedLaplaceAmplitude pairedEtaXiCompletionFactor
    pairedEtaXiCompletionNumerator
  field_simp [hs0, h1s, hfactorS, hfactorPartner, hgammaPartner]
  ring

/-- Explicit factorization of the reflection multiplier on `Re s = 1`, away
from the central point and dyadic resonances. -/
theorem pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_eq_explicit
    {t : ℝ} (ht : t ≠ 0)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    pairedEtaLaplaceReflectionMultiplier
        (1 + (t : ℂ) * Complex.I) =
      ((1 + (t : ℂ) * Complex.I) / (-(t : ℂ) * Complex.I)) *
        (Complex.Gammaℝ (1 + (t : ℂ) * Complex.I) /
          Complex.Gammaℝ (-(t : ℂ) * Complex.I)) *
        (pairedEtaFactor (-(t : ℂ) * Complex.I) /
          pairedEtaFactor (1 + (t : ℂ) * Complex.I)) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, Complex.mul_re] at hre
  have h1s : 1 - s ≠ 0 := by
    have hcoord : 1 - s = -(t : ℂ) * Complex.I := by simp [s]
    rw [hcoord]
    exact mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr ht)) Complex.I_ne_zero
  have hfactorS : pairedEtaFactor s ≠ 0 := by
    simpa [s] using
      (pairedEtaFactor_one_add_mul_I_ne_zero_iff t).2 heta
  have hfactorPartner : pairedEtaFactor (1 - s) ≠ 0 := by
    simpa [s] using pairedEtaFactor_neg_mul_I_ne_zero t
  have hgammaPartner : Complex.Gammaℝ (1 - s) ≠ 0 := by
    simpa [s] using Gammaℝ_neg_mul_I_ne_zero ht
  simpa [s] using pairedEtaLaplaceReflectionMultiplier_eq_explicit_of_ne
    hs0 h1s hfactorS hfactorPartner hgammaPartner

/-- Exact squared norm of the elementary spectral ratio on `Re s = 1`. -/
theorem normSq_etaReflectionBoundary_spectralRatio {t : ℝ} (ht : t ≠ 0) :
    Complex.normSq
        ((1 + (t : ℂ) * Complex.I) / (-(t : ℂ) * Complex.I)) =
      (1 + t ^ 2) / t ^ 2 := by
  rw [Complex.normSq_div]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  field_simp [ht]

/-- Exact squared norm of the eta-factor ratio on `Re s = 1`. -/
theorem normSq_etaReflectionBoundary_etaRatio (t : ℝ) :
    Complex.normSq
        (pairedEtaFactor (-(t : ℂ) * Complex.I) /
          pairedEtaFactor (1 + (t : ℂ) * Complex.I)) =
      (5 - 4 * Real.cos (t * Real.log 2)) /
        (2 - 2 * Real.cos (t * Real.log 2)) := by
  rw [Complex.normSq_div, normSq_pairedEtaFactor_neg_mul_I,
    normSq_pairedEtaFactor_one_add_mul_I]

/-- Exact squared norm of the eta reflection multiplier on the nonsingular
part of the outer boundary `Re s = 1`. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I
    {t : ℝ} (ht : t ≠ 0)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    Complex.normSq
        (pairedEtaLaplaceReflectionMultiplier
          (1 + (t : ℂ) * Complex.I)) =
      ((1 + t ^ 2) / (2 * Real.pi * t)) *
        Real.tanh (Real.pi * t / 2) *
        ((5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2))) := by
  rw [pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_eq_explicit ht heta,
    Complex.normSq_mul, Complex.normSq_mul,
    normSq_etaReflectionBoundary_spectralRatio ht,
    normSq_Gammaℝ_boundary_ratio ht,
    normSq_etaReflectionBoundary_etaRatio]
  field_simp [ht, Real.pi_ne_zero]

private theorem etaReflectionBoundary_cos_le_quartic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun u =>
    1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u
  have hderiv (u : ℝ) :
      deriv f u = Real.sin u - (u - u ^ 3 / 6) := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hderiv]
      have hu0 : 0 ≤ u := by
        have huPos : 0 < u := by
          simpa only [interior_Ici, Set.mem_Ioi] using hu
        exact huPos.le
      exact sub_nonneg.mpr (Real.sin_ge_sub_cube hu0)
  have h0x := hmono (by simp) hx hx
  simpa [f] using h0x

private theorem etaReflectionBoundary_sin_le_quintic {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f : ℝ → ℝ := fun u =>
    u - u ^ 3 / 6 + u ^ 5 / 120 - Real.sin u
  have hderiv (u : ℝ) :
      deriv f u = 1 - u ^ 2 / 2 + u ^ 4 / 24 - Real.cos u := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hderiv]
      have hu0 : 0 ≤ u := by
        have huPos : 0 < u := by
          simpa only [interior_Ici, Set.mem_Ioi] using hu
        exact huPos.le
      linarith [etaReflectionBoundary_cos_le_quartic hu0]
  have h0x := hmono (by simp) hx hx
  simpa [f] using h0x

private theorem etaReflectionBoundary_three_add_sq_mul_sin_sq_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 21 / 20) :
    (3 + x ^ 2) * Real.sin x ^ 2 ≤ 3 * x ^ 2 := by
  let p : ℝ := x - x ^ 3 / 6 + x ^ 5 / 120
  have hxpi : x ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  have hsinp : Real.sin x ≤ p := by
    simpa [p] using etaReflectionBoundary_sin_le_quintic hx0
  have hp0 : 0 ≤ p := hsin0.trans hsinp
  have hsq : Real.sin x ^ 2 ≤ p ^ 2 :=
    (sq_le_sq₀ hsin0 hp0).2 hsinp
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy2 : x ^ 2 ≤ 2 := by nlinarith
  have hy3 : (x ^ 2) ^ 3 ≤ (2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hy0 hy2 3
  have hpoly :
      0 ≤ 2880 - 520 * x ^ 2 + 37 * x ^ 4 - x ^ 6 := by
    have hx4 : 0 ≤ x ^ 4 := by positivity
    have hxeven : (x ^ 2) ^ 3 = x ^ 6 := by ring
    rw [hxeven] at hy3
    nlinarith
  have hpbound : (3 + x ^ 2) * p ^ 2 ≤ 3 * x ^ 2 := by
    have hfactor :
        3 * x ^ 2 - (3 + x ^ 2) * p ^ 2 =
          x ^ 6 * (2880 - 520 * x ^ 2 + 37 * x ^ 4 - x ^ 6) / 14400 := by
      dsimp [p]
      ring
    rw [← sub_nonneg, hfactor]
    positivity
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans hpbound

private theorem etaReflectionBoundary_self_le_sinh {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sinh x := by
  let f : ℝ → ℝ := fun u => Real.sinh u - u
  have hderiv (u : ℝ) : deriv f u = Real.cosh u - 1 := by
    simp (disch := fun_prop) [f]
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro u _
      rw [hderiv]
      exact sub_nonneg.mpr (Real.one_le_cosh u)
  have h0x := hmono (by simp) hx hx
  simpa [f] using h0x

private theorem etaReflectionBoundary_one_add_sq_div_two_le_cosh {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 / 2 ≤ Real.cosh x := by
  let f : ℝ → ℝ := fun u => Real.cosh u - (1 + u ^ 2 / 2)
  have hderiv (u : ℝ) : deriv f u = Real.sinh u - u := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hderiv]
      have hu0 : 0 ≤ u := by
        have huPos : 0 < u := by
          simpa only [interior_Ici, Set.mem_Ioi] using hu
        exact huPos.le
      exact sub_nonneg.mpr (etaReflectionBoundary_self_le_sinh hu0)
  have h0x := hmono (by simp) hx hx
  simpa [f] using h0x

private theorem etaReflectionBoundary_sinh_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x + x ^ 3 / 6 ≤ Real.sinh x := by
  let f : ℝ → ℝ := fun u => Real.sinh u - (u + u ^ 3 / 6)
  have hderiv (u : ℝ) : deriv f u = Real.cosh u - (1 + u ^ 2 / 2) := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro u hu
      rw [hderiv]
      have hu0 : 0 ≤ u := by
        have huPos : 0 < u := by
          simpa only [interior_Ici, Set.mem_Ioi] using hu
        exact huPos.le
      exact sub_nonneg.mpr (etaReflectionBoundary_one_add_sq_div_two_le_cosh hu0)
  have h0x := hmono (by simp) hx hx
  simpa [f] using h0x

private theorem etaReflectionBoundary_cubic_normalized_le_tanh {x : ℝ} (hx : 0 ≤ x) :
    (x + x ^ 3 / 6) / Real.sqrt (1 + (x + x ^ 3 / 6) ^ 2) ≤
      Real.tanh x := by
  let p : ℝ := x + x ^ 3 / 6
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hsinh0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  have hpsinh : p ≤ Real.sinh x := by
    simpa [p] using etaReflectionBoundary_sinh_cubic_lower hx
  have hsqrtp : 0 < Real.sqrt (1 + p ^ 2) := by positivity
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  have hcross : p * Real.cosh x ≤
      Real.sinh x * Real.sqrt (1 + p ^ 2) := by
    rw [← sq_le_sq₀ (mul_nonneg hp0 hcosh.le)
      (mul_nonneg hsinh0 (Real.sqrt_nonneg _)),
      mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.cosh_sq']
    have hsq : p ^ 2 ≤ Real.sinh x ^ 2 :=
      (sq_le_sq₀ hp0 hsinh0).2 hpsinh
    nlinarith [sq_nonneg p, sq_nonneg (Real.sinh x)]
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_le_div_iff₀ hsqrtp hcosh).2 hcross

/-- A uniform lower bound for the eta-factor ratio when `0 < t ≤ 3`. -/
theorem etaReflectionBoundary_etaRatio_lower
    {t : ℝ} (ht : 0 < t) (ht3 : t ≤ 3) :
    25 / 12 + 1 / (Real.log 2 ^ 2 * t ^ 2) ≤
      (5 - 4 * Real.cos (t * Real.log 2)) /
        (2 - 2 * Real.cos (t * Real.log 2)) := by
  let q : ℝ := t * Real.log 2 / 2
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqUpper : q ≤ 21 / 20 := by
    have hlogUpper : Real.log 2 < 7 / 10 := by
      linarith [Real.log_two_lt_d9]
    dsimp [q]
    nlinarith
  have hsinBound := etaReflectionBoundary_three_add_sq_mul_sin_sq_le hq0.le hqUpper
  have hqPi : q < Real.pi := by linarith [Real.pi_gt_three]
  have hsin0 : 0 < Real.sin q :=
    Real.sin_pos_of_pos_of_lt_pi hq0 hqPi
  have hfrac :
      (3 + q ^ 2) / (12 * q ^ 2) ≤ 1 / (4 * Real.sin q ^ 2) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 12 * q ^ 2)
      (by positivity : 0 < 4 * Real.sin q ^ 2)]
    nlinarith
  have hphase : t * Real.log 2 = 2 * q := by
    dsimp [q]
    ring
  rw [hphase, Real.cos_two_mul_eq_one_sub]
  have hqSq : 4 * q ^ 2 = Real.log 2 ^ 2 * t ^ 2 := by
    dsimp [q]
    ring
  have hqNe : q ≠ 0 := hq0.ne'
  have hsinNe : Real.sin q ≠ 0 := hsin0.ne'
  field_simp [hqNe, hsinNe, hlog0.ne', ht.ne'] at hfrac ⊢
  nlinarith [hfrac, hqSq]

private def etaReflectionBoundaryPolynomial (x : ℝ) : ℝ :=
  171211610646102327301275625 * x ^ 6 -
    42344842220122531875063406 * x ^ 5 -
    2228701850867372876134004375 * x ^ 4 +
    458574170242893522579000000 * x ^ 3 +
    5774070719434582400400000000 * x ^ 2 +
    4842931689735552000000000000 * x +
    1001798461440000000000000000

private theorem etaReflectionBoundary_polynomial_pos {x : ℝ} (hx : 0 < x) :
    0 < etaReflectionBoundaryPolynomial x := by
  have hx0 : 0 ≤ x := hx.le
  by_cases hx1 : x ≤ 1
  · have hid : etaReflectionBoundaryPolynomial x =
        1001798461440000000000000000 * (1 - x) ^ 6 +
        10853722458375552000000000000 * x * (1 - x) ^ 5 +
        45015706089712342400400000000 * x ^ 2 * (1 - x) ^ 4 +
        92020143174136743124179000000 * x ^ 3 * (1 - x) ^ 3 +
        97247738795424322094002995625 * x ^ 4 * (1 - x) ^ 2 +
        50197706061829901885193927844 * x ^ 5 * (1 - x) +
        9977539958411634842271207844 * x ^ 6 := by
      unfold etaReflectionBoundaryPolynomial
      ring
    rw [hid]
    positivity
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hx2 : x ≤ 2
    · have hid : etaReflectionBoundaryPolynomial x =
          9977539958411634842271207844 * (2 - x) ^ 6 +
          69532773439109716222060566284 * (x - 1) * (2 - x) ^ 5 +
          193923075681823393778336187825 * (x - 1) ^ 2 * (2 - x) ^ 4 +
          274459918061923332983481106280 * (x - 1) ^ 3 * (2 - x) ^ 3 +
          205633683207475825240973550040 * (x - 1) ^ 4 * (2 - x) ^ 2 +
          76766212333052946020105538528 * (x - 1) ^ 5 * (2 - x) +
          11395816597021243691367541008 * (x - 1) ^ 6 := by
        unfold etaReflectionBoundaryPolynomial
        ring
      rw [hid]
      positivity
    · have hx2' : 2 < x := lt_of_not_ge hx2
      by_cases hx3 : x ≤ 3
      · have hid : etaReflectionBoundaryPolynomial x =
            11395816597021243691367541008 * (3 - x) ^ 6 +
            59983586831201978276304953568 * (x - 2) * (3 - x) ^ 5 +
            121720555698220986521970625240 * (x - 2) ^ 2 * (3 - x) ^ 4 +
            123291709799164418758892314200 * (x - 2) ^ 3 * (3 - x) ^ 3 +
            76070960930566005980581510785 * (x - 2) ^ 4 * (3 - x) ^ 2 +
            39618175168173377934789302232 * (x - 2) ^ 5 * (3 - x) +
            13877350183377641103368168592 * (x - 2) ^ 6 := by
          unfold etaReflectionBoundaryPolynomial
          ring
        rw [hid]
        positivity
      · have hx3' : 3 < x := lt_of_not_ge hx3
        by_cases hx4 : x ≤ 4
        · have hid : etaReflectionBoundaryPolynomial x =
              13877350183377641103368168592 * (4 - x) ^ 6 +
              126910027032358315305628720872 * (x - 3) * (4 - x) ^ 5 +
              512530220251490692834778603985 * (x - 3) ^ 2 * (4 - x) ^ 4 +
              1120925000258851088233094657520 * (x - 3) ^ 3 * (4 - x) ^ 3 +
              1368783389793582247527789282400 * (x - 3) ^ 4 * (4 - x) ^ 2 +
              876666089904457991147022313216 * (x - 3) ^ 5 * (4 - x) +
              229481368577862915547110912256 * (x - 3) ^ 6 := by
            unfold etaReflectionBoundaryPolynomial
            ring
          rw [hid]
          positivity
        · have hx4' : 4 < x := lt_of_not_ge hx4
          have hid : etaReflectionBoundaryPolynomial x =
              229481368577862915547110912256 +
              500222121562719502135643160320 * (x - 4) +
              427673468939236024999341400160 * (x - 4) ^ 2 +
              177175031428156301350057585040 * (x - 4) ^ 3 +
              38015187859794735038670877505 * (x - 4) ^ 4 +
              4066733813286333323355551594 * (x - 4) ^ 5 +
              171211610646102327301275625 * (x - 4) ^ 6 := by
            unfold etaReflectionBoundaryPolynomial
            ring
          rw [hid]
          positivity

private def etaReflectionBoundaryRationalCubic (t : ℝ) : ℝ :=
  (157 / 50) * t / 2 + ((157 / 50) * t / 2) ^ 3 / 6

private def etaReflectionBoundaryRationalEtaLower (t : ℝ) : ℝ :=
  25 / 12 + 1 / ((139 / 200) ^ 2 * t ^ 2)

private def etaReflectionBoundaryRationalLower (t : ℝ) : ℝ :=
  (1 + t ^ 2) / (2 * (22 / 7) * t) *
    (etaReflectionBoundaryRationalCubic t /
      Real.sqrt (1 + etaReflectionBoundaryRationalCubic t ^ 2)) *
    etaReflectionBoundaryRationalEtaLower t

private theorem etaReflectionBoundary_one_lt_rationalLower {t : ℝ} (ht : 0 < t) :
    1 < etaReflectionBoundaryRationalLower t := by
  let p := etaReflectionBoundaryRationalCubic t
  let e := etaReflectionBoundaryRationalEtaLower t
  let F :=
    (1 + t ^ 2) ^ 2 * p ^ 2 * e ^ 2 -
      4 * (22 / 7) ^ 2 * t ^ 2 * (1 + p ^ 2)
  have hp : 0 < p := by
    dsimp [p, etaReflectionBoundaryRationalCubic]
    positivity
  have he : 0 < e := by
    dsimp [e, etaReflectionBoundaryRationalEtaLower]
    positivity
  have hpoly : 0 < etaReflectionBoundaryPolynomial (t ^ 2) :=
    etaReflectionBoundary_polynomial_pos (sq_pos_of_pos ht)
  have hFidentity :
      F = etaReflectionBoundaryPolynomial (t ^ 2) /
        (94824437230656000000000000 * t ^ 2) := by
    dsimp [F, p, e, etaReflectionBoundaryRationalCubic,
      etaReflectionBoundaryRationalEtaLower]
    field_simp [ht.ne']
    unfold etaReflectionBoundaryPolynomial
    ring
  have hF : 0 < F := by
    rw [hFidentity]
    positivity
  have hsqrt : 0 < Real.sqrt (1 + p ^ 2) := by positivity
  have hlowerPos : 0 < etaReflectionBoundaryRationalLower t := by
    unfold etaReflectionBoundaryRationalLower
    rw [show etaReflectionBoundaryRationalCubic t = p by rfl,
      show etaReflectionBoundaryRationalEtaLower t = e by rfl]
    positivity
  have hsqDiff :
      etaReflectionBoundaryRationalLower t ^ 2 - 1 =
        F / (4 * (22 / 7) ^ 2 * t ^ 2 * (1 + p ^ 2)) := by
    unfold etaReflectionBoundaryRationalLower
    rw [show etaReflectionBoundaryRationalCubic t = p by rfl,
      show etaReflectionBoundaryRationalEtaLower t = e by rfl]
    simp only [mul_pow, div_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + p ^ 2)]
    dsimp [F]
    field_simp [ht.ne']
    ring
  have hsq : 1 ^ 2 < etaReflectionBoundaryRationalLower t ^ 2 := by
    rw [one_pow]
    have hden : 0 < 4 * (22 / 7 : ℝ) ^ 2 * t ^ 2 * (1 + p ^ 2) := by
      positivity
    have : 0 < etaReflectionBoundaryRationalLower t ^ 2 - 1 := by
      rw [hsqDiff]
      exact div_pos hF hden
    linarith
  exact (sq_lt_sq₀ (by norm_num) hlowerPos.le).1 hsq

private theorem etaReflectionBoundary_normalized_le_normalized
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / Real.sqrt (1 + a ^ 2) ≤
      b / Real.sqrt (1 + b ^ 2) := by
  have hb : 0 ≤ b := ha.trans hab
  have hsqrta : 0 < Real.sqrt (1 + a ^ 2) := by positivity
  have hsqrtb : 0 < Real.sqrt (1 + b ^ 2) := by positivity
  rw [div_le_div_iff₀ hsqrta hsqrtb]
  rw [← sq_le_sq₀ (mul_nonneg ha hsqrtb.le)
    (mul_nonneg hb hsqrta.le),
    mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 1 + b ^ 2),
    Real.sq_sqrt (by positivity : 0 ≤ 1 + a ^ 2)]
  nlinarith [sq_nonneg a, sq_nonneg b]

private theorem etaReflectionBoundary_one_lt_product_of_le_three
    {t : ℝ} (ht : 0 < t) (ht3 : t ≤ 3) :
    1 < ((1 + t ^ 2) / (2 * Real.pi * t)) *
        Real.tanh (Real.pi * t / 2) *
        ((5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2))) := by
  let z0 : ℝ := (157 / 50) * t / 2
  let z : ℝ := Real.pi * t / 2
  let p0 : ℝ := z0 + z0 ^ 3 / 6
  let p : ℝ := z + z ^ 3 / 6
  have hz0 : 0 < z0 := by dsimp [z0]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hzle : z0 ≤ z := by
    dsimp [z0, z]
    nlinarith [Real.pi_gt_d2]
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hple : p0 ≤ p := by
    have hcubic : z0 ^ 3 ≤ z ^ 3 :=
      pow_le_pow_left₀ hz0.le hzle 3
    dsimp [p0, p]
    linarith
  have hnorm :
      p0 / Real.sqrt (1 + p0 ^ 2) ≤ Real.tanh z := by
    exact (etaReflectionBoundary_normalized_le_normalized hp0 hple).trans
      (etaReflectionBoundary_cubic_normalized_le_tanh hz.le)
  have hprefactor :
      (1 + t ^ 2) / (2 * (22 / 7) * t) ≤
        (1 + t ^ 2) / (2 * Real.pi * t) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * (22 / 7 : ℝ) * t)
      (by positivity : 0 < 2 * Real.pi * t)]
    have hpiUpper : Real.pi < 22 / 7 := by
      linarith [Real.pi_lt_d4]
    have hden : 2 * Real.pi * t ≤ 2 * (22 / 7 : ℝ) * t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpiUpper.le (by norm_num)) ht.le
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogUpper : Real.log 2 < 139 / 200 := by
    linarith [Real.log_two_lt_d9]
  have hdenLog :
      Real.log 2 ^ 2 * t ^ 2 ≤ (139 / 200) ^ 2 * t ^ 2 := by
    have hsqlog : Real.log 2 ^ 2 ≤ (139 / 200) ^ 2 :=
      (sq_le_sq₀ hlog0.le (by norm_num)).2 hlogUpper.le
    exact mul_le_mul_of_nonneg_right hsqlog (sq_nonneg t)
  have hetaRational :
      etaReflectionBoundaryRationalEtaLower t ≤
        25 / 12 + 1 / (Real.log 2 ^ 2 * t ^ 2) := by
    unfold etaReflectionBoundaryRationalEtaLower
    have hinv :
        1 / ((139 / 200) ^ 2 * t ^ 2) ≤
          1 / (Real.log 2 ^ 2 * t ^ 2) := by
      rw [div_le_div_iff₀
        (by positivity : 0 < (139 / 200 : ℝ) ^ 2 * t ^ 2)
        (by positivity : 0 < Real.log 2 ^ 2 * t ^ 2)]
      simpa only [one_mul] using hdenLog
    linarith
  have heta :
      etaReflectionBoundaryRationalEtaLower t ≤
        (5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2)) :=
    hetaRational.trans (etaReflectionBoundary_etaRatio_lower ht ht3)
  have hlower := etaReflectionBoundary_one_lt_rationalLower ht
  apply hlower.trans_le
  unfold etaReflectionBoundaryRationalLower etaReflectionBoundaryRationalCubic
  change
    (1 + t ^ 2) / (2 * (22 / 7) * t) *
          (p0 / Real.sqrt (1 + p0 ^ 2)) *
        etaReflectionBoundaryRationalEtaLower t ≤
      (1 + t ^ 2) / (2 * Real.pi * t) * Real.tanh z *
        ((5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2)))
  have hleft0 : 0 ≤ (1 + t ^ 2) / (2 * (22 / 7) * t) := by positivity
  have hright0 : 0 ≤ (1 + t ^ 2) / (2 * Real.pi * t) := by positivity
  have hnorm0 : 0 ≤ p0 / Real.sqrt (1 + p0 ^ 2) := by positivity
  have htanh0 : 0 ≤ Real.tanh z := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hz.le) (Real.cosh_pos z).le
  have heta0 : 0 ≤ etaReflectionBoundaryRationalEtaLower t := by
    unfold etaReflectionBoundaryRationalEtaLower
    positivity
  exact mul_le_mul
    (mul_le_mul hprefactor hnorm hnorm0 hright0)
    heta heta0 (mul_nonneg hright0 htanh0)

private theorem etaReflectionBoundary_nineteen_twentieth_lt_tanh
    {x : ℝ} (hx : 9 / 2 ≤ x) :
    19 / 20 < Real.tanh x := by
  let p : ℝ := x + x ^ 3 / 6
  have hx0 : 0 ≤ x := by linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hsqrt : 0 < Real.sqrt (1 + p ^ 2) := by positivity
  have hcross :
      19 * Real.sqrt (1 + p ^ 2) < 20 * p := by
    rw [← sq_lt_sq₀ (mul_nonneg (by norm_num) hsqrt.le)
      (mul_nonneg (by norm_num) hp0.le),
      mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + p ^ 2)]
    have hpx : x ≤ p := by
      dsimp [p]
      have hx3 : 0 ≤ x ^ 3 := by positivity
      linarith
    have hpsq : x ^ 2 ≤ p ^ 2 :=
      (sq_le_sq₀ hx0 hp0.le).2 hpx
    nlinarith [sq_nonneg x]
  have hlower : 19 / 20 < p / Real.sqrt (1 + p ^ 2) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 20) hsqrt]
    simpa [mul_comm] using hcross
  exact hlower.trans_le (etaReflectionBoundary_cubic_normalized_le_tanh hx0)

private theorem etaReflectionBoundary_one_lt_product_of_three_le
    {t : ℝ} (ht3 : 3 ≤ t)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    1 < ((1 + t ^ 2) / (2 * Real.pi * t)) *
        Real.tanh (Real.pi * t / 2) *
        ((5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2))) := by
  have ht : 0 < t := by linarith
  have hz : 9 / 2 ≤ Real.pi * t / 2 := by
    have hmul := mul_le_mul ht3 Real.pi_gt_three.le (by norm_num) ht.le
    nlinarith
  have htanh : 19 / 20 < Real.tanh (Real.pi * t / 2) :=
    etaReflectionBoundary_nineteen_twentieth_lt_tanh hz
  have hpiUpper : Real.pi < 22 / 7 := by
    linarith [Real.pi_lt_d4]
  have hquadratic : 0 ≤ (3 * t - 1) * (t - 3) := by
    apply mul_nonneg <;> linarith
  have hpiMul : 35 * Real.pi * t < 110 * t := by
    have h := mul_lt_mul_of_pos_right hpiUpper ht
    nlinarith
  have hratio : 35 / 33 < (1 + t ^ 2) / (Real.pi * t) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 33)
      (by positivity : 0 < Real.pi * t)]
    nlinarith
  have hbase :
      1 < (1 + t ^ 2) / (Real.pi * t) *
        Real.tanh (Real.pi * t / 2) := by
    have hmul := mul_lt_mul hratio htanh.le
      (by norm_num : (0 : ℝ) < 19 / 20)
      (by positivity : 0 ≤ (1 + t ^ 2) / (Real.pi * t))
    have hconst : (1 : ℝ) < (35 / 33) * (19 / 20) := by norm_num
    exact hconst.trans hmul
  have hcoslt : Real.cos (t * Real.log 2) < 1 :=
    lt_of_le_of_ne (Real.cos_le_one _) heta
  have hetaTwo :
      2 < (5 - 4 * Real.cos (t * Real.log 2)) /
        (2 - 2 * Real.cos (t * Real.log 2)) := by
    rw [lt_div_iff₀ (by nlinarith : 0 < 2 - 2 * Real.cos (t * Real.log 2))]
    linarith
  have hA : 0 < (1 + t ^ 2) / (2 * Real.pi * t) *
      Real.tanh (Real.pi * t / 2) := by
    have htanh0 : 0 < Real.tanh (Real.pi * t / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
    positivity
  calc
    1 < (1 + t ^ 2) / (Real.pi * t) *
        Real.tanh (Real.pi * t / 2) := hbase
    _ = ((1 + t ^ 2) / (2 * Real.pi * t) *
          Real.tanh (Real.pi * t / 2)) * 2 := by ring
    _ < ((1 + t ^ 2) / (2 * Real.pi * t) *
          Real.tanh (Real.pi * t / 2)) *
        ((5 - 4 * Real.cos (t * Real.log 2)) /
          (2 - 2 * Real.cos (t * Real.log 2))) :=
      mul_lt_mul_of_pos_left hetaTwo hA

/-- The squared reflection-multiplier norm is strictly greater than one on the
nonsingular positive-ordinate part of `Re s = 1`. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_gt_one_of_pos
    {t : ℝ} (ht : 0 < t)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    1 < Complex.normSq
      (pairedEtaLaplaceReflectionMultiplier
        (1 + (t : ℂ) * Complex.I)) := by
  rw [normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I ht.ne' heta]
  rcases le_total t 3 with ht3 | h3t
  · exact etaReflectionBoundary_one_lt_product_of_le_three ht ht3
  · exact etaReflectionBoundary_one_lt_product_of_three_le h3t heta

/-- At every nonsingular nonzero point of `Re s = 1`, the squared eta
reflection-multiplier norm is strictly greater than one. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_gt_one
    {t : ℝ} (ht : t ≠ 0)
    (heta : Real.cos (t * Real.log 2) ≠ 1) :
    1 < Complex.normSq
      (pairedEtaLaplaceReflectionMultiplier
        (1 + (t : ℂ) * Complex.I)) := by
  rcases lt_or_gt_of_ne ht with htneg | htpos
  · have hnegpos : 0 < -t := neg_pos.mpr htneg
    have hetaNeg : Real.cos ((-t) * Real.log 2) ≠ 1 := by
      simpa [show (-t) * Real.log 2 = -(t * Real.log 2) by ring] using heta
    have hpos := normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_gt_one_of_pos
      hnegpos hetaNeg
    have hcoord :
        (1 + ((-t : ℝ) : ℂ) * Complex.I) =
          starRingEnd ℂ (1 + (t : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hcoord, pairedEtaLaplaceReflectionMultiplier_conj,
      Complex.normSq_conj] at hpos
    exact hpos
  · exact normSq_pairedEtaLaplaceReflectionMultiplier_one_add_mul_I_gt_one_of_pos htpos heta

end
end RiemannGaussian
