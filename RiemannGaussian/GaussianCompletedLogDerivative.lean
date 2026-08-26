import RiemannGaussian.GaussianExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Completed-zeta logarithmic derivative

This file isolates the exact pointwise algebra behind the Gaussian explicit
formula.  On the zero-free half-plane `re s > 1`, the negative logarithmic
derivative of zeta is decomposed into the logarithmic derivative of the
entire pole-cleared xi function, the two elementary pole factors, and the
Archimedean `log pi` and digamma terms.
-/

namespace RiemannGaussian

noncomputable section

open Filter
open scoped Topology

lemma logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnotPole : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    nlinarith
  have hGamma : Complex.Gamma (s / 2) ≠ 0 := by
    exact Complex.Gamma_ne_zero hnotPole
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hGammaDiff :
      DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hnotPole).comp s (by fun_prop)
  have hexponent : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s :=
    (hasDerivAt_id s).neg.div_const 2
  have hpowDiff :
      DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hexponent.differentiableAt.const_cpow (Or.inl hpi)
  have hpowLog :
      logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
        -Complex.log Real.pi / 2 := by
    rw [logDeriv_apply,
      Complex.deriv_const_cpow hexponent.differentiableAt (Real.pi : ℂ),
      hexponent.deriv]
    field_simp [hpow]
  have hGammaLog :
      logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
        Complex.digamma (s / 2) / 2 := by
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) =
        Complex.Gamma ∘ (fun z : ℂ => z / 2) by rfl,
      logDeriv_comp (Complex.differentiableAt_Gamma (s / 2) hnotPole)
        (x := s) (g := fun z : ℂ => z / 2) (by fun_prop)]
    rw [← Complex.digamma_def]
    simp
    ring
  change logDeriv
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s = _
  rw [logDeriv_mul s hpow hGamma]
  · rw [hpowLog, hGammaLog]
  · exact hpowDiff
  · exact hGammaDiff

/-- On the right half-plane, the pole-cleared xi function is the usual
polynomial factor times the real completed Gamma factor and zeta. -/
lemma riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    riemannXi s =
      s * (1 - s) * Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hGammaℝ : Complex.Gammaℝ s ≠ 0 := by
    rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    nlinarith
  have hzetaCompleted := riemannZeta_def_of_ne_zero hs0
  have hzetaMul : riemannZeta s * Complex.Gammaℝ s =
      completedRiemannZeta s :=
    (eq_div_iff hGammaℝ).mp hzetaCompleted
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, ← hzetaMul]
  ring

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℝ s ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  have hre := congrArg Complex.re hn
  norm_num at hre
  nlinarith

lemma differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnotPole : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    nlinarith
  have hexponent : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by
    fun_prop
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hexponent.const_cpow (Or.inl hpi)
  have hGamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) hnotPole).comp s (by fun_prop)
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
  exact hpow.mul hGamma

/-- Exact logarithmic derivative of the pole-cleared xi function on the
zero-free half-plane. -/
theorem logDeriv_riemannXi_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 +
          deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaℝ := Gammaℝ_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs.le
  have hGammaℝDiff :=
    differentiableAt_Gammaℝ_of_re_pos (show 0 < s.re by linarith)
  have hzetaDiff := differentiableAt_riemannZeta hs1
  have hlocal : riemannXi =ᶠ[nhds s]
      (fun z : ℂ => z * (1 - z) * Complex.Gammaℝ z * riemannZeta z) := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re hz
  rw [(logDeriv_congr_nhds hlocal).self_of_nhds]
  have hlinear :
      logDeriv (fun z : ℂ => z * (1 - z)) s =
        1 / s + 1 / (s - 1) := by
    have hderivSub : deriv (fun z : ℂ => 1 - z) s = -1 :=
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv.trans (by ring)
    rw [logDeriv_mul (f := fun z : ℂ => z)
      (g := fun z : ℂ => 1 - z) s hs0 h1s (by fun_prop) (by fun_prop)]
    simp only [logDeriv_apply, deriv_id'', hderivSub]
    field_simp [hs0, hs1]
    ring
  have hcompleted :
      logDeriv (fun z : ℂ => z * (1 - z) * Complex.Gammaℝ z) s =
        1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
          Complex.digamma (s / 2) / 2 := by
    rw [logDeriv_mul (f := fun z : ℂ => z * (1 - z))
      (g := Complex.Gammaℝ) s (mul_ne_zero hs0 h1s) hGammaℝ
      ((by fun_prop) : DifferentiableAt ℂ (fun z : ℂ => z * (1 - z)) s)
      hGammaℝDiff]
    rw [hlinear, logDeriv_Gammaℝ (show 0 < s.re by linarith)]
    ring
  rw [logDeriv_mul
    (f := fun z : ℂ => z * (1 - z) * Complex.Gammaℝ z)
    (g := riemannZeta) s
    (mul_ne_zero (mul_ne_zero hs0 h1s) hGammaℝ)
    hzeta
    (((by fun_prop) : DifferentiableAt ℂ (fun z : ℂ => z * (1 - z)) s).mul
      hGammaℝDiff)
    hzetaDiff]
  rw [hcompleted, logDeriv_apply]

/-- Rearranged in the sign convention of the prime-side contour integral. -/
theorem negLogDeriv_riemannZeta_eq_completed_terms
    {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      -deriv riemannXi s / riemannXi s +
        1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
          Complex.digamma (s / 2) / 2 := by
  have h := logDeriv_riemannXi_of_one_lt_re hs
  rw [logDeriv_apply] at h
  rw [neg_div, neg_div]
  rw [h]
  ring

/-- Spectral-coordinate form on the safe line `s = 3/2 + I*u`. -/
theorem negLogDeriv_riemannZeta_safeLine_decomposition (u : ℝ) :
    -deriv riemannZeta (3 / 2 + Complex.I * (u : ℂ)) /
        riemannZeta (3 / 2 + Complex.I * (u : ℂ)) =
      -deriv riemannXi (3 / 2 + Complex.I * (u : ℂ)) /
          riemannXi (3 / 2 + Complex.I * (u : ℂ)) +
        1 / (3 / 2 + Complex.I * (u : ℂ)) +
        1 / (3 / 2 + Complex.I * (u : ℂ) - 1) -
        Complex.log Real.pi / 2 +
        Complex.digamma
          ((3 / 2 + Complex.I * (u : ℂ)) / 2) / 2 :=
  negLogDeriv_riemannZeta_eq_completed_terms (by norm_num)

end

end RiemannGaussian
