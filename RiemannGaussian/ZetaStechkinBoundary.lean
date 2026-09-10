/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerBoundaryControl
import RiemannGaussian.ZetaStechkinPhaseBudget
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Exact Stechkin response at the Euler boundary

The actual zeta pole is removed before the limit toward `sigma=1`.
The full complex response is retained, and its real part has a uniform
summable dominator for every admissible real-frequency family. The
regularized complete prime work therefore has an Abel limit, including
the zero frequency and infinite spectra accumulating at zero.

At the boundary the exact signed completion and all actual reflection
pairs remain. The selected right-half zero retains its full source.
No positivity is asserted for the pole-removed arithmetic work.
-/

namespace RiemannGaussian
noncomputable section
open Complex Set Filter
open scoped Topology

/-- The full complex response after removing the zeta pole from both
sampling lines, before taking a real part or a boundary limit. -/
def zetaStechkinPoleRemoved (σ t : ℝ) : ℂ :=
  -logDeriv riemannZeta₁ ((σ : ℂ) + I * t) +
    (zetaStechkinWeight σ : ℂ) *
      logDeriv riemannZeta₁ ((zetaStechkinAbscissa σ : ℝ) + I * t)

/-- The exact complex completion comparison, without replacing it by
a logarithmic height allowance. -/
def zetaStechkinRegularComparison (σ t : ℝ) : ℂ :=
  zetaGlobalRegularCorrection ((σ : ℂ) + I * t) -
    (zetaStechkinWeight σ : ℂ) *
      zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * t)

private theorem abscissa_mem {σ : ℝ} (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2) :
    1 ≤ zetaStechkinAbscissa σ ∧ zetaStechkinAbscissa σ ≤ 3 := by
  have ht := lt_zetaStechkinAbscissa hσ
  have he := zetaStechkinAbscissa_quadratic σ
  constructor
  · linarith
  · nlinarith [sq_nonneg (σ - 1), sq_nonneg (zetaStechkinAbscissa σ - 3)]

/-- The exact boundary identity includes the filled pole and the whole
actual zero spectrum, with its genuine multiplicities. -/
theorem zetaStechkinPoleRemoved_add_zeroMass_eq {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    (zetaStechkinPoleRemoved σ t).re +
      (∑' rho : NontrivialZetaZero, zetaStechkinPoissonSummand σ t rho) =
        (zetaStechkinRegularComparison σ t).re := by
  have hs := zeta_poleRemoved_global_real_budget (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have ht := zeta_poleRemoved_global_real_budget
    (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * t)
    (by simpa using hσ.trans (lt_zetaStechkinAbscissa hσ).le)
  rw [tsum_zetaStechkinPoissonSummand hσ]
  simp only [zetaStechkinPoleRemoved, zetaStechkinRegularComparison,
    Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs ht ⊢
  linear_combination hs - zetaStechkinWeight σ * ht

/-- On an Euler-product line, this response is precisely the original
arithmetic work minus its exact pole comparison. -/
theorem zetaStechkinPoleRemoved_eq_prime_sub_pole {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (zetaStechkinPoleRemoved σ t).re =
      (-logDeriv riemannZeta ((σ : ℂ) + I * t)).re -
        zetaStechkinWeight σ * (-logDeriv riemannZeta
          ((zetaStechkinAbscissa σ : ℝ) + I * t)).re - zetaStechkinPoleBudget σ t := by
  have he := zeta_stechkin_real_budget hσ t
  have hr := zetaStechkinPoleRemoved_add_zeroMass_eq hσ.le t
  simp only [zetaStechkinRegularComparison, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  linarith

/-- The complete complex response is continuous in the sampling line
through the Euler boundary at every fixed real ordinate. -/
theorem continuousAt_zetaStechkinPoleRemoved {σ : ℝ} (hσ : 1 ≤ σ) (t : ℝ) :
    ContinuousAt (fun u => zetaStechkinPoleRemoved u t) σ := by
  have hτ : Continuous zetaStechkinAbscissa := by unfold zetaStechkinAbscissa; fun_prop
  have hc : ContinuousAt zetaStechkinWeight σ := by
    unfold zetaStechkinWeight
    apply continuousAt_id.div ((continuousAt_const.mul hτ.continuousAt).sub continuousAt_const)
    have ht := lt_zetaStechkinAbscissa hσ
    dsimp
    linarith
  have hfirst := analyticAt_logDeriv_riemannZeta₁_of_one_le_re
    (s := (σ : ℂ) + I * t) (by simpa using hσ)
  have hsecond := analyticAt_logDeriv_riemannZeta₁_of_one_le_re
    (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * t)
    (by simpa using hσ.trans (lt_zetaStechkinAbscissa hσ).le)
  have h1 : ContinuousAt (fun u : ℝ => logDeriv riemannZeta₁ ((u : ℂ) + I * t)) σ :=
    hfirst.continuousAt.comp (f := fun u : ℝ => (u : ℂ) + I * t) (by fun_prop)
  have h2 : ContinuousAt (fun u : ℝ => logDeriv riemannZeta₁
      ((zetaStechkinAbscissa u : ℝ) + I * t)) σ :=
    hsecond.continuousAt.comp
      (f := fun u : ℝ => ((zetaStechkinAbscissa u : ℝ) : ℂ) + I * t) (by fun_prop)
  exact h1.neg.add ((Complex.continuous_ofReal.continuousAt.comp hc).mul h2)

/-- One constant controls the real pole-removed response at every
height uniformly as the sampling line tends to one. -/
theorem exists_zetaStechkinPoleRemoved_euler_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 → ∀ t : ℝ,
      |(zetaStechkinPoleRemoved σ t).re| ≤ C * zetaEulerLogHeight t := by
  obtain ⟨C, hC, hb⟩ := exists_re_logDeriv_riemannZeta₁_euler_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro σ hσ hσ2 t
  have ht := abscissa_mem hσ hσ2
  have h1 := hb σ hσ (by linarith) t
  have h2 := hb (zetaStechkinAbscissa σ) ht.1 ht.2 t
  have hc := zetaStechkinWeight_mem_Ioo hσ
  simp only [zetaStechkinPoleRemoved, Complex.add_re, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| +
        zetaStechkinWeight σ *
          |(logDeriv riemannZeta₁ ((zetaStechkinAbscissa σ : ℝ) + I * t)).re| := by
      simpa only [abs_neg, abs_mul, abs_of_pos hc.1] using
        abs_add_le (-(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re)
          (zetaStechkinWeight σ *
            (logDeriv riemannZeta₁ ((zetaStechkinAbscissa σ : ℝ) + I * t)).re)
    _ ≤ 2 * C * zetaEulerLogHeight t := by
      have hh := mul_le_mul_of_nonneg_left h2 hc.1.le
      have hL := three_lt_zetaEulerLogHeight t
      nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) (mul_nonneg hC.le (by linarith : 0 ≤ zetaEulerLogHeight t))]

/-- The exact real completion comparison has a uniform logarithmic
dominator on the same closed interval of sampling lines. -/
theorem abs_re_zetaStechkinRegularComparison_euler_le {σ : ℝ}
    (hσ : 1 ≤ σ) (hσ2 : σ ≤ 2) (t : ℝ) :
    |(zetaStechkinRegularComparison σ t).re| ≤ 4 * zetaEulerLogHeight t := by
  have ht := abscissa_mem hσ hσ2
  have h1 := abs_re_zetaGlobalRegularCorrection_euler_le hσ (by linarith : σ ≤ 3) (t := t)
  have h2 := abs_re_zetaGlobalRegularCorrection_euler_le ht.1 ht.2 (t := t)
  have hc := zetaStechkinWeight_mem_Ioo hσ
  simp only [zetaStechkinRegularComparison, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := abs_sub (zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re
    (zetaStechkinWeight σ *
      (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * t)).re)
  rw [abs_mul, abs_of_pos hc.1] at h
  have hh := mul_le_mul_of_nonneg_left h2 hc.1.le
  have hL := three_lt_zetaEulerLogHeight t
  nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) (by linarith : 0 ≤ zetaEulerLogHeight t)]

end
end RiemannGaussian
