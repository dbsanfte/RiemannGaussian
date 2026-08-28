import RiemannGaussian.RiemannXiSuzukiFiniteGram

/-!
# Convergence of Suzuki's spectral coefficient windows

The complete Suzuki coefficient sequence is already an unconditional element
of `ℓ²` on the genuine xi divisor.  This file truncates it by the same
symmetric spectral windows used in the finite zero-function expansion and
proves norm convergence to the complete vector.

This is the coefficient-space half of the desired infinite synthesis passage.
Transporting the convergence through the normalized zero-function family is a
separate bounded-synthesis/Gram estimate and is not assumed here.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The finite coordinate truncation of Suzuki's complete `ℓ²` coefficient
vector over one symmetric genuine-zero window. -/
def riemannXiSuzukiSpectralCoefficientWindowVector
    (t T : ℝ) : ℓ²(NontrivialZetaZero, ℂ) :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    lp.single 2 rho (zetaSuzukiSpectralCoefficientFeature t rho)

/-- A coordinate of the truncated vector is the full coefficient inside the
window and zero outside it. -/
theorem riemannXiSuzukiSpectralCoefficientWindowVector_apply
    (t T : ℝ) (rho : NontrivialZetaZero) :
    riemannXiSuzukiSpectralCoefficientWindowVector t T rho =
      if rho ∈ spectralZetaZeroWindow T then
        zetaSuzukiSpectralCoefficientFeature t rho
      else 0 := by
  unfold riemannXiSuzukiSpectralCoefficientWindowVector
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply,
    Finset.sum_pi_single]

/-- The squared norm of a coefficient window is exactly the corresponding
finite sum of positive coefficient energies. -/
theorem norm_sq_riemannXiSuzukiSpectralCoefficientWindowVector
    (t T : ℝ) :
    ‖riemannXiSuzukiSpectralCoefficientWindowVector t T‖ ^ 2 =
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaSuzukiSpectralCoefficientEnergy t rho := by
  have hnorm := lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (by norm_num)
    (zetaSuzukiSpectralCoefficientFeature t)
    (spectralZetaZeroWindow T)
  simpa only [riemannXiSuzukiSpectralCoefficientWindowVector,
    ENNReal.toReal_ofNat, Real.rpow_two, Complex.sq_norm,
    normSq_zetaSuzukiSpectralCoefficientFeature] using hnorm

/-- The exact squared truncation error is the complete coefficient energy
minus the finite-window energy. -/
theorem norm_sq_riemannXiSuzukiSpectralCoefficientVector_sub_window
    (t T : ℝ) :
    ‖riemannXiSuzukiSpectralCoefficientVector t -
        riemannXiSuzukiSpectralCoefficientWindowVector t T‖ ^ 2 =
      ‖riemannXiSuzukiSpectralCoefficientVector t‖ ^ 2 -
        ∑ rho ∈ spectralZetaZeroWindow T,
          zetaSuzukiSpectralCoefficientEnergy t rho := by
  have herror := lp.norm_compl_sum_single
    (p := (2 : ℝ≥0∞)) (by norm_num)
    (riemannXiSuzukiSpectralCoefficientVector t)
    (spectralZetaZeroWindow T)
  simpa only [riemannXiSuzukiSpectralCoefficientWindowVector,
    riemannXiSuzukiSpectralCoefficientVector,
    ENNReal.toReal_ofNat, Real.rpow_two, Complex.sq_norm,
    normSq_zetaSuzukiSpectralCoefficientFeature] using herror

/-- The genuine symmetric spectral windows converge in `ℓ²` norm to Suzuki's
complete coefficient vector at every real screw time. -/
theorem tendsto_riemannXiSuzukiSpectralCoefficientWindowVector
    (t : ℝ) :
    Tendsto (fun T : ℝ ↦
      riemannXiSuzukiSpectralCoefficientWindowVector t T) atTop
        (nhds (riemannXiSuzukiSpectralCoefficientVector t)) := by
  have hsum := lp.hasSum_single ENNReal.ofNat_ne_top
    (riemannXiSuzukiSpectralCoefficientVector t)
  change Tendsto
    (fun T : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        lp.single 2 rho
          (riemannXiSuzukiSpectralCoefficientVector t rho)) atTop
      (nhds (riemannXiSuzukiSpectralCoefficientVector t))
  exact hsum.comp tendsto_spectralZetaZeroWindow_atTop

end

end RiemannGaussian
