import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedExpanding

/-!
# Scalar positivity of the canonical selected boundary functional

The canonical Cauchy--Green exhaustion produces a complex arithmetic
boundary-minus-bulk functional.  This file proves that the finite functional
is in fact purely imaginary and identifies its imaginary part with `2*pi`
times the real selected heat-residue window.

The resulting scalar functional is nonnegative, monotone along the canonical
quantitative heights, and strictly positive as soon as a window contains an
off-axis zero.  Its finite vanishing is exactly emptiness of that selected
window, and its limit is `2*pi` times the complete RH-equivalent heat total.
Thus neither complex cancellation nor cancellation between later finite
stages can remove an off-axis contribution.  The still-open task is to derive
vanishing from unconditional arithmetic estimates rather than from the
spectral identity itself.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- Every finite selected residue window is real when regarded as a complex
number. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_im_eq_zero
    (x tau T : ℝ) :
    (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).im = 0 := by
  unfold suzukiChebyshevLaplaceBoundaryHeatResidueWindow
  rw [Complex.im_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_im,
    Finset.sum_const_zero]

/-- Enlarging a nonnegative spectral height window can only increase the real
selected heat-residue total. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_mono
    (x tau : ℝ) {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) :
    (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re ≤
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau U).re := by
  have hU : 0 ≤ U := hT.trans hTU
  have hsubset : spectralZetaZeroWindow T ⊆ spectralZetaZeroWindow U := by
    intro rho hrho
    apply (mem_spectralZetaZeroWindow hU rho).mpr
    exact ((mem_spectralZetaZeroWindow hT rho).mp hrho).trans hTU
  unfold suzukiChebyshevLaplaceBoundaryHeatResidueWindow
  simp only [Complex.re_sum,
    suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_re]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun rho _ _ =>
    zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau rho

/-- A finite selected heat-residue window has zero real part exactly when the
corresponding selected zero window is empty. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_eq_zero_iff
    (x tau T : ℝ) :
    (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re = 0 ↔
      spectralUpperZetaZeroWindow T = ∅ := by
  constructor
  · intro hzero
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨rho, hrho⟩
    have hpos :=
      suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_pos_of_mem_upper
        x tau T hrho
    rw [hzero] at hpos
    exact (lt_self_iff_false 0).mp hpos
  · intro hempty
    rw [suzukiChebyshevLaplaceBoundaryHeatResidueWindow_eq_selected,
      hempty]
    simp

/-- The quantitative zero-free spectral heights form a monotone cofinal
sequence. -/
theorem monotone_quantitativeSpectralBoundaryTruncation :
    Monotone quantitativeSpectralBoundaryTruncation := by
  intro n m hnm
  rcases eq_or_lt_of_le hnm with rfl | hlt
  · rfl
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    calc
      quantitativeSpectralBoundaryTruncation n ≤ (n : ℝ) + 1 :=
        (quantitativeSpectralBoundaryTruncation_spec n).2.1.le
      _ ≤ (m : ℝ) := hcast
      _ ≤ quantitativeSpectralBoundaryTruncation m :=
        (quantitativeSpectralBoundaryTruncation_spec m).1.le

/-- The canonical arithmetic boundary-minus-bulk functional has zero real
part at every finite stage. -/
theorem quantitativeSelectedLaplaceBoundarySubArea_re_eq_zero
    (x tau : ℝ) (n : ℕ) :
    (rectangularBoundaryIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).re =
      0 := by
  rw [← quantitativeSelectedLaplaceBoundaryHeat_finiteCauchyGreen x tau n]
  simp [Complex.mul_re, Complex.mul_im,
    suzukiChebyshevLaplaceBoundaryHeatResidueWindow_im_eq_zero]

/-- The imaginary part of the canonical finite arithmetic functional is
exactly `2*pi` times the real selected heat-residue window. -/
theorem quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul
    (x tau : ℝ) (n : ℕ) :
    (rectangularBoundaryIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).im =
      2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re := by
  rw [← quantitativeSelectedLaplaceBoundaryHeat_finiteCauchyGreen x tau n]
  simp [Complex.mul_re, Complex.mul_im]

/-- The canonical finite arithmetic scalar functional is nonnegative. -/
theorem quantitativeSelectedLaplaceBoundarySubArea_im_nonneg
    (x tau : ℝ) (n : ℕ) :
    0 ≤
      (rectangularBoundaryIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).im := by
  rw [quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul]
  exact mul_nonneg (by positivity)
    (suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_nonneg x tau _)

/-- The canonical arithmetic scalar functional is monotone along the
quantitative height exhaustion. -/
theorem monotone_quantitativeSelectedLaplaceBoundarySubArea_im
    (x tau : ℝ) :
    Monotone fun n : ℕ =>
      (rectangularBoundaryIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).im := by
  intro n m hnm
  dsimp only
  rw [quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul,
    quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_mono
  · exact quantitativeSpectralBoundaryTruncation_nonneg n
  · exact monotone_quantitativeSpectralBoundaryTruncation hnm

/-- A selected off-axis zero in a canonical window makes the corresponding
arithmetic scalar functional strictly positive. -/
theorem quantitativeSelectedLaplaceBoundarySubArea_im_pos_of_mem_upper
    (x tau : ℝ) (n : ℕ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n)) :
    0 <
      (rectangularBoundaryIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).im := by
  rw [quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul]
  exact mul_pos (by positivity)
    (suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_pos_of_mem_upper
      x tau _ hrho)

/-- Finite vanishing of the canonical arithmetic scalar is exactly emptiness
of that stage's selected zero window. -/
theorem quantitativeSelectedLaplaceBoundarySubArea_im_eq_zero_iff
    (x tau : ℝ) (n : ℕ) :
    (rectangularBoundaryIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)).im =
      0 ↔
    spectralUpperZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n) = ∅ := by
  rw [quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul]
  constructor
  · intro hzero
    have hscale : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hresidue :
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hscale
    exact
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_eq_zero_iff
        x tau _).mp hresidue
  · intro hempty
    have hresidue :
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re = 0 :=
      (suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_eq_zero_iff
        x tau _).mpr hempty
    rw [hresidue, mul_zero]

/-- The canonical nonnegative arithmetic scalars converge to `2*pi` times the
complete selected boundary-heat total. -/
theorem tendsto_quantitativeSelectedLaplaceBoundarySubArea_im
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (rectangularBoundaryIntegral
              (selectedLaplaceLeftBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (selectedLaplaceRightBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (-quantitativeSpectralBoundaryTruncation n)
              (quantitativeSpectralBoundaryTruncation n)
              (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
            rectangularAreaIntegral
              (selectedLaplaceLeftBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (selectedLaplaceRightBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (-quantitativeSpectralBoundaryTruncation n)
              (quantitativeSpectralBoundaryTruncation n)
              (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
                x tau)).im)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hwindowComplex :=
    (tendsto_suzukiChebyshevLaplaceBoundaryHeatResidueWindow x htau).comp
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hwindowRe : Tendsto
      (fun n : ℕ =>
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re)
      atTop
      (𝓝 (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hwindowComplex
    change Tendsto
      (fun n : ℕ =>
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re)
      atTop
      (𝓝 (riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) at hre
    exact hre
  have hscaled : Tendsto
      (fun n : ℕ => 2 * Real.pi *
        (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n)).re)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) :=
    tendsto_const_nhds.mul hwindowRe
  apply hscaled.congr'
  filter_upwards with n
  exact
    (quantitativeSelectedLaplaceBoundarySubArea_im_eq_two_pi_mul
      x tau n).symm

/-- Convergence of the canonical nonnegative arithmetic scalar to zero is
equivalent to RH.  The unconditional proof of this limit remains open. -/
theorem tendsto_quantitativeSelectedLaplaceBoundarySubArea_im_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (rectangularBoundaryIntegral
              (selectedLaplaceLeftBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (selectedLaplaceRightBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (-quantitativeSpectralBoundaryTruncation n)
              (quantitativeSpectralBoundaryTruncation n)
              (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
            rectangularAreaIntegral
              (selectedLaplaceLeftBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (selectedLaplaceRightBoundary
                (quantitativeSpectralBoundaryTruncation n))
              (-quantitativeSpectralBoundaryTruncation n)
              (quantitativeSpectralBoundaryTruncation n)
              (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource
                x tau)).im)
      atTop (𝓝 0) ↔ RiemannHypothesis := by
  have hlimit := tendsto_quantitativeSelectedLaplaceBoundarySubArea_im x htau
  constructor
  · intro hzero
    have hscaled :
        2 * Real.pi * riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      tendsto_nhds_unique hlimit hzero
    have hscale : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (mul_eq_zero.mp hscaled).resolve_left hscale
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp htotal
  · intro hRH
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    simpa only [htotal, mul_zero] using hlimit

end

end RiemannGaussian
