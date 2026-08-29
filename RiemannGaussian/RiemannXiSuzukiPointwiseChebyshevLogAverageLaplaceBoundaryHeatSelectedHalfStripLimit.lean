import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStrip

/-!
# The complete detector limit on separated near-edge half-strips

The preceding near-edge construction gives finite rectangles whose horizontal
sides converge to the two edges of the shifted critical strip, whose vertical
heights tend to infinity, and whose boundaries avoid the complete bounded
divisor.  Its residue window is deliberately filtered by the rectangle, so it
is not one of the nested height windows used earlier.

This file proves that no spectral mass is lost by that filtering.  Every fixed
upper off-axis zero eventually enters the rectangles, non-upper zeros
contribute identically zero, and the absolutely summable complete heat-residue
series supplies a uniform dominator.  Dominated convergence therefore sends
the filtered finite sums to the complete RH-equivalent heat total.  Combining
this with finite Cauchy--Green yields the first global arithmetic
boundary-minus-bulk limit on contours that genuinely approach both strip
edges.  No claim is made here that this limit vanishes unconditionally.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The finite heat-residue sum selected by the separated near-edge rectangle
at stage `n`. -/
def separatedSelectedBoundaryHeatResidueWindow
    (x tau : ℝ) (n : ℕ) : ℂ :=
  ∑ rho ∈ separatedSelectedZetaZeroWindow n,
    suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho

/-- On the separated selected window, the arithmetic residue is exactly the
spectral heat kernel weighted by zero multiplicity. -/
theorem separatedSelectedBoundaryHeatResidueWindow_eq_kernel_sum
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedBoundaryHeatResidueWindow x tau n =
      ∑ rho ∈ separatedSelectedZetaZeroWindow n,
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ) := by
  unfold separatedSelectedBoundaryHeatResidueWindow
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [suzukiChebyshevLaplaceBoundaryHeatResidue]
  rw [if_pos]
  exact
    selectedLaplaceZeroCoordinate_re_lt_zero_of_mem
      (mem_separatedSelectedZetaZeroWindow.mp hrho).1

/-- Every separated selected finite residue sum is real. -/
theorem separatedSelectedBoundaryHeatResidueWindow_im_eq_zero
    (x tau : ℝ) (n : ℕ) :
    (separatedSelectedBoundaryHeatResidueWindow x tau n).im = 0 := by
  unfold separatedSelectedBoundaryHeatResidueWindow
  rw [Complex.im_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_im,
    Finset.sum_const_zero]

/-- The real part of every separated selected finite residue sum is
nonnegative. -/
theorem separatedSelectedBoundaryHeatResidueWindow_re_nonneg
    (x tau : ℝ) (n : ℕ) :
    0 ≤ (separatedSelectedBoundaryHeatResidueWindow x tau n).re := by
  unfold separatedSelectedBoundaryHeatResidueWindow
  rw [Complex.re_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_re]
  exact Finset.sum_nonneg fun rho _ =>
    zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau rho

/-- A separated selected finite residue sum is strictly positive whenever its
window contains a zero. -/
theorem separatedSelectedBoundaryHeatResidueWindow_re_pos_of_mem
    (x tau : ℝ) (n : ℕ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ separatedSelectedZetaZeroWindow n) :
    0 < (separatedSelectedBoundaryHeatResidueWindow x tau n).re := by
  unfold separatedSelectedBoundaryHeatResidueWindow
  rw [Complex.re_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_re]
  apply Finset.sum_pos'
  · exact fun sigma _ =>
      zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau sigma
  · refine ⟨rho, hrho, ?_⟩
    exact zetaUpperHyperbolicBoundaryHeatSummand_pos x tau rho
      (mem_spectralUpperZetaZeroWindow.mp
        (mem_separatedSelectedZetaZeroWindow.mp hrho).1).2

/-- The filtered finite residue sums on the separated near-edge exhaustion
converge to the complete upper boundary-heat total. -/
theorem tendsto_separatedSelectedBoundaryHeatResidueWindow
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedBoundaryHeatResidueWindow x tau) atTop
      (𝓝 (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ)) := by
  let f : ℕ → NontrivialZetaZero → ℂ := fun n rho =>
    if rho ∈ separatedSelectedZetaZeroWindow n then
      suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho
    else 0
  have hpoint : ∀ rho : NontrivialZetaZero,
      Tendsto (fun n : ℕ => f n rho) atTop
        (𝓝 (suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
    intro rho
    by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_mem_separatedSelectedZetaZeroWindow
        rho hupper] with n hn
      dsimp only [f]
      rw [if_pos hn]
    · have hnotMem : ∀ n : ℕ,
          rho ∉ separatedSelectedZetaZeroWindow n := by
        intro n hmem
        exact hupper (mem_spectralUpperZetaZeroWindow.mp
          (mem_separatedSelectedZetaZeroWindow.mp hmem).1).2
      have hresidue :
          suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho = 0 := by
        rw [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
          riemannXiUpperHyperbolicBoundaryHeatResidue,
          zetaUpperHyperbolicBoundaryHeatSummand, if_neg hupper]
        norm_num
      simp only [f, hnotMem, if_false, hresidue]
      exact tendsto_const_nhds
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ rho : NontrivialZetaZero,
      ‖f n rho‖ ≤
        ‖suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho‖ := by
    exact Eventually.of_forall fun n rho => by
      dsimp only [f]
      split_ifs <;> simp
  have hsumNorm : Summable fun rho : NontrivialZetaZero =>
      ‖suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho‖ :=
    (hasSum_suzukiChebyshevLaplaceBoundaryHeatResidue x htau).summable.norm
  have hlimit := tendsto_tsum_of_dominated_convergence hsumNorm hpoint hbound
  have htotal : (∑' rho : NontrivialZetaZero,
      suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho) =
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) :=
    (hasSum_suzukiChebyshevLaplaceBoundaryHeatResidue x htau).tsum_eq
  rw [htotal] at hlimit
  apply hlimit.congr'
  filter_upwards with n
  rw [tsum_eq_sum (s := separatedSelectedZetaZeroWindow n) (by
    intro rho hnot
    dsimp only [f]
    rw [if_neg hnot])]
  unfold separatedSelectedBoundaryHeatResidueWindow
  apply Finset.sum_congr rfl
  intro rho hrho
  dsimp only [f]
  rw [if_pos hrho]

/-- The finite Cauchy--Green identity expressed using the separated selected
residue-window sum. -/
theorem separatedSelectedLaplaceBoundaryHeat_residueWindow_eq_boundary_sub_area
    (x tau : ℝ) (n : ℕ) :
    (2 * Real.pi * Complex.I) *
        separatedSelectedBoundaryHeatResidueWindow x tau n =
      rectangularBoundaryIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) := by
  rw [separatedSelectedBoundaryHeatResidueWindow_eq_kernel_sum]
  exact separatedSelectedLaplaceBoundaryHeat_residue_eq_boundary_sub_area
    x tau n

/-- Along the genuine near-edge half-strip exhaustion, the actual arithmetic
boundary-minus-bulk functional converges to `2*pi*i` times the complete
upper boundary-heat total. -/
theorem tendsto_separatedSelectedLaplaceBoundarySubArea
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        rectangularBoundaryIntegral
            (selectedLaplaceSeparatedLeftBoundary n)
            (selectedLaplaceSeparatedRightBoundary n)
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceSeparatedLeftBoundary n)
            (selectedLaplaceSeparatedRightBoundary n)
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau))
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  have hscaled : Tendsto
      (fun n : ℕ => (2 * Real.pi * Complex.I) *
        separatedSelectedBoundaryHeatResidueWindow x tau n)
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) :=
    tendsto_const_nhds.mul
      (tendsto_separatedSelectedBoundaryHeatResidueWindow x htau)
  apply hscaled.congr'
  filter_upwards with n
  exact
    separatedSelectedLaplaceBoundaryHeat_residueWindow_eq_boundary_sub_area
      x tau n

end

end RiemannGaussian
