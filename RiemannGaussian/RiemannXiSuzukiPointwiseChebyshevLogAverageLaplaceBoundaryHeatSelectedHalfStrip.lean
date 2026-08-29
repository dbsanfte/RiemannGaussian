import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedScalar

/-!
# A genuine near-edge selected half-strip exhaustion

The finite-extremum rectangles constructed earlier contain the complete
selected height window, but their horizontal sides depend directly on the
unknown extreme zeros and need not approach the edges of the shifted critical
strip.  That geometry is exact but poorly suited to independent arithmetic
estimates.

This file constructs a second, genuinely expanding exhaustion.  At stage
`n`, the left side is chosen inside a width `1/(n+4)` of `Re p=-1/2`, the
right side inside the same width of `Re p=0`, and the vertical sides use the
existing cofinal quantitative zero-free height.  A finite-set gap theorem
chooses both horizontal sides with an explicit positive distance from every
zero in the bounded-height divisor.  The resulting endpoints converge to the
two strip edges.

The selected divisor is now filtered by actual membership in this rectangle.
Every chosen zero is strictly inside, every other bounded-height zero is
genuinely outside, and every fixed off-axis selected zero eventually enters
the exhaustion.  Lean then proves the exact finite arithmetic
boundary-minus-bulk identity on each near-edge rectangle.  Passing the
filtered positive sums to the complete heat detector is the next limit step.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The deterministic width of each horizontal edge-selection interval. -/
def selectedLaplaceEdgeWidth (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 4)

/-- Every horizontal edge-selection interval has positive width. -/
theorem selectedLaplaceEdgeWidth_pos (n : ℕ) :
    0 < selectedLaplaceEdgeWidth n := by
  unfold selectedLaplaceEdgeWidth
  positivity

/-- The edge width is at most one quarter, keeping the two selection
intervals ordered. -/
theorem selectedLaplaceEdgeWidth_le_quarter (n : ℕ) :
    selectedLaplaceEdgeWidth n ≤ 1 / 4 := by
  unfold selectedLaplaceEdgeWidth
  rw [div_le_iff₀ (by positivity)]
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith

/-- The horizontal edge-selection widths tend to zero. -/
theorem tendsto_selectedLaplaceEdgeWidth_zero :
    Tendsto selectedLaplaceEdgeWidth atTop (𝓝 0) := by
  have hdenominator : Tendsto (fun n : ℕ => (n : ℝ) + 4)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hinverse := tendsto_inv_atTop_zero.comp hdenominator
  exact hinverse.congr' (Eventually.of_forall fun n => by
    simp [selectedLaplaceEdgeWidth, one_div])

/-- The finite real coordinates that the two horizontal sides must avoid at
stage `n`. -/
def selectedLaplaceRealBoundaryObstructions (n : ℕ) : Finset ℝ :=
  (spectralZetaZeroWindow (quantitativeSpectralBoundaryTruncation n)).image
    fun rho => (suzukiChebyshevLaplaceZeroCoordinate rho).re

/-- The explicit finite-gap separation radius available to both horizontal
sides. -/
def selectedLaplaceEdgeSeparation (n : ℕ) : ℝ :=
  selectedLaplaceEdgeWidth n /
    (3 * (((selectedLaplaceRealBoundaryObstructions n).card : ℝ) + 2))

/-- Every horizontal finite-gap separation radius is positive. -/
theorem selectedLaplaceEdgeSeparation_pos (n : ℕ) :
    0 < selectedLaplaceEdgeSeparation n := by
  unfold selectedLaplaceEdgeSeparation
  exact div_pos (selectedLaplaceEdgeWidth_pos n) (by positivity)

/-- There is a left side near `-1/2` separated from every bounded-height zero
real coordinate by the explicit finite-gap radius. -/
theorem exists_selectedLaplaceLeftBoundary (n : ℕ) :
    ∃ l : ℝ,
      -(1 / 2 : ℝ) < l ∧
      l < -(1 / 2 : ℝ) + selectedLaplaceEdgeWidth n ∧
      ∀ y ∈ selectedLaplaceRealBoundaryObstructions n,
        selectedLaplaceEdgeSeparation n ≤ |l - y| := by
  obtain ⟨l, hl0, hl1, hsep⟩ :=
    exists_real_in_Ioo_avoiding_finset
      (selectedLaplaceRealBoundaryObstructions n)
      (show -(1 / 2 : ℝ) <
          -(1 / 2 : ℝ) + selectedLaplaceEdgeWidth n by
        linarith [selectedLaplaceEdgeWidth_pos n])
  refine ⟨l, hl0, hl1, ?_⟩
  intro y hy
  simpa [selectedLaplaceEdgeSeparation] using hsep y hy

/-- A fixed separated left side in the shrinking interval next to
`Re p=-1/2`. -/
def selectedLaplaceSeparatedLeftBoundary (n : ℕ) : ℝ :=
  Classical.choose (exists_selectedLaplaceLeftBoundary n)

/-- Location and zero-separation specification of the chosen left side. -/
theorem selectedLaplaceSeparatedLeftBoundary_spec (n : ℕ) :
    -(1 / 2 : ℝ) < selectedLaplaceSeparatedLeftBoundary n ∧
      selectedLaplaceSeparatedLeftBoundary n <
        -(1 / 2 : ℝ) + selectedLaplaceEdgeWidth n ∧
      ∀ y ∈ selectedLaplaceRealBoundaryObstructions n,
        selectedLaplaceEdgeSeparation n ≤
          |selectedLaplaceSeparatedLeftBoundary n - y| :=
  Classical.choose_spec (exists_selectedLaplaceLeftBoundary n)

/-- There is a right side near zero separated from every bounded-height zero
real coordinate by the explicit finite-gap radius. -/
theorem exists_selectedLaplaceRightBoundary (n : ℕ) :
    ∃ r : ℝ,
      -selectedLaplaceEdgeWidth n < r ∧ r < 0 ∧
      ∀ y ∈ selectedLaplaceRealBoundaryObstructions n,
        selectedLaplaceEdgeSeparation n ≤ |r - y| := by
  obtain ⟨r, hr0, hr1, hsep⟩ :=
    exists_real_in_Ioo_avoiding_finset
      (selectedLaplaceRealBoundaryObstructions n)
      (show -selectedLaplaceEdgeWidth n < 0 by
        linarith [selectedLaplaceEdgeWidth_pos n])
  refine ⟨r, hr0, hr1, ?_⟩
  intro y hy
  simpa [selectedLaplaceEdgeSeparation] using hsep y hy

/-- A fixed separated right side in the shrinking interval next to the
critical line `Re p=0`. -/
def selectedLaplaceSeparatedRightBoundary (n : ℕ) : ℝ :=
  Classical.choose (exists_selectedLaplaceRightBoundary n)

/-- Location and zero-separation specification of the chosen right side. -/
theorem selectedLaplaceSeparatedRightBoundary_spec (n : ℕ) :
    -selectedLaplaceEdgeWidth n <
        selectedLaplaceSeparatedRightBoundary n ∧
      selectedLaplaceSeparatedRightBoundary n < 0 ∧
      ∀ y ∈ selectedLaplaceRealBoundaryObstructions n,
        selectedLaplaceEdgeSeparation n ≤
          |selectedLaplaceSeparatedRightBoundary n - y| :=
  Classical.choose_spec (exists_selectedLaplaceRightBoundary n)

/-- The separated near-edge horizontal sides are strictly ordered. -/
theorem selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary (n : ℕ) :
    selectedLaplaceSeparatedLeftBoundary n <
      selectedLaplaceSeparatedRightBoundary n := by
  have hl := (selectedLaplaceSeparatedLeftBoundary_spec n).2.1
  have hr := (selectedLaplaceSeparatedRightBoundary_spec n).1
  have hw := selectedLaplaceEdgeWidth_le_quarter n
  linarith

/-- The separated left sides converge to the left edge `Re p=-1/2`. -/
theorem tendsto_selectedLaplaceSeparatedLeftBoundary_neg_half :
    Tendsto selectedLaplaceSeparatedLeftBoundary atTop
      (𝓝 (-(1 / 2 : ℝ))) := by
  have hupperLimit : Tendsto
      (fun n : ℕ => -(1 / 2 : ℝ) + selectedLaplaceEdgeWidth n)
      atTop (𝓝 (-(1 / 2 : ℝ))) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_selectedLaplaceEdgeWidth_zero)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperLimit
  · exact Eventually.of_forall fun n =>
      (selectedLaplaceSeparatedLeftBoundary_spec n).1.le
  · exact Eventually.of_forall fun n =>
      (selectedLaplaceSeparatedLeftBoundary_spec n).2.1.le

/-- The separated right sides converge to the critical line `Re p=0`. -/
theorem tendsto_selectedLaplaceSeparatedRightBoundary_zero :
    Tendsto selectedLaplaceSeparatedRightBoundary atTop (𝓝 0) := by
  have hlowerLimit : Tendsto
      (fun n : ℕ => -selectedLaplaceEdgeWidth n) atTop (𝓝 0) := by
    simpa using tendsto_selectedLaplaceEdgeWidth_zero.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit tendsto_const_nhds
  · exact Eventually.of_forall fun n =>
      (selectedLaplaceSeparatedRightBoundary_spec n).1.le
  · exact Eventually.of_forall fun n =>
      (selectedLaplaceSeparatedRightBoundary_spec n).2.1.le

/-- No zero in the bounded-height window lies on the chosen left side. -/
theorem selectedLaplaceSeparatedLeftBoundary_ne_coordinate_of_mem
    (n : ℕ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n)) :
    selectedLaplaceSeparatedLeftBoundary n ≠
      (suzukiChebyshevLaplaceZeroCoordinate rho).re := by
  intro heq
  have hmem : (suzukiChebyshevLaplaceZeroCoordinate rho).re ∈
      selectedLaplaceRealBoundaryObstructions n := by
    apply Finset.mem_image.mpr
    exact ⟨rho, hrho, rfl⟩
  have hsep := (selectedLaplaceSeparatedLeftBoundary_spec n).2.2 _ hmem
  rw [heq, sub_self, abs_zero] at hsep
  exact (not_lt_of_ge hsep) (selectedLaplaceEdgeSeparation_pos n)

/-- No zero in the bounded-height window lies on the chosen right side. -/
theorem selectedLaplaceSeparatedRightBoundary_ne_coordinate_of_mem
    (n : ℕ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n)) :
    selectedLaplaceSeparatedRightBoundary n ≠
      (suzukiChebyshevLaplaceZeroCoordinate rho).re := by
  intro heq
  have hmem : (suzukiChebyshevLaplaceZeroCoordinate rho).re ∈
      selectedLaplaceRealBoundaryObstructions n := by
    apply Finset.mem_image.mpr
    exact ⟨rho, hrho, rfl⟩
  have hsep := (selectedLaplaceSeparatedRightBoundary_spec n).2.2 _ hmem
  rw [heq, sub_self, abs_zero] at hsep
  exact (not_lt_of_ge hsep) (selectedLaplaceEdgeSeparation_pos n)

/-- The selected zeta zeros strictly inside the near-edge rectangle at stage
`n`. -/
def separatedSelectedZetaZeroWindow (n : ℕ) :
    Finset NontrivialZetaZero :=
  (spectralUpperZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n)).filter fun rho =>
    selectedLaplaceSeparatedLeftBoundary n <
        (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re <
        selectedLaplaceSeparatedRightBoundary n

/-- Membership in the separated selected window is exactly upper-window
membership plus the two strict horizontal inequalities. -/
@[simp] theorem mem_separatedSelectedZetaZeroWindow
    {n : ℕ} {rho : NontrivialZetaZero} :
    rho ∈ separatedSelectedZetaZeroWindow n ↔
      rho ∈ spectralUpperZetaZeroWindow
          (quantitativeSpectralBoundaryTruncation n) ∧
        selectedLaplaceSeparatedLeftBoundary n <
          (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
        (suzukiChebyshevLaplaceZeroCoordinate rho).re <
          selectedLaplaceSeparatedRightBoundary n := by
  simp [separatedSelectedZetaZeroWindow]

/-- Every separated selected zero belongs to the complete bounded-height
spectral window. -/
theorem separatedSelectedZetaZeroWindow_subset_spectral
    (n : ℕ) :
    separatedSelectedZetaZeroWindow n ⊆
      spectralZetaZeroWindow (quantitativeSpectralBoundaryTruncation n) := by
  intro rho hrho
  exact (mem_spectralUpperZetaZeroWindow.mp
    (mem_separatedSelectedZetaZeroWindow.mp hrho).1).1

/-- Every near-edge rectangle stays in the positive shifted-coordinate slab
where the complete bounded-height divisor is available. -/
theorem separatedSelectedLaplaceRectangle_subset_finiteSlab (n : ℕ) :
    [[selectedLaplaceSeparatedLeftBoundary n,
        selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]] ⊆
      suzukiChebyshevLaplaceFiniteSlab
        (quantitativeSpectralBoundaryTruncation n) := by
  let T := quantitativeSpectralBoundaryTruncation n
  have hT : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hlr : selectedLaplaceSeparatedLeftBoundary n ≤
      selectedLaplaceSeparatedRightBoundary n :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  have hbu : -T ≤ T := by linarith
  intro z hz
  rw [uIcc_of_le hlr, uIcc_of_le hbu] at hz
  constructor
  · have hzre : -(1 / 2 : ℝ) < z.re :=
      (selectedLaplaceSeparatedLeftBoundary_spec n).1.trans_le hz.1.1
    rw [Complex.add_re]
    norm_num
    linarith
  · exact abs_le.mpr hz.2

/-- Every zero chosen by the separated selected filter lies strictly inside
all four sides of its rectangle. -/
theorem separatedSelectedLaplaceWindow_strictly_inside (n : ℕ)
    {rho : NontrivialZetaZero}
    (hrho : rho ∈ separatedSelectedZetaZeroWindow n) :
    selectedLaplaceSeparatedLeftBoundary n <
        (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re <
        selectedLaplaceSeparatedRightBoundary n ∧
      -quantitativeSpectralBoundaryTruncation n <
        (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im <
        quantitativeSpectralBoundaryTruncation n := by
  have hmem := mem_separatedSelectedZetaZeroWindow.mp hrho
  have hwindow := (mem_spectralUpperZetaZeroWindow.mp hmem.1).1
  have habsLe : |(zetaSpectralCoordinate rho.1).re| ≤
      quantitativeSpectralBoundaryTruncation n :=
    (mem_spectralZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation_nonneg n) rho).mp hwindow
  have habsLt : |(zetaSpectralCoordinate rho.1).re| <
      quantitativeSpectralBoundaryTruncation n :=
    lt_of_le_of_ne habsLe
      (quantitativeSpectralBoundaryTruncation_zeroFree n rho)
  have him : |(suzukiChebyshevLaplaceZeroCoordinate rho).im| <
      quantitativeSpectralBoundaryTruncation n := by
    rw [suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re]
    exact habsLt
  exact ⟨hmem.2.1, hmem.2.2, (abs_lt.mp him).1, (abs_lt.mp him).2⟩

/-- Every bounded-height zero not chosen by the separated selected filter is
genuinely outside the closed rectangle; horizontal equality is excluded by
the finite-gap construction. -/
theorem separatedSelectedLaplaceZero_outside_of_not_mem (n : ℕ)
    {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n))
    (hnot : rho ∉ separatedSelectedZetaZeroWindow n) :
    suzukiChebyshevLaplaceZeroCoordinate rho ∉
      [[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]] := by
  have hlr : selectedLaplaceSeparatedLeftBoundary n ≤
      selectedLaplaceSeparatedRightBoundary n :=
    (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hupperMem : rho ∈ spectralUpperZetaZeroWindow
        (quantitativeSpectralBoundaryTruncation n) :=
      mem_spectralUpperZetaZeroWindow.mpr ⟨hrho, hupper⟩
    have hnotBounds :
        ¬(selectedLaplaceSeparatedLeftBoundary n <
              (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
            (suzukiChebyshevLaplaceZeroCoordinate rho).re <
              selectedLaplaceSeparatedRightBoundary n) := by
      intro hbounds
      exact hnot (mem_separatedSelectedZetaZeroWindow.mpr
        ⟨hupperMem, hbounds⟩)
    intro hc
    rw [uIcc_of_le hlr] at hc
    by_cases hleft :
        (suzukiChebyshevLaplaceZeroCoordinate rho).re ≤
          selectedLaplaceSeparatedLeftBoundary n
    · have heq : (suzukiChebyshevLaplaceZeroCoordinate rho).re =
          selectedLaplaceSeparatedLeftBoundary n :=
        le_antisymm hleft hc.1.1
      exact
        (selectedLaplaceSeparatedLeftBoundary_ne_coordinate_of_mem n hrho)
          heq.symm
    · have hleftLt : selectedLaplaceSeparatedLeftBoundary n <
          (suzukiChebyshevLaplaceZeroCoordinate rho).re :=
        lt_of_not_ge hleft
      have hright : selectedLaplaceSeparatedRightBoundary n ≤
          (suzukiChebyshevLaplaceZeroCoordinate rho).re :=
        le_of_not_gt fun hrightLt => hnotBounds ⟨hleftLt, hrightLt⟩
      have heq : selectedLaplaceSeparatedRightBoundary n =
          (suzukiChebyshevLaplaceZeroCoordinate rho).re :=
        le_antisymm hright hc.1.2
      exact
        (selectedLaplaceSeparatedRightBoundary_ne_coordinate_of_mem n hrho)
          heq
  · have hnre :
        ¬(suzukiChebyshevLaplaceZeroCoordinate rho).re < 0 := by
      intro hre
      exact hupper
        ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mp hre)
    have hre0 : 0 ≤ (suzukiChebyshevLaplaceZeroCoordinate rho).re :=
      le_of_not_gt hnre
    intro hc
    rw [uIcc_of_le hlr] at hc
    have hrneg := (selectedLaplaceSeparatedRightBoundary_spec n).2.1
    linarith [hc.1.2]

/-- The exact selected finite Cauchy--Green identity on each separated
near-edge rectangle. -/
theorem separatedSelectedLaplaceBoundaryHeat_finiteCauchyGreen
    (x tau : ℝ) (n : ℕ) :
    rectangularAreaIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularBoundaryIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          ∑ rho ∈ separatedSelectedZetaZeroWindow n,
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ) := by
  apply
    suzukiChebyshevLaplaceBoundaryHeat_finiteCauchyGreen_of_selectedFinset
      x tau
      (selectedLaplaceSeparatedLeftBoundary n)
      (selectedLaplaceSeparatedRightBoundary n)
      (-quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation n)
      (quantitativeSpectralBoundaryTruncation_nonneg n)
      (selectedLaplaceSeparatedLeftBoundary_lt_rightBoundary n).le
      (by linarith [quantitativeSpectralBoundaryTruncation_nonneg n])
      (separatedSelectedZetaZeroWindow n)
  · exact separatedSelectedZetaZeroWindow_subset_spectral n
  · exact separatedSelectedLaplaceRectangle_subset_finiteSlab n
  · intro rho hrho
    exact separatedSelectedLaplaceWindow_strictly_inside n hrho
  · intro rho hrho hnot
    exact separatedSelectedLaplaceZero_outside_of_not_mem n hrho hnot

/-- Detector-first form of the near-edge finite identity: the filtered
positive residue sum is the actual arithmetic boundary-minus-bulk
functional. -/
theorem separatedSelectedLaplaceBoundaryHeat_residue_eq_boundary_sub_area
    (x tau : ℝ) (n : ℕ) :
    (2 * Real.pi * Complex.I) *
          ∑ rho ∈ separatedSelectedZetaZeroWindow n,
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ) =
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
  rw [separatedSelectedLaplaceBoundaryHeat_finiteCauchyGreen x tau n]
  ring

/-- Every fixed selected off-axis zero eventually belongs to every later
near-edge window, so the filtered rectangles exhaust the selected divisor
pointwise. -/
theorem eventually_mem_separatedSelectedZetaZeroWindow
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    ∀ᶠ n : ℕ in atTop, rho ∈ separatedSelectedZetaZeroWindow n := by
  have hleftGap :
      0 < (suzukiChebyshevLaplaceZeroCoordinate rho).re + 1 / 2 := by
    linarith [selectedLaplaceZeroCoordinate_re_gt_neg_half rho]
  have hrightGap :
      0 < -(suzukiChebyshevLaplaceZeroCoordinate rho).re := by
    exact neg_pos.mpr
      ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mpr hupper)
  have hwidthLeft : ∀ᶠ n : ℕ in atTop,
      selectedLaplaceEdgeWidth n <
        (suzukiChebyshevLaplaceZeroCoordinate rho).re + 1 / 2 :=
    (tendsto_order.1 tendsto_selectedLaplaceEdgeWidth_zero).2 _ hleftGap
  have hwidthRight : ∀ᶠ n : ℕ in atTop,
      selectedLaplaceEdgeWidth n <
        -(suzukiChebyshevLaplaceZeroCoordinate rho).re :=
    (tendsto_order.1 tendsto_selectedLaplaceEdgeWidth_zero).2 _ hrightGap
  have hheight : ∀ᶠ n : ℕ in atTop,
      |(zetaSpectralCoordinate rho.1).re| ≤
        quantitativeSpectralBoundaryTruncation n :=
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
      (eventually_ge_atTop |(zetaSpectralCoordinate rho.1).re|)
  filter_upwards [hwidthLeft, hwidthRight, hheight] with n hwLeft hwRight hT
  apply mem_separatedSelectedZetaZeroWindow.mpr
  constructor
  · apply mem_spectralUpperZetaZeroWindow.mpr
    exact ⟨(mem_spectralZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation_nonneg n) rho).mpr hT,
      hupper⟩
  · constructor
    · have hl := (selectedLaplaceSeparatedLeftBoundary_spec n).2.1
      linarith
    · have hr := (selectedLaplaceSeparatedRightBoundary_spec n).1
      linarith

end

end RiemannGaussian
