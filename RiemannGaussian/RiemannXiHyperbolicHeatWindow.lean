import RiemannGaussian.RiemannXiHyperbolicHeat

/-!
# Finite windows of the spectral-xi heat divisor

This file realizes the complete fixed-proper-time heat sum as the limit of
canonical finite spectral windows.  The complex form of every window is the
finite sum of the genuine heat-weighted local residues of
`logDeriv riemannXiSpectral`; cofinality of the zero windows and absolute
summability give the entire limit.

This is the finite-divisor approximation on the spectral-xi side.  It does
not yet identify these windows with the zero multisets of the root-pinned
polynomial approximants.
-/

namespace RiemannGaussian

noncomputable section

open Filter Topology

/-- Every selected real heat summand is nonnegative. -/
theorem zetaUpperHyperbolicHeatSummand_nonneg
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperHyperbolicHeatSummand z tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicHeatSummand, if_pos hupper]
    exact mul_nonneg (Nat.cast_nonneg _)
      (upperHalfPlaneHyperbolicHeatIntegrand_pos hz hupper htau).le
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper]

/-- A selected upper zero contributes strictly positively. -/
theorem zetaUpperHyperbolicHeatSummand_pos
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    0 < zetaUpperHyperbolicHeatSummand z tau rho := by
  rw [zetaUpperHyperbolicHeatSummand, if_pos hupper]
  exact mul_pos (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
    (upperHalfPlaneHyperbolicHeatIntegrand_pos hz hupper htau)

/-- The real fixed-time heat sum over the canonical symmetric spectral
window. -/
noncomputable def riemannXiUpperHyperbolicHeatWindow
    (z : ℂ) (tau T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaUpperHyperbolicHeatSummand z tau rho

/-- The same finite window written as heat-weighted spectral-xi residues. -/
noncomputable def riemannXiUpperHyperbolicHeatResidueWindow
    (z : ℂ) (tau T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    riemannXiUpperHyperbolicHeatResidue z tau rho

/-- The residue window is exactly the complex cast of the real heat
window. -/
@[simp] theorem riemannXiUpperHyperbolicHeatResidueWindow_eq_ofReal
    (z : ℂ) (tau T : ℝ) :
    riemannXiUpperHyperbolicHeatResidueWindow z tau T =
      (riemannXiUpperHyperbolicHeatWindow z tau T : ℂ) := by
  simp [riemannXiUpperHyperbolicHeatResidueWindow,
    riemannXiUpperHyperbolicHeatWindow]

/-- Every finite upper heat window is nonnegative. -/
theorem riemannXiUpperHyperbolicHeatWindow_nonneg
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) (T : ℝ) :
    0 ≤ riemannXiUpperHyperbolicHeatWindow z tau T := by
  unfold riemannXiUpperHyperbolicHeatWindow
  exact Finset.sum_nonneg fun rho _ ↦
    zetaUpperHyperbolicHeatSummand_nonneg hz htau rho

/-- A finite window never exceeds the complete nonnegative heat sum. -/
theorem riemannXiUpperHyperbolicHeatWindow_le_sum
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) (T : ℝ) :
    riemannXiUpperHyperbolicHeatWindow z tau T ≤
      riemannXiUpperHyperbolicHeatSum z tau := by
  unfold riemannXiUpperHyperbolicHeatWindow
    riemannXiUpperHyperbolicHeatSum
  exact (summable_zetaUpperHyperbolicHeatSummand hz htau).sum_le_tsum
    (spectralZetaZeroWindow T) fun rho _ ↦
      zetaUpperHyperbolicHeatSummand_nonneg hz htau rho

/-- A finite window vanishes exactly when it contains no selected upper
spectral zero. -/
theorem riemannXiUpperHyperbolicHeatWindow_eq_zero_iff
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) (T : ℝ) :
    riemannXiUpperHyperbolicHeatWindow z tau T = 0 ↔
      ∀ rho ∈ spectralZetaZeroWindow T,
        ¬0 < (zetaSpectralCoordinate rho.1).im := by
  unfold riemannXiUpperHyperbolicHeatWindow
  have hnonneg : ∀ rho ∈ spectralZetaZeroWindow T,
      0 ≤ zetaUpperHyperbolicHeatSummand z tau rho := fun rho _ ↦
    zetaUpperHyperbolicHeatSummand_nonneg hz htau rho
  constructor
  · intro hzero rho hrho hupper
    have htermZero :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero rho hrho
    have htermPos :=
      zetaUpperHyperbolicHeatSummand_pos hz htau rho hupper
    linarith
  · intro hupper
    apply (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mpr
    intro rho hrho
    rw [zetaUpperHyperbolicHeatSummand, if_neg (hupper rho hrho)]

/-- Once a window contains one upper zero, its heat sum is strictly
positive. -/
theorem riemannXiUpperHyperbolicHeatWindow_pos_of_upper_zero
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    {T : ℝ} (hT : |(zetaSpectralCoordinate rho.1).re| ≤ T) :
    0 < riemannXiUpperHyperbolicHeatWindow z tau T := by
  unfold riemannXiUpperHyperbolicHeatWindow
  apply Finset.sum_pos'
  · intro sigma _
    exact zetaUpperHyperbolicHeatSummand_nonneg hz htau sigma
  · refine ⟨rho, ?_, zetaUpperHyperbolicHeatSummand_pos hz htau rho hupper⟩
    exact (mem_spectralZetaZeroWindow
      ((abs_nonneg (zetaSpectralCoordinate rho.1).re).trans hT) rho).mpr hT

/-- Expanding real heat windows converge to the complete fixed-time heat
sum. -/
theorem tendsto_riemannXiUpperHyperbolicHeatWindow
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (riemannXiUpperHyperbolicHeatWindow z tau) atTop
      (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  have hsum := (summable_zetaUpperHyperbolicHeatSummand hz htau).hasSum
  change Tendsto
      (fun S : Finset NontrivialZetaZero ↦
        ∑ rho ∈ S, zetaUpperHyperbolicHeatSummand z tau rho)
      atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) at hsum
  unfold riemannXiUpperHyperbolicHeatWindow
  exact hsum.comp tendsto_spectralZetaZeroWindow_atTop

/-- Expanding finite sums of the genuine heat-weighted logarithmic-
derivative residues converge to the complete heat sum. -/
theorem tendsto_riemannXiUpperHyperbolicHeatResidueWindow
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (riemannXiUpperHyperbolicHeatResidueWindow z tau) atTop
      (nhds (riemannXiUpperHyperbolicHeatSum z tau : ℂ)) := by
  have hsum := hasSum_riemannXiUpperHyperbolicHeatResidue hz htau
  change Tendsto
      (fun S : Finset NontrivialZetaZero ↦
        ∑ rho ∈ S, riemannXiUpperHyperbolicHeatResidue z tau rho)
      atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau : ℂ)) at hsum
  unfold riemannXiUpperHyperbolicHeatResidueWindow
  exact hsum.comp tendsto_spectralZetaZeroWindow_atTop

/-- The canonical zero-free boundary truncations give a concrete real
sequence converging to the full heat sum. -/
theorem tendsto_riemannXiUpperHyperbolicHeatWindow_boundaryTruncation
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ riemannXiUpperHyperbolicHeatWindow z tau
        (spectralBoundaryTruncation n)) atTop
      (nhds (riemannXiUpperHyperbolicHeatSum z tau)) :=
  (tendsto_riemannXiUpperHyperbolicHeatWindow hz htau).comp
    tendsto_spectralBoundaryTruncation_atTop

/-- The same zero-free truncation sequence converges in its literal residue
form. -/
theorem tendsto_riemannXiUpperHyperbolicHeatResidueWindow_boundaryTruncation
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ riemannXiUpperHyperbolicHeatResidueWindow z tau
        (spectralBoundaryTruncation n)) atTop
      (nhds (riemannXiUpperHyperbolicHeatSum z tau : ℂ)) :=
  (tendsto_riemannXiUpperHyperbolicHeatResidueWindow hz htau).comp
    tendsto_spectralBoundaryTruncation_atTop

/-- At any fixed upper observation point and positive proper time, RH is
equivalent to vanishing of every finite spectral heat window. -/
theorem riemannHypothesis_iff_forall_riemannXiUpperHyperbolicHeatWindow_eq_zero
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    RiemannHypothesis ↔
      ∀ T : ℝ, riemannXiUpperHyperbolicHeatWindow z tau T = 0 := by
  constructor
  · intro hRH T
    apply (riemannXiUpperHyperbolicHeatWindow_eq_zero_iff hz htau T).mpr
    intro rho _
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    linarith
  · intro hwindow
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hpos := riemannXiUpperHyperbolicHeatWindow_pos_of_upper_zero
      hz htau rho hwupper (le_refl _)
    have hzero := hwindow |(zetaSpectralCoordinate rho.1).re|
    linarith

end

end RiemannGaussian
