import RiemannGaussian.RiemannXiSuzukiPointwiseCurvature
import RiemannGaussian.SuzukiTransportTail

/-!
# Exact tail normalization of Suzuki's pointwise arithmetic model

The transport-tail criterion was previously parameterized by a functional
normalization hypothesis.  This file discharges that hypothesis for Suzuki's
literal pointwise Archimedean term.

The input is the source-exact curvature theorem: on positive time the
Archimedean slope has derivative `suzukiSmoothCurvature`.  The fundamental
theorem of calculus and derivative uniqueness then recover the slope and the
Archimedean function from curvature at any positive base.  Finally, the
finite frozen prime prefix shifts the base value and base slope by its exact
mass and moment.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Calculus of the transport primitives -/

private theorem intervalIntegrable_suzukiSmoothCurvature
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable suzukiSmoothCurvature volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_suzukiSmoothCurvature_Ioi.mono
  intro s hs
  rcases Set.mem_uIcc.mp hs with has | hbs
  · exact ha.trans_le has.1
  · exact hb.trans_le hbs.1

private theorem intervalIntegrable_suzukiSmoothCurvatureMoment
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s : ℝ => s * suzukiSmoothCurvature s)
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_id.mul continuousOn_suzukiSmoothCurvature_Ioi).mono
  intro s hs
  rcases Set.mem_uIcc.mp hs with has | hbs
  · exact ha.trans_le has.1
  · exact hb.trans_le hbs.1

/-- Curvature mass accumulated from a positive base differentiates to
Suzuki's smooth curvature at every positive endpoint. -/
theorem hasDerivAt_transportCurvatureMass_suzukiSmoothCurvature
    {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    HasDerivAt
      (transportCurvatureMass suzukiSmoothCurvature base)
      (suzukiSmoothCurvature t) t := by
  have hcontinuousAt : ContinuousAt suzukiSmoothCurvature t :=
    (continuousOn_suzukiSmoothCurvature_Ioi t ht).continuousAt
      (Ioi_mem_nhds ht)
  unfold transportCurvatureMass
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_suzukiSmoothCurvature hbase ht)
    (continuousOn_suzukiSmoothCurvature_Ioi.stronglyMeasurableAtFilter
      isOpen_Ioi t ht) hcontinuousAt

/-- The first curvature moment accumulated from a positive base has endpoint
derivative `t * suzukiSmoothCurvature t`. -/
theorem hasDerivAt_transportCurvatureMoment_suzukiSmoothCurvature
    {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    HasDerivAt
      (transportCurvatureMoment suzukiSmoothCurvature base)
      (t * suzukiSmoothCurvature t) t := by
  have hcontinuousAt : ContinuousAt suzukiSmoothCurvature t :=
    (continuousOn_suzukiSmoothCurvature_Ioi t ht).continuousAt
      (Ioi_mem_nhds ht)
  have hmomentContinuousAt :
      ContinuousAt (fun s : ℝ => s * suzukiSmoothCurvature s) t :=
    continuousAt_id.mul hcontinuousAt
  unfold transportCurvatureMoment
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_suzukiSmoothCurvatureMoment hbase ht)
    ((continuousOn_id.mul
      continuousOn_suzukiSmoothCurvature_Ioi).stronglyMeasurableAtFilter
        isOpen_Ioi t ht) hmomentContinuousAt

/-- The zero-slope curvature background differentiates to accumulated
curvature mass. -/
theorem hasDerivAt_zeroSlopeCurvatureBackground_suzukiSmoothCurvature
    (baseValue : ℝ) {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    HasDerivAt
      (zeroSlopeCurvatureBackground baseValue base suzukiSmoothCurvature)
      (transportCurvatureMass suzukiSmoothCurvature base t) t := by
  have hmass :=
    hasDerivAt_transportCurvatureMass_suzukiSmoothCurvature hbase ht
  have hmoment :=
    hasDerivAt_transportCurvatureMoment_suzukiSmoothCurvature hbase ht
  unfold zeroSlopeCurvatureBackground
  apply (((hasDerivAt_const t baseValue).add
    ((hasDerivAt_id t).mul hmass)).sub hmoment).congr_deriv
  simp only [id_eq]
  ring

/-- A slope-reset curvature background has derivative equal to curvature mass
plus its prescribed base slope. -/
theorem hasDerivAt_slopeResetCurvatureBackground_suzukiSmoothCurvature
    (baseValue baseSlope : ℝ) {base t : ℝ}
    (hbase : 0 < base) (ht : 0 < t) :
    HasDerivAt
      (slopeResetCurvatureBackground baseValue baseSlope base
        suzukiSmoothCurvature)
      (transportCurvatureMass suzukiSmoothCurvature base t + baseSlope) t := by
  have hzero :=
    hasDerivAt_zeroSlopeCurvatureBackground_suzukiSmoothCurvature
      baseValue hbase ht
  have haffine : HasDerivAt (fun u : ℝ => baseSlope * (u - base))
      baseSlope t := by
    apply (((hasDerivAt_id t).sub_const base).const_mul baseSlope).congr_deriv
    ring
  unfold slopeResetCurvatureBackground
  exact hzero.add haffine

/-! ## Reconstruction from curvature -/

/-- The Archimedean slope reconstructed by integrating curvature from a
positive base. -/
def suzukiPointwiseIntegratedArchimedeanSlope
    (base t : ℝ) : ℝ :=
  transportCurvatureMass suzukiSmoothCurvature base t +
    suzukiPointwiseArchimedeanSlope base

/-- The curvature-integrated slope has derivative
`suzukiSmoothCurvature`. -/
theorem hasDerivAt_suzukiPointwiseIntegratedArchimedeanSlope
    {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    HasDerivAt (suzukiPointwiseIntegratedArchimedeanSlope base)
      (suzukiSmoothCurvature t) t := by
  unfold suzukiPointwiseIntegratedArchimedeanSlope
  exact (hasDerivAt_transportCurvatureMass_suzukiSmoothCurvature
    hbase ht).add_const (suzukiPointwiseArchimedeanSlope base)

/-- The explicit Archimedean slope equals curvature mass accumulated from
any positive base plus its slope at that base. -/
theorem suzukiPointwiseArchimedeanSlope_eq_integrated
    {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    suzukiPointwiseArchimedeanSlope t =
      suzukiPointwiseIntegratedArchimedeanSlope base t := by
  have hslopeDifferentiable :
      DifferentiableOn ℝ suzukiPointwiseArchimedeanSlope (Set.Ioi 0) := by
    intro u hu
    exact (hasDerivAt_suzukiPointwiseArchimedeanSlope hu).differentiableAt
      |>.differentiableWithinAt
  have hintegratedDifferentiable : DifferentiableOn ℝ
      (suzukiPointwiseIntegratedArchimedeanSlope base) (Set.Ioi 0) := by
    intro u hu
    exact (hasDerivAt_suzukiPointwiseIntegratedArchimedeanSlope hbase hu)
      |>.differentiableAt.differentiableWithinAt
  have hderiv : (Set.Ioi 0).EqOn
      (deriv suzukiPointwiseArchimedeanSlope)
      (deriv (suzukiPointwiseIntegratedArchimedeanSlope base)) := by
    intro u hu
    rw [(hasDerivAt_suzukiPointwiseArchimedeanSlope hu).deriv,
      (hasDerivAt_suzukiPointwiseIntegratedArchimedeanSlope hbase hu).deriv]
  have hbaseValue : suzukiPointwiseArchimedeanSlope base =
      suzukiPointwiseIntegratedArchimedeanSlope base base := by
    simp [suzukiPointwiseIntegratedArchimedeanSlope]
  have heq := isOpen_Ioi.eqOn_of_deriv_eq isPreconnected_Ioi
    hslopeDifferentiable hintegratedDifferentiable hderiv hbase hbaseValue
  exact heq ht

/-- On positive time, Suzuki's literal pointwise Archimedean term is exactly
the curvature background reset to its value and slope at any positive base. -/
theorem suzukiPointwiseArchimedean_eq_slopeResetCurvatureBackground
    {base t : ℝ} (hbase : 0 < base) (ht : 0 < t) :
    suzukiPointwiseArchimedean t =
      slopeResetCurvatureBackground
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) base
        suzukiSmoothCurvature t := by
  have harchDifferentiable :
      DifferentiableOn ℝ suzukiPointwiseArchimedean (Set.Ioi 0) := by
    intro u hu
    exact (hasDerivAt_suzukiPointwiseArchimedean hu).differentiableAt
      |>.differentiableWithinAt
  have hresetDifferentiable : DifferentiableOn ℝ
      (slopeResetCurvatureBackground
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) base
        suzukiSmoothCurvature) (Set.Ioi 0) := by
    intro u hu
    exact
      (hasDerivAt_slopeResetCurvatureBackground_suzukiSmoothCurvature
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) hbase hu)
        |>.differentiableAt.differentiableWithinAt
  have hderiv : (Set.Ioi 0).EqOn
      (deriv suzukiPointwiseArchimedean)
      (deriv (slopeResetCurvatureBackground
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) base
        suzukiSmoothCurvature)) := by
    intro u hu
    rw [(hasDerivAt_suzukiPointwiseArchimedean hu).deriv,
      (hasDerivAt_slopeResetCurvatureBackground_suzukiSmoothCurvature
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) hbase hu).deriv]
    exact suzukiPointwiseArchimedeanSlope_eq_integrated hbase hu
  have hbaseValue : suzukiPointwiseArchimedean base =
      slopeResetCurvatureBackground
        (suzukiPointwiseArchimedean base)
        (suzukiPointwiseArchimedeanSlope base) base
        suzukiSmoothCurvature base := by simp
  have heq := isOpen_Ioi.eqOn_of_deriv_eq isPreconnected_Ioi
    harchDifferentiable hresetDifferentiable hderiv hbase hbaseValue
  exact heq ht

/-! ## Exact normalization after a frozen prime prefix -/

/-- Value at the reset base after affinely freezing the first `start` prime
hinges. -/
def suzukiPointwiseFrozenBaseValue (base : ℝ) (start : ℕ) : ℝ :=
  frozenScrewHingeModel suzukiPointwiseArchimedean
    suzukiPrimeLocation suzukiPrimeWeight start base

/-- Slope at the reset base after subtracting the mass of the first `start`
prime hinges. -/
def suzukiPointwiseFrozenBaseSlope (base : ℝ) (start : ℕ) : ℝ :=
  suzukiPointwiseArchimedeanSlope base -
    screwPrefixMass suzukiPrimeWeight start

/-- For every positive base and every finite prime prefix, the literal
pointwise Archimedean background satisfies the exact transport-tail
normalization with its computed frozen value and slope. -/
theorem suzukiPointwiseTailNormalization
    {base : ℝ} (hbase : 0 < base) (start : ℕ) :
    SuzukiTailNormalization suzukiPointwiseArchimedean
      (suzukiPointwiseFrozenBaseValue base start)
      (suzukiPointwiseFrozenBaseSlope base start) base start := by
  intro t ht
  have htpos : 0 < t := hbase.trans_le ht
  rw [frozenScrewHingeModel_eq_arch_sub_mass_add_moment,
    suzukiPointwiseArchimedean_eq_slopeResetCurvatureBackground
      hbase htpos]
  unfold suzukiPointwiseFrozenBaseValue
    suzukiPointwiseFrozenBaseSlope
  rw [frozenScrewHingeModel_eq_arch_sub_mass_add_moment]
  unfold slopeResetCurvatureBackground zeroSlopeCurvatureBackground
  ring

/-- The complete literal arithmetic pointwise function is therefore governed
on an audited tail by the cumulative transport-surplus criterion without any
separate normalization hypothesis.  The remaining assumptions concern the
chosen event cut and the sign of its now-explicit frozen slope. -/
theorem riemannXiSuzukiPsiNonnegative_on_tail_iff_cumulativeTransportSurplus
    {base : ℝ} {start : ℕ} (hlog : Real.log 2 ≤ base)
    (hslope : suzukiPointwiseFrozenBaseSlope base start ≤ 0)
    (hcut : ScrewEventCut suzukiPrimeLocation base start) :
    (∀ t : ℝ, base ≤ t → 0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ cutoff : ℕ,
        -suzukiPointwiseFrozenBaseValue base start ≤
          ∑ n ∈ Finset.range cutoff,
            suzukiResetTransportCellSurplus base
              (suzukiPointwiseFrozenBaseSlope base start)
              hlog hslope start n := by
  have hbase : 0 < base :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hlog
  have hcriterion :=
    suzukiFullModel_nonnegativeOn_tail_iff_cumulativeTransportSurplus
      (archimedean := suzukiPointwiseArchimedean)
      hlog hslope hcut (suzukiPointwiseTailNormalization hbase start)
  constructor
  · intro hpsi
    apply hcriterion.mp
    intro t ht
    rw [← riemannXiSuzukiPsiNonnegative_eq_screwHingeModel
      (hbase.le.trans ht)]
    exact hpsi t ht
  · intro hsurplus t ht
    rw [riemannXiSuzukiPsiNonnegative_eq_screwHingeModel
      (hbase.le.trans ht)]
    exact hcriterion.mpr hsurplus t ht

end

end RiemannGaussian
