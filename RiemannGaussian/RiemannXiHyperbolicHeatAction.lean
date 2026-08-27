import RiemannGaussian.RiemannXiUpperHeightTrace

/-!
# The complete spectral-xi proper-time action

The fixed-positive-time spectral heat and its zero-time trace are already
constructed without endpoint assumptions.  This file performs the next
Tonelli step: it integrates the complete nonnegative heat over all positive
proper times in `ℝ≥0∞` and identifies the result with the full
multiplicity-counted sum of logarithmic pseudo-hyperbolic defects.

Using extended nonnegative reals is essential.  Neither finiteness of the
spectral height trace nor finiteness of the total logarithmic defect is
assumed.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-! ## A positive proper-time exhaustion -/

/-- The compact positive-time window used to turn the two-ended improper
limit into a genuine Lebesgue integral. -/
def positiveProperTimeWindow (n : ℕ) : Set ℝ :=
  Ioc (reciprocalNatProperTime n) ((n : ℝ) + 1)

/-- The endpoints of `positiveProperTimeWindow` tend simultaneously to zero
from above and to positive infinity. -/
theorem tendsto_positiveProperTimeWindow_endpoints :
    Tendsto
      (fun n : ℕ ↦ (reciprocalNatProperTime n, (n : ℝ) + 1))
      atTop ((nhdsWithin 0 (Ioi 0)) ×ˢ atTop) := by
  have hcast : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  exact tendsto_reciprocalNatProperTime_zero.prodMk hupper

/-- The windows exhaust `(0, ∞)` up to the ambient restricted measure. -/
theorem aecover_positiveProperTimeWindow :
    AECover (volume.restrict (Ioi (0 : ℝ))) atTop
      positiveProperTimeWindow := by
  refine ⟨?_, fun _ ↦ measurableSet_Ioc⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  have hzero : Tendsto reciprocalNatProperTime atTop (nhds 0) :=
    tendsto_reciprocalNatProperTime_zero.mono_right nhdsWithin_le_nhds
  have hlower : ∀ᶠ n in atTop, reciprocalNatProperTime n < tau :=
    (tendsto_order.1 hzero).2 tau htau
  have hupperLimit : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1)
      atTop atTop := by
    have hcast : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
        atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  have hupper : ∀ᶠ n : ℕ in atTop, tau ≤ (n : ℝ) + 1 :=
    hupperLimit.eventually (eventually_ge_atTop tau)
  filter_upwards [hlower, hupper] with n hnLower hnUpper
  exact ⟨hnLower, hnUpper⟩

/-! ## One spectral pair as a Lebesgue integral -/

/-- A single hyperbolic heat kernel is continuous throughout positive proper
time. -/
theorem continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ioi
    (z alpha : ℂ) :
    ContinuousOn
      (fun tau : ℝ ↦ upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)
      (Ioi 0) := by
  intro tau htau
  apply ContinuousAt.continuousWithinAt
  unfold upperHalfPlaneHyperbolicHeatIntegrand
  fun_prop (disch := exact htau.ne')

/-- For distinct upper-half-plane points, the Lebesgue integral of one lifted
heat kernel over all positive proper time is exactly its logarithmic defect.
-/
theorem lintegral_ofReal_upperHalfPlaneHyperbolicHeatIntegrand
    {z alpha : ℂ} (hz : 0 < z.im) (halpha : 0 < alpha.im)
    (hne : z ≠ alpha) :
    (∫⁻ tau in Ioi (0 : ℝ),
        ENNReal.ofReal
          (upperHalfPlaneHyperbolicHeatIntegrand z alpha tau)) =
      ENNReal.ofReal
        (-2 * Real.log
          (upperHalfPlanePseudoHyperbolicDistance z alpha)) := by
  let f : ℝ → ℝ := fun tau ↦
    upperHalfPlaneHyperbolicHeatIntegrand z alpha tau
  have hmeas : AEMeasurable (fun tau ↦ ENNReal.ofReal (f tau))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ioi z alpha).aemeasurable
      measurableSet_Ioi |>.ennreal_ofReal
  have hwindowOrdered (n : ℕ) :
      reciprocalNatProperTime n ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hreciprocal : reciprocalNatProperTime n ≤ 1 := by
      unfold reciprocalNatProperTime
      apply (div_le_one (show (0 : ℝ) < (n : ℝ) + 1 by linarith)).2
      linarith
    exact hreciprocal.trans (by linarith)
  have hwindowSubset (n : ℕ) :
      positiveProperTimeWindow n ⊆ Ioi (0 : ℝ) := by
    intro tau htau
    exact (reciprocalNatProperTime_pos n).trans htau.1
  have hintervalIntegrable (n : ℕ) :
      IntervalIntegrable f volume
        (reciprocalNatProperTime n) ((n : ℝ) + 1) := by
    apply ((continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ici
      z alpha (reciprocalNatProperTime_pos n)).mono ?_).intervalIntegrable
    intro tau htau
    rw [uIcc_of_le (hwindowOrdered n)] at htau
    exact htau.1
  have hcompact (n : ℕ) :
      (∫⁻ tau in positiveProperTimeWindow n,
          ENNReal.ofReal (f tau) ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ENNReal.ofReal
          (∫ tau in reciprocalNatProperTime n..(n : ℝ) + 1,
            f tau) := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (positiveProperTimeWindow n)] f := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with tau htau
      exact (upperHalfPlaneHyperbolicHeatIntegrand_pos hz halpha
        ((reciprocalNatProperTime_pos n).trans htau.1)).le
    have hwindowMeas : MeasurableSet (positiveProperTimeWindow n) := by
      exact measurableSet_Ioc
    change (∫⁻ tau,
        ENNReal.ofReal (f tau) ∂
          ((volume.restrict (Ioi (0 : ℝ))).restrict
            (positiveProperTimeWindow n))) = _
    rw [Measure.restrict_restrict hwindowMeas,
      inter_eq_left.mpr (hwindowSubset n)]
    simp only [positiveProperTimeWindow] at hnonneg ⊢
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hintervalIntegrable n).1 hnonneg]
    congr 1
    exact (intervalIntegral.integral_of_le (hwindowOrdered n)).symm
  have hreal : Tendsto
      (fun n : ℕ ↦
        ∫ tau in reciprocalNatProperTime n..(n : ℝ) + 1, f tau)
      atTop
      (nhds (-2 * Real.log
        (upperHalfPlanePseudoHyperbolicDistance z alpha))) :=
    (tendsto_upperHalfPlaneHyperbolicHeatIntegral hz halpha hne).comp
      tendsto_positiveProperTimeWindow_endpoints
  have hlifted : Tendsto
      (fun n : ℕ ↦
        ∫⁻ tau in positiveProperTimeWindow n,
          ENNReal.ofReal (f tau) ∂(volume.restrict (Ioi (0 : ℝ))))
      atTop
      (nhds (ENNReal.ofReal
        (-2 * Real.log
          (upperHalfPlanePseudoHyperbolicDistance z alpha)))) := by
    apply (ENNReal.tendsto_ofReal hreal).congr'
    exact Eventually.of_forall fun n ↦ (hcompact n).symm
  exact aecover_positiveProperTimeWindow.lintegral_eq_of_tendsto
    _ hmeas hlifted

/-! ## The complete spectral action -/

/-- The multiplicity-counted logarithmic defect contributed by one upper
spectral zero. -/
def zetaUpperHyperbolicLogDefectSummand
    (z : ℂ) (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (-2 * Real.log
        (upperHalfPlanePseudoHyperbolicDistance z
          (zetaSpectralCoordinate rho.1)))
  else 0

/-- Each selected logarithmic defect is nonnegative when the observation
point is distinct from the corresponding spectral zero. -/
theorem zetaUpperHyperbolicLogDefectSummand_nonneg
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero)
    (hne : z ≠ zetaSpectralCoordinate rho.1) :
    0 ≤ zetaUpperHyperbolicLogDefectSummand z rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicLogDefectSummand, if_pos hupper]
    apply mul_nonneg (Nat.cast_nonneg _)
    have hrpos := upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz hupper hne
    have hrlt := upperHalfPlanePseudoHyperbolicDistance_lt_one hz hupper
    have hlog := Real.log_neg hrpos hrlt
    linarith
  · rw [zetaUpperHyperbolicLogDefectSummand, if_neg hupper]

/-- An upper spectral zero contributes a strictly positive logarithmic
defect at every distinct upper observation point. -/
theorem zetaUpperHyperbolicLogDefectSummand_pos
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im)
    (hne : z ≠ zetaSpectralCoordinate rho.1) :
    0 < zetaUpperHyperbolicLogDefectSummand z rho := by
  rw [zetaUpperHyperbolicLogDefectSummand, if_pos hupper]
  apply mul_pos
  · exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  · have hrpos := upperHalfPlanePseudoHyperbolicDistance_pos_of_ne
      hz hupper hne
    have hrlt := upperHalfPlanePseudoHyperbolicDistance_lt_one hz hupper
    have hlog := Real.log_neg hrpos hrlt
    linarith

/-- Each lifted heat summand is measurable on positive proper time. -/
theorem aemeasurable_ofReal_zetaUpperHyperbolicHeatSummand
    (z : ℂ) (rho : NontrivialZetaZero) :
    AEMeasurable
      (fun tau : ℝ ↦
        ENNReal.ofReal (zetaUpperHyperbolicHeatSummand z tau rho))
      (volume.restrict (Ioi (0 : ℝ))) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hkernel : AEMeasurable
        (fun tau : ℝ ↦ upperHalfPlaneHyperbolicHeatIntegrand z
          (zetaSpectralCoordinate rho.1) tau)
        (volume.restrict (Ioi (0 : ℝ))) :=
      (continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ioi z
        (zetaSpectralCoordinate rho.1)).aemeasurable measurableSet_Ioi
    simpa only [zetaUpperHyperbolicHeatSummand, if_pos hupper] using
      (hkernel.const_mul
        (analyticZetaZeroMultiplicity rho : ℝ)).ennreal_ofReal
  · simp only [zetaUpperHyperbolicHeatSummand, if_neg hupper]
    exact aemeasurable_const

/-- Integrating one genuine spectral heat residue gives exactly its
multiplicity-counted logarithmic defect. -/
theorem lintegral_ofReal_zetaUpperHyperbolicHeatSummand
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (rho : NontrivialZetaZero) :
    (∫⁻ tau in Ioi (0 : ℝ),
        ENNReal.ofReal (zetaUpperHyperbolicHeatSummand z tau rho)) =
      ENNReal.ofReal (zetaUpperHyperbolicLogDefectSummand z rho) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      apply hxi
      rw [heq]
      exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2
        ⟨rho, rfl⟩
    have hkernelMeas : AEMeasurable
        (fun tau : ℝ ↦ ENNReal.ofReal
          (upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau))
        (volume.restrict (Ioi (0 : ℝ))) :=
      ((continuousOn_upperHalfPlaneHyperbolicHeatIntegrand_Ioi z
        (zetaSpectralCoordinate rho.1)).aemeasurable
          measurableSet_Ioi).ennreal_ofReal
    have hheat : (fun tau : ℝ ↦
        zetaUpperHyperbolicHeatSummand z tau rho) =
        fun tau ↦ (analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau := by
      funext tau
      rw [zetaUpperHyperbolicHeatSummand, if_pos hupper]
    have hdefect : zetaUpperHyperbolicLogDefectSummand z rho =
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (-2 * Real.log
            (upperHalfPlanePseudoHyperbolicDistance z
              (zetaSpectralCoordinate rho.1))) := by
      rw [zetaUpperHyperbolicLogDefectSummand, if_pos hupper]
    have hintegral :
        (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
          (zetaUpperHyperbolicHeatSummand z tau rho)) =
        ∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            upperHalfPlaneHyperbolicHeatIntegrand z
              (zetaSpectralCoordinate rho.1) tau) := by
      apply lintegral_congr
      intro tau
      rw [congrFun hheat tau]
    rw [hintegral, hdefect,
      ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    calc
      (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            upperHalfPlaneHyperbolicHeatIntegrand z
              (zetaSpectralCoordinate rho.1) tau)) =
          ∫⁻ tau in Ioi (0 : ℝ),
            ENNReal.ofReal (analyticZetaZeroMultiplicity rho : ℝ) *
              ENNReal.ofReal
                (upperHalfPlaneHyperbolicHeatIntegrand z
                  (zetaSpectralCoordinate rho.1) tau) := by
        apply lintegral_congr
        intro tau
        exact ENNReal.ofReal_mul (Nat.cast_nonneg _)
      _ = ENNReal.ofReal (analyticZetaZeroMultiplicity rho : ℝ) *
          (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
            (upperHalfPlaneHyperbolicHeatIntegrand z
              (zetaSpectralCoordinate rho.1) tau)) :=
        lintegral_const_mul'' _ hkernelMeas
      _ = ENNReal.ofReal (analyticZetaZeroMultiplicity rho : ℝ) *
          ENNReal.ofReal
            (-2 * Real.log
              (upperHalfPlanePseudoHyperbolicDistance z
                (zetaSpectralCoordinate rho.1))) := by
        rw [lintegral_ofReal_upperHalfPlaneHyperbolicHeatIntegrand
          hz hupper hne]
  · have hheat : (fun tau : ℝ ↦
        zetaUpperHyperbolicHeatSummand z tau rho) = fun _ ↦ 0 := by
      funext tau
      rw [zetaUpperHyperbolicHeatSummand, if_neg hupper]
    have hdefect : zetaUpperHyperbolicLogDefectSummand z rho = 0 := by
      rw [zetaUpperHyperbolicLogDefectSummand, if_neg hupper]
    have hintegral :
        (∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal
          (zetaUpperHyperbolicHeatSummand z tau rho)) =
        ∫⁻ _tau in Ioi (0 : ℝ), ENNReal.ofReal 0 := by
      apply lintegral_congr
      intro tau
      rw [congrFun hheat tau]
    rw [hintegral, hdefect]
    simp

/-- The complete multiplicity-counted upper spectral logarithmic defect,
allowing the value `∞`. -/
def riemannXiUpperHyperbolicLogDefectMass (z : ℂ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaUpperHyperbolicLogDefectSummand z rho)

/-- The complete spectral-xi heat action as an extended nonnegative Lebesgue
integral over all positive proper times. -/
def riemannXiUpperHyperbolicHeatAction (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ tau in Ioi (0 : ℝ),
    ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z tau)

/-- Tonelli's theorem identifies the complete proper-time heat action with
the full multiplicity-counted sum of spectral logarithmic defects.  The
identity remains valid when either side is infinite. -/
theorem riemannXiUpperHyperbolicHeatAction_eq_logDefectMass
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicHeatAction z =
      riemannXiUpperHyperbolicLogDefectMass z := by
  unfold riemannXiUpperHyperbolicHeatAction
    riemannXiUpperHyperbolicLogDefectMass
  calc
    (∫⁻ tau in Ioi (0 : ℝ),
        ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z tau)) =
        ∫⁻ tau in Ioi (0 : ℝ),
          ∑' rho : NontrivialZetaZero,
            ENNReal.ofReal
              (zetaUpperHyperbolicHeatSummand z tau rho) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      exact ofReal_riemannXiUpperHyperbolicHeatSum_eq_tsum hz htau
    _ = ∑' rho : NontrivialZetaZero,
          ∫⁻ tau in Ioi (0 : ℝ),
            ENNReal.ofReal
              (zetaUpperHyperbolicHeatSummand z tau rho) := by
      exact lintegral_tsum
        (aemeasurable_ofReal_zetaUpperHyperbolicHeatSummand z)
    _ = ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperHyperbolicLogDefectSummand z rho) := by
      apply tsum_congr
      intro rho
      exact lintegral_ofReal_zetaUpperHyperbolicHeatSummand hz hxi rho

/-- At a nonzero upper observation point, vanishing of the complete spectral
logarithmic defect is exactly the Riemann hypothesis. -/
theorem riemannXiUpperHyperbolicLogDefectMass_eq_zero_iff_riemannHypothesis
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicLogDefectMass z = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hne : z ≠ zetaSpectralCoordinate rho.1 := by
      intro heq
      apply hxi
      rw [heq]
      exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2
        ⟨rho, rfl⟩
    have hsummand : 0 < zetaUpperHyperbolicLogDefectSummand z rho :=
      zetaUpperHyperbolicLogDefectSummand_pos hz rho hwupper hne
    have hterm : 0 < ENNReal.ofReal
        (zetaUpperHyperbolicLogDefectSummand z rho) :=
      ENNReal.ofReal_pos.mpr hsummand
    have hle : ENNReal.ofReal
          (zetaUpperHyperbolicLogDefectSummand z rho) ≤
        riemannXiUpperHyperbolicLogDefectMass z :=
      ENNReal.le_tsum rho
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    unfold riemannXiUpperHyperbolicLogDefectMass
    rw [ENNReal.tsum_eq_zero]
    intro rho
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    have hnupper : ¬0 < (zetaSpectralCoordinate rho.1).im := by
      linarith
    rw [zetaUpperHyperbolicLogDefectSummand, if_neg hnupper,
      ENNReal.ofReal_zero]

/-- Equivalently, the complete extended proper-time heat action vanishes
exactly under RH. -/
theorem riemannXiUpperHyperbolicHeatAction_eq_zero_iff_riemannHypothesis
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) :
    riemannXiUpperHyperbolicHeatAction z = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiUpperHyperbolicHeatAction_eq_logDefectMass hz hxi]
  exact
    riemannXiUpperHyperbolicLogDefectMass_eq_zero_iff_riemannHypothesis hz hxi

end

end RiemannGaussian
