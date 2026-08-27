import RiemannGaussian.FiniteToEntireProperTimeHeightVariation

/-!
# The entire spectral-xi height trace at proper time zero

At a finite stage, the zero-time heat trace is four times the observation
height times the total upper-root height.  This file constructs the analogous
quantity for the complete spectral-xi divisor without assuming that its
height sum is finite.

The spectral height mass therefore takes values in `ℝ≥0∞`.  A monotone
convergence theorem for extended-real series is proved and applied along the
cofinal reciprocal times `1 / (n + 1)`.  The resulting theorem identifies the
limit of the complete fixed-time spectral heat with the full
multiplicity-counted height trace, including the possibility `∞`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-counted upper height contributed by one nontrivial zeta
zero in spectral coordinates. -/
def zetaUpperSpectralHeightSummand (rho : NontrivialZetaZero) : ℝ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℝ) *
      (zetaSpectralCoordinate rho.1).im
  else 0

/-- Every spectral upper-height summand is nonnegative. -/
theorem zetaUpperSpectralHeightSummand_nonneg
    (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperSpectralHeightSummand rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperSpectralHeightSummand, if_pos hupper]
    exact mul_nonneg (Nat.cast_nonneg _) hupper.le
  · rw [zetaUpperSpectralHeightSummand, if_neg hupper]

/-- The complete upper spectral-xi height mass.  The value is extended real
because finiteness is neither assumed nor currently known. -/
def riemannXiUpperSpectralHeightMass : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)

/-- The full zero-time heat trace at an observation point, again allowing
the value `∞`. -/
def riemannXiUpperHyperbolicHeatTrace (z : ℂ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal
      (4 * z.im * zetaUpperSpectralHeightSummand rho)

/-- One heat-weighted spectral residue tends to four times the observation
height times its multiplicity-counted upper spectral height. -/
theorem tendsto_zetaUpperHyperbolicHeatSummand_zero
    (z : ℂ) (rho : NontrivialZetaZero) :
    Tendsto (fun tau ↦ zetaUpperHyperbolicHeatSummand z tau rho)
      (nhdsWithin 0 (Ioi 0))
      (nhds (4 * z.im * zetaUpperSpectralHeightSummand rho)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hheight : zetaUpperSpectralHeightSummand rho =
        (analyticZetaZeroMultiplicity rho : ℝ) *
          (zetaSpectralCoordinate rho.1).im := by
      rw [zetaUpperSpectralHeightSummand, if_pos hupper]
    rw [hheight]
    have hlimit :=
      (tendsto_upperHalfPlaneHyperbolicHeatIntegrand_zero z
        (zetaSpectralCoordinate rho.1)).const_mul
          (analyticZetaZeroMultiplicity rho : ℝ)
    have heq : (fun tau ↦ zetaUpperHyperbolicHeatSummand z tau rho) =
        fun tau ↦ (analyticZetaZeroMultiplicity rho : ℝ) *
          upperHalfPlaneHyperbolicHeatIntegrand z
            (zetaSpectralCoordinate rho.1) tau := by
      funext tau
      rw [zetaUpperHyperbolicHeatSummand, if_pos hupper]
    rw [heq]
    convert hlimit using 1
    ring_nf
  · have hheat : (fun tau ↦
        zetaUpperHyperbolicHeatSummand z tau rho) = fun _ ↦ 0 := by
      funext tau
      rw [zetaUpperHyperbolicHeatSummand, if_neg hupper]
    have hheight : zetaUpperSpectralHeightSummand rho = 0 := by
      rw [zetaUpperSpectralHeightSummand, if_neg hupper]
    rw [hheat, hheight, mul_zero]
    exact tendsto_const_nhds

/-- Monotone convergence commutes with an arbitrary extended-real series.
This is the counting-measure monotone convergence theorem in a form tailored
to the spectral heat trace. -/
theorem tendsto_tsum_ennreal_of_monotone
    {ι : Type*} (f : ℕ → ι → ℝ≥0∞) (g : ι → ℝ≥0∞)
    (hmono : ∀ i, Monotone fun n ↦ f n i)
    (hlimit : ∀ i, Tendsto (fun n ↦ f n i) atTop (nhds (g i))) :
    Tendsto (fun n ↦ ∑' i, f n i) atTop (nhds (∑' i, g i)) := by
  have hsumMono : Monotone fun n ↦ ∑' i, f n i := by
    intro n m hnm
    exact ENNReal.tsum_le_tsum fun i ↦ hmono i hnm
  have hsup : (⨆ n, ∑' i, f n i) = ∑' i, g i := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply ENNReal.tsum_le_tsum
      intro i
      exact (hmono i).ge_of_tendsto (hlimit i) n
    · rw [ENNReal.tsum_eq_iSup_sum]
      apply iSup_le
      intro s
      have hfinite : Tendsto (fun n ↦ ∑ i ∈ s, f n i)
          atTop (nhds (∑ i ∈ s, g i)) :=
        tendsto_finsetSum s fun i _ ↦ hlimit i
      apply le_of_tendsto hfinite
      exact Eventually.of_forall fun n ↦
        (ENNReal.sum_le_tsum s).trans (le_iSup (fun m ↦ ∑' i, f m i) n)
  rw [← hsup]
  exact tendsto_atTop_iSup hsumMono

/-- Reciprocal integer proper times form the canonical decreasing sequence
toward zero used for the entire trace. -/
def reciprocalNatProperTime (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Every reciprocal integer proper time is positive. -/
theorem reciprocalNatProperTime_pos (n : ℕ) :
    0 < reciprocalNatProperTime n := by
  unfold reciprocalNatProperTime
  positivity

/-- Reciprocal integer proper time decreases as the index increases. -/
theorem antitone_reciprocalNatProperTime :
    Antitone reciprocalNatProperTime := by
  intro n m hnm
  simpa [reciprocalNatProperTime] using
    (Nat.one_div_le_one_div (α := ℝ) hnm)

/-- The reciprocal proper times tend to zero through positive values. -/
theorem tendsto_reciprocalNatProperTime_zero :
    Tendsto reciprocalNatProperTime atTop (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n ↦ reciprocalNatProperTime_pos n⟩
  change Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Along decreasing reciprocal proper times, every lifted spectral heat
summand increases monotonically. -/
theorem monotone_zetaUpperHyperbolicHeatSummand_reciprocal
    {z : ℂ} (hz : 0 < z.im) (rho : NontrivialZetaZero) :
    Monotone fun n ↦ ENNReal.ofReal
      (zetaUpperHyperbolicHeatSummand z (reciprocalNatProperTime n) rho) := by
  intro n m hnm
  apply ENNReal.ofReal_le_ofReal
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicHeatSummand, if_pos hupper,
      zetaUpperHyperbolicHeatSummand, if_pos hupper]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact upperHalfPlaneHyperbolicHeatIntegrand_le_of_time_le
      hz hupper (reciprocalNatProperTime_pos m)
      (antitone_reciprocalNatProperTime hnm)
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper,
      zetaUpperHyperbolicHeatSummand, if_neg hupper]

/-- The complete spectral-xi heat is antitone on positive proper time. -/
theorem riemannXiUpperHyperbolicHeatSum_le_of_time_le
    {z : ℂ} (hz : 0 < z.im) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    riemannXiUpperHyperbolicHeatSum z t ≤
      riemannXiUpperHyperbolicHeatSum z s := by
  unfold riemannXiUpperHyperbolicHeatSum
  apply (summable_zetaUpperHyperbolicHeatSummand
    hz (hs.trans_le hst)).tsum_le_tsum _
    (summable_zetaUpperHyperbolicHeatSummand hz hs)
  intro rho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperHyperbolicHeatSummand, if_pos hupper,
      zetaUpperHyperbolicHeatSummand, if_pos hupper]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact upperHalfPlaneHyperbolicHeatIntegrand_le_of_time_le
      hz hupper hs hst
  · rw [zetaUpperHyperbolicHeatSummand, if_neg hupper,
      zetaUpperHyperbolicHeatSummand, if_neg hupper]

/-- Lifting the convergent positive-time real series to `ℝ≥0∞` commutes
with its sum. -/
theorem ofReal_riemannXiUpperHyperbolicHeatSum_eq_tsum
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z tau) =
      ∑' rho : NontrivialZetaZero,
        ENNReal.ofReal (zetaUpperHyperbolicHeatSummand z tau rho) := by
  unfold riemannXiUpperHyperbolicHeatSum
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun rho ↦ zetaUpperHyperbolicHeatSummand_nonneg hz htau rho)
    (summable_zetaUpperHyperbolicHeatSummand hz htau)

/-- The complete fixed-time spectral-xi heat converges along reciprocal
proper times to its full extended-real zero-time height trace. -/
theorem tendsto_riemannXiUpperHyperbolicHeatSum_reciprocal_zero
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto
      (fun n ↦ ENNReal.ofReal
        (riemannXiUpperHyperbolicHeatSum z (reciprocalNatProperTime n)))
      atTop (nhds (riemannXiUpperHyperbolicHeatTrace z)) := by
  have hpointwise (rho : NontrivialZetaZero) : Tendsto
      (fun n ↦ ENNReal.ofReal
        (zetaUpperHyperbolicHeatSummand z
          (reciprocalNatProperTime n) rho))
      atTop
      (nhds (ENNReal.ofReal
        (4 * z.im * zetaUpperSpectralHeightSummand rho))) :=
    ENNReal.tendsto_ofReal
      ((tendsto_zetaUpperHyperbolicHeatSummand_zero z rho).comp
        tendsto_reciprocalNatProperTime_zero)
  have hsum := tendsto_tsum_ennreal_of_monotone
    (fun n rho ↦ ENNReal.ofReal
      (zetaUpperHyperbolicHeatSummand z
        (reciprocalNatProperTime n) rho))
    (fun rho ↦ ENNReal.ofReal
      (4 * z.im * zetaUpperSpectralHeightSummand rho))
    (fun rho ↦ monotone_zetaUpperHyperbolicHeatSummand_reciprocal hz rho)
    hpointwise
  change Tendsto _ atTop
    (nhds (∑' rho : NontrivialZetaZero,
      ENNReal.ofReal
        (4 * z.im * zetaUpperSpectralHeightSummand rho)))
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦
    (ofReal_riemannXiUpperHyperbolicHeatSum_eq_tsum
      hz (reciprocalNatProperTime_pos n)).symm

/-- The lifted complete heat is monotone along reciprocal proper times. -/
theorem monotone_riemannXiUpperHyperbolicHeatSum_reciprocal
    {z : ℂ} (hz : 0 < z.im) :
    Monotone fun n ↦ ENNReal.ofReal
      (riemannXiUpperHyperbolicHeatSum z (reciprocalNatProperTime n)) := by
  intro n m hnm
  apply ENNReal.ofReal_le_ofReal
  exact riemannXiUpperHyperbolicHeatSum_le_of_time_le
    hz (reciprocalNatProperTime_pos m)
    (antitone_reciprocalNatProperTime hnm)

/-- Every positive-time lifted spectral heat is bounded above by the full
zero-time trace. -/
theorem ofReal_riemannXiUpperHyperbolicHeatSum_le_trace
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z tau) ≤
      riemannXiUpperHyperbolicHeatTrace z := by
  have hreciprocal : Tendsto reciprocalNatProperTime atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heventually : ∀ᶠ n in atTop,
      reciprocalNatProperTime n < tau :=
    (tendsto_order.1 hreciprocal).2 tau htau
  obtain ⟨n, hn⟩ := heventually.exists
  calc
    ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z tau) ≤
        ENNReal.ofReal (riemannXiUpperHyperbolicHeatSum z
          (reciprocalNatProperTime n)) :=
      ENNReal.ofReal_le_ofReal
        (riemannXiUpperHyperbolicHeatSum_le_of_time_le
          hz (reciprocalNatProperTime_pos n) hn.le)
    _ ≤ riemannXiUpperHyperbolicHeatTrace z :=
      (monotone_riemannXiUpperHyperbolicHeatSum_reciprocal hz).ge_of_tendsto
        (tendsto_riemannXiUpperHyperbolicHeatSum_reciprocal_zero hz) n

/-- The reciprocal-sequence result upgrades to the full one-sided
proper-time limit.  Thus no cofinal-sequence qualification remains: the
entire spectral heat approaches exactly the extended spectral height trace
as `tau → 0+`. -/
theorem tendsto_riemannXiUpperHyperbolicHeatSum_zero
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto
      (fun tau ↦ ENNReal.ofReal
        (riemannXiUpperHyperbolicHeatSum z tau))
      (nhdsWithin 0 (Ioi 0))
      (nhds (riemannXiUpperHyperbolicHeatTrace z)) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    have hsequence :=
      tendsto_riemannXiUpperHyperbolicHeatSum_reciprocal_zero hz
    have heventually : ∀ᶠ n in atTop, lower < ENNReal.ofReal
        (riemannXiUpperHyperbolicHeatSum z
          (reciprocalNatProperTime n)) :=
      (tendsto_order.1 hsequence).1 lower hlower
    obtain ⟨n, hn⟩ := heventually.exists
    have hsmall : ∀ᶠ tau in nhdsWithin 0 (Ioi 0),
        tau < reciprocalNatProperTime n :=
      nhdsWithin_le_nhds
        (Iio_mem_nhds (reciprocalNatProperTime_pos n))
    have hpositive : ∀ᶠ tau : ℝ in nhdsWithin 0 (Ioi 0), 0 < tau :=
      eventually_nhdsWithin_of_forall fun _ htau ↦ htau
    filter_upwards [hsmall, hpositive] with tau htauSmall htauPos
    exact hn.trans_le (ENNReal.ofReal_le_ofReal
      (riemannXiUpperHyperbolicHeatSum_le_of_time_le
        hz htauPos htauSmall.le))
  · intro upper hupper
    have hpositive : ∀ᶠ tau : ℝ in nhdsWithin 0 (Ioi 0), 0 < tau :=
      eventually_nhdsWithin_of_forall fun _ htau ↦ htau
    filter_upwards [hpositive] with tau htau
    exact (ofReal_riemannXiUpperHyperbolicHeatSum_le_trace
      hz htau).trans_lt hupper

/-- The full heat trace factors as the positive observation coefficient
times the observation-independent spectral height mass. -/
theorem riemannXiUpperHyperbolicHeatTrace_eq_heightMass
    {z : ℂ} (hz : 0 ≤ z.im) :
    riemannXiUpperHyperbolicHeatTrace z =
      ENNReal.ofReal (4 * z.im) * riemannXiUpperSpectralHeightMass := by
  unfold riemannXiUpperHyperbolicHeatTrace
    riemannXiUpperSpectralHeightMass
  have hcoefficient : 0 ≤ (4 : ℝ) * z.im :=
    mul_nonneg (by norm_num) hz
  simp_rw [ENNReal.ofReal_mul hcoefficient]
  exact ENNReal.tsum_mul_left

/-- Vanishing of the complete upper spectral height mass is exactly RH. -/
theorem riemannXiUpperSpectralHeightMass_eq_zero_iff_riemannHypothesis :
    riemannXiUpperSpectralHeightMass = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hsummand : 0 < zetaUpperSpectralHeightSummand rho := by
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    have hterm : 0 < ENNReal.ofReal
        (zetaUpperSpectralHeightSummand rho) := ENNReal.ofReal_pos.mpr hsummand
    have hle : ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) ≤
        riemannXiUpperSpectralHeightMass := by
      exact ENNReal.le_tsum rho
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    unfold riemannXiUpperSpectralHeightMass
    rw [ENNReal.tsum_eq_zero]
    intro rho
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    have hnupper : ¬0 < (zetaSpectralCoordinate rho.1).im := by
      linarith
    rw [zetaUpperSpectralHeightSummand, if_neg hnupper,
      ENNReal.ofReal_zero]

end

end RiemannGaussian
