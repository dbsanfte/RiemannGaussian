import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeAxisLargeHeight

/-!
# Large-height Poisson linearization of the safe-axis defect

The complete safe-axis logarithmic defect is nonlinear in each upper
spectral zero.  This module proves that the nonlinearity disappears in the
unscaled large-height limit.  At `z = i y`, the critical-strip bound gives
the uniform divisor gap `y - 1/2`.  The established logarithm-versus-Poisson
comparison then has relative excess

`2 y / (y - 1/2)^2`.

That excess is `O(1 / y)`, while the preceding module proves that the full
logarithmic defect is `o(y)`.  Their product is therefore `o(1)`: the real
complete logarithmic and Poisson defects differ by a quantity tending to
zero.  Consequently unscaled logarithmic-defect decay is equivalent to
decay of the positive Poisson defect, and hence to decay of `2 y` times the
complete elementary Blaschke derivative variation.  No form of RH is used.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The relative excess in the safe-axis logarithm-versus-Poisson
comparison. -/
def safeAxisLogPoissonComparisonExcess (y : ℝ) : ℝ :=
  2 * y / (y - 1 / 2) ^ 2

/-- The comparison excess is nonnegative throughout the safe large-height
region. -/
theorem safeAxisLogPoissonComparisonExcess_nonneg
    {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ safeAxisLogPoissonComparisonExcess y := by
  unfold safeAxisLogPoissonComparisonExcess
  positivity

/-- Every genuine spectral zero is uniformly separated from the imaginary
safe-axis point `i y` by at least `y - 1/2`. -/
theorem sub_half_le_norm_imaginary_sub_zetaSpectralCoordinate
    {y : ℝ} (hy : 1 ≤ y) (rho : NontrivialZetaZero) :
    y - 1 / 2 ≤
      ‖((y : ℂ) * Complex.I) - zetaSpectralCoordinate rho.1‖ := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hhalf : alpha.im < 1 / 2 := by
    dsimp [alpha]
    exact (le_abs_self _).trans_lt habs
  have hyalpha : 0 ≤ y - alpha.im := by linarith
  calc
    y - 1 / 2 ≤ y - alpha.im := by linarith
    _ = |((((y : ℂ) * Complex.I) - alpha).im)| := by
      rw [abs_of_nonneg]
      · simp
      · simpa using hyalpha
    _ ≤ ‖((y : ℂ) * Complex.I) - alpha‖ :=
      Complex.abs_im_le_norm _

/-- At every safe height, the complete logarithmic defect is bounded by the
complete Poisson defect times `1` plus the explicit comparison excess. -/
theorem
    riemannXiUpperHyperbolicLogDefectMass_imaginary_le_one_add_excess_mul_poisson
    {y : ℝ} (hy : 1 ≤ y) :
    riemannXiUpperHyperbolicLogDefectMass
        ((y : ℂ) * Complex.I) ≤
      ENNReal.ofReal (1 + safeAxisLogPoissonComparisonExcess y) *
        riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I) := by
  have hyPos : 0 < y := by linarith
  have hdelta : 0 < y - 1 / 2 := by linarith
  have hgap : ∀ rho : NontrivialZetaZero,
      0 < (zetaSpectralCoordinate rho.1).im →
        y - 1 / 2 ≤
          ‖((y : ℂ) * Complex.I) - zetaSpectralCoordinate rho.1‖ := by
    intro rho _hupper
    exact sub_half_le_norm_imaginary_sub_zetaSpectralCoordinate hy rho
  simpa [safeAxisLogPoissonComparisonExcess] using
    (riemannXiUpperHyperbolicLogDefectMass_le_gapCoefficient_mul_poissonMass
      (z := (y : ℂ) * Complex.I) (by simpa using hyPos) hdelta hgap)

/-- In real finite values, the Poisson defect lies below the logarithmic
defect, and their gap is bounded by the comparison excess times the full
logarithmic defect. -/
theorem safeAxisLogDefect_toReal_sub_poisson_bounds
    {y : ℝ} (hy : 1 ≤ y) :
    0 ≤
        (riemannXiUpperHyperbolicLogDefectMass
          ((y : ℂ) * Complex.I)).toReal -
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal ∧
      (riemannXiUpperHyperbolicLogDefectMass
          ((y : ℂ) * Complex.I)).toReal -
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal ≤
        safeAxisLogPoissonComparisonExcess y *
          (riemannXiUpperHyperbolicLogDefectMass
            ((y : ℂ) * Complex.I)).toReal := by
  let z : ℂ := (y : ℂ) * Complex.I
  let L : ℝ≥0∞ := riemannXiUpperHyperbolicLogDefectMass z
  let P : ℝ≥0∞ := riemannXiUpperHyperbolicPoissonDefectMass z
  let c : ℝ := safeAxisLogPoissonComparisonExcess y
  have hyPos : 0 < y := by linarith
  have hz : 0 < z.im := by simpa [z] using hyPos
  have hxi : riemannXiSpectral z ≠ 0 := by
    simpa [z] using riemannXiSpectral_ne_zero_imaginarySafeAxis hy
  have hLtop : L ≠ ∞ := by
    exact riemannXiUpperHyperbolicLogDefectMass_ne_top hz hxi
  have hPtop : P ≠ ∞ := by
    exact riemannXiUpperHyperbolicPoissonDefectMass_ne_top hz
  have hc : 0 ≤ c := by
    exact safeAxisLogPoissonComparisonExcess_nonneg hy
  have hPLenn : P ≤ L := by
    exact riemannXiUpperHyperbolicPoissonDefectMass_le_logDefectMass hz hxi
  have hPL : P.toReal ≤ L.toReal := by
    exact ENNReal.toReal_mono hLtop hPLenn
  have hLPenn : L ≤ ENNReal.ofReal (1 + c) * P := by
    simpa [L, P, c, z] using
      riemannXiUpperHyperbolicLogDefectMass_imaginary_le_one_add_excess_mul_poisson
        hy
  have hproductTop : ENNReal.ofReal (1 + c) * P ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPtop
  have hLP : L.toReal ≤ (1 + c) * P.toReal := by
    calc
      L.toReal ≤ (ENNReal.ofReal (1 + c) * P).toReal :=
        ENNReal.toReal_mono hproductTop hLPenn
      _ = (1 + c) * P.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
        positivity
  change 0 ≤ L.toReal - P.toReal ∧
    L.toReal - P.toReal ≤ c * L.toReal
  constructor
  · linarith
  · calc
      L.toReal - P.toReal ≤ c * P.toReal := by
        nlinarith
      _ ≤ c * L.toReal := mul_le_mul_of_nonneg_left hPL hc

/-- Multiplying the comparison excess by the observation height has the
finite limit `2`. -/
theorem tendsto_safeAxisLogPoissonComparisonExcess_mul_atTop_two :
    Tendsto (fun y : ℝ ↦ safeAxisLogPoissonComparisonExcess y * y)
      atTop (nhds 2) := by
  have hsmall : Tendsto (fun y : ℝ ↦ (1 / 2 : ℝ) / y)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hbase : Tendsto (fun y : ℝ ↦ 1 - (1 / 2 : ℝ) / y)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hsmall
  have hraw : Tendsto
      (fun y : ℝ ↦ 2 / (1 - (1 / 2 : ℝ) / y) ^ 2)
      atTop (nhds 2) := by
    change Tendsto
      ((fun _ : ℝ ↦ (2 : ℝ)) /
        (fun y : ℝ ↦ (1 - (1 / 2 : ℝ) / y) ^ 2))
      atTop (nhds 2)
    simpa only [one_pow, div_one] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (nhds 2)).div
          (hbase.pow 2) (by norm_num))
  apply hraw.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy0 : y ≠ 0 := by linarith
  have hsub : y - 1 / 2 ≠ 0 := by linarith
  unfold safeAxisLogPoissonComparisonExcess
  field_simp [hy0, hsub]

/-- The nonlinear complete logarithmic defect and its linear Poisson defect
have vanishing absolute gap at infinite safe-axis height. -/
theorem
    tendsto_riemannXiUpperHyperbolicLogDefectMass_toReal_sub_poissonDefectMass_toReal_imaginary_atTop_zero
    :
    Tendsto
      (fun y : ℝ ↦
        (riemannXiUpperHyperbolicLogDefectMass
          ((y : ℂ) * Complex.I)).toReal -
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal)
      atTop (nhds 0) := by
  have henvelope : Tendsto
      (fun y : ℝ ↦ safeAxisLogPoissonComparisonExcess y *
        (riemannXiUpperHyperbolicLogDefectMass
          ((y : ℂ) * Complex.I)).toReal)
      atTop (nhds 0) := by
    have hproduct : Tendsto
        (fun y : ℝ ↦
          (safeAxisLogPoissonComparisonExcess y * y) *
            ((riemannXiUpperHyperbolicLogDefectMass
              ((y : ℂ) * Complex.I)).toReal / y))
        atTop (nhds 0) := by
      simpa using
        tendsto_safeAxisLogPoissonComparisonExcess_mul_atTop_two.mul
          tendsto_riemannXiUpperHyperbolicLogDefectMass_imaginary_toReal_div_atTop_zero
    exact hproduct.congr' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      have hy0 : y ≠ 0 := by linarith
      field_simp [hy0])
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (safeAxisLogDefect_toReal_sub_poisson_bounds hy).1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact (safeAxisLogDefect_toReal_sub_poisson_bounds hy).2
  · exact henvelope

/-- Unscaled decay of the complete logarithmic defect is equivalent to
unscaled decay of its positive Poisson linearization. -/
theorem
    tendsto_safeAxisLogDefect_toReal_zero_iff_poissonDefect_toReal_zero :
    Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicLogDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) ↔
      Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicPoissonDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) := by
  let L : ℝ → ℝ := fun y ↦
    (riemannXiUpperHyperbolicLogDefectMass
      ((y : ℂ) * Complex.I)).toReal
  let P : ℝ → ℝ := fun y ↦
    (riemannXiUpperHyperbolicPoissonDefectMass
      ((y : ℂ) * Complex.I)).toReal
  have hgap : Tendsto (fun y : ℝ ↦ L y - P y) atTop (nhds 0) := by
    simpa [L, P] using
      tendsto_riemannXiUpperHyperbolicLogDefectMass_toReal_sub_poissonDefectMass_toReal_imaginary_atTop_zero
  constructor
  · intro hL
    have h := hL.sub hgap
    convert h using 1
    · funext y
      dsimp [L, P]
      ring_nf
    · ring_nf
  · intro hP
    have h := hP.add hgap
    convert h using 1
    · funext y
      dsimp [L, P]
      ring_nf
    · ring_nf

/-- On the safe axis, the real Poisson defect is exactly `2 y` times the
complete elementary Blaschke derivative variation. -/
theorem
    riemannXiUpperHyperbolicPoissonDefectMass_imaginary_toReal_eq_two_mul_height_mul_variation
    {y : ℝ} (hy : 1 ≤ y) :
    (riemannXiUpperHyperbolicPoissonDefectMass
        ((y : ℂ) * Complex.I)).toReal =
      2 * y *
        (riemannXiUpperBlaschkeDerivativeVariationMass
          ((y : ℂ) * Complex.I)).toReal := by
  have hyPos : 0 < y := by linarith
  have htwo : 0 ≤ 2 * (((y : ℂ) * Complex.I).im) := by
    simpa using (show 0 ≤ 2 * y by positivity)
  rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_two_im_mul_variationMass
      (by simpa using hyPos),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal htwo]
  simp

/-- Terminal linearized frontier.  Unscaled decay of the complete
RH-detecting logarithmic defect is exactly decay of the height-scaled
positive Blaschke derivative variation.  The preceding asymptotic-gap
theorem proves that this is a lossless large-height replacement, rather than
an assumed approximation. -/
theorem
    tendsto_safeAxisLogDefect_toReal_zero_iff_height_mul_blaschkeVariation_zero
    :
    Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicLogDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) ↔
      Tendsto
        (fun y : ℝ ↦
          2 * y *
            (riemannXiUpperBlaschkeDerivativeVariationMass
              ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) := by
  rw [tendsto_safeAxisLogDefect_toReal_zero_iff_poissonDefect_toReal_zero]
  constructor
  · intro hP
    apply hP.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact
      riemannXiUpperHyperbolicPoissonDefectMass_imaginary_toReal_eq_two_mul_height_mul_variation
        hy
  · intro hV
    apply hV.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact
      (riemannXiUpperHyperbolicPoissonDefectMass_imaginary_toReal_eq_two_mul_height_mul_variation
        hy).symm

end

end RiemannGaussian
