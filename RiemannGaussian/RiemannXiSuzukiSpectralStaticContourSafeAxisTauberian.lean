import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeAxisPoissonAsymptotic

/-!
# A Tauberian law for the safe-axis Poisson defect

The safe-axis Poisson defect is a positive smoothing of the multiplicity-
weighted upper spectral height measure.  This module proves the corresponding
two-sided Tauberian statement: its unscaled decay is equivalent to sublinear
growth of the cumulative upper-height mass in symmetric ordinate windows.

The hard implication is quantitative.  A central window contributes at most
four times its normalized height mass.  Successive dyadic ordinate shells
contribute a geometric tail, giving a uniform factor `20`.  Conversely, on
the central window the Poisson kernel is bounded below by `1 / y`, so Poisson
decay forces sublinear cumulative mass.  All sums retain analytic zero
multiplicity, and no form of RH is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The real multiplicity-weighted upper spectral height accumulated over
the symmetric ordinate window `|Re alpha| <= T`. -/
def riemannXiUpperSpectralHeightCumulative (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaUpperSpectralHeightSummand rho

/-- The real safe-axis Poisson mass in the same finite ordinate window. -/
def riemannXiUpperSafeAxisPoissonCumulative (y T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaUpperHyperbolicPoissonDefectSummand
      ((y : ℂ) * Complex.I) rho

/-- Cumulative upper spectral height is nonnegative. -/
theorem riemannXiUpperSpectralHeightCumulative_nonneg (T : ℝ) :
    0 ≤ riemannXiUpperSpectralHeightCumulative T := by
  unfold riemannXiUpperSpectralHeightCumulative
  exact Finset.sum_nonneg fun rho _ ↦
    zetaUpperSpectralHeightSummand_nonneg rho

/-- Every finite safe-axis Poisson window is nonnegative at positive height. -/
theorem riemannXiUpperSafeAxisPoissonCumulative_nonneg
    {y : ℝ} (hy : 0 < y) (T : ℝ) :
    0 ≤ riemannXiUpperSafeAxisPoissonCumulative y T := by
  unfold riemannXiUpperSafeAxisPoissonCumulative
  exact Finset.sum_nonneg fun rho _ ↦
    zetaUpperHyperbolicPoissonDefectSummand_nonneg (by simpa using hy) rho

/-- Symmetric spectral windows are monotone in their nonnegative radius. -/
theorem spectralZetaZeroWindow_subset
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    spectralZetaZeroWindow S ⊆ spectralZetaZeroWindow T := by
  intro rho hrho
  apply (mem_spectralZetaZeroWindow (hS.trans hST) rho).mpr
  exact ((mem_spectralZetaZeroWindow hS rho).mp hrho).trans hST

/-- The real cumulative upper-height mass is monotone on nonnegative
radii. -/
theorem riemannXiUpperSpectralHeightCumulative_mono
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) :
    riemannXiUpperSpectralHeightCumulative S ≤
      riemannXiUpperSpectralHeightCumulative T := by
  unfold riemannXiUpperSpectralHeightCumulative
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (spectralZetaZeroWindow_subset hS hST)
    (fun rho _ _ ↦ zetaUpperSpectralHeightSummand_nonneg rho)

/-- On the imaginary axis the reflected-zero denominator has the elementary
real-coordinate form `gamma^2 + (y + a)^2`. -/
theorem normSq_imaginary_sub_conj_zetaSpectralCoordinate
    (y : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq
        (((y : ℂ) * Complex.I) -
          starRingEnd ℂ (zetaSpectralCoordinate rho.1)) =
      (zetaSpectralCoordinate rho.1).re ^ 2 +
        (y + (zetaSpectralCoordinate rho.1).im) ^ 2 := by
  unfold Complex.normSq
  simp
  ring

/-- The safe-axis Poisson contribution of one zero never exceeds four times
its upper-height contribution divided by the observation height. -/
theorem zetaUpperSafeAxisPoissonSummand_le_four_div_mul_height
    {y : ℝ} (hy : 0 < y) (rho : NontrivialZetaZero) :
    zetaUpperHyperbolicPoissonDefectSummand
        ((y : ℂ) * Complex.I) rho ≤
      (4 / y) * zetaUpperSpectralHeightSummand rho := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  by_cases hupper : 0 < alpha.im
  · have hden : 0 < alpha.re ^ 2 + (y + alpha.im) ^ 2 := by
      positivity
    have hySq : 0 < y ^ 2 := sq_pos_of_pos hy
    have hdenLower : y ^ 2 ≤ alpha.re ^ 2 + (y + alpha.im) ^ 2 := by
      nlinarith [sq_nonneg alpha.re]
    have hcore :
        4 * y * alpha.im /
            (alpha.re ^ 2 + (y + alpha.im) ^ 2) ≤
          (4 / y) * alpha.im := by
      calc
        4 * y * alpha.im /
              (alpha.re ^ 2 + (y + alpha.im) ^ 2) ≤
            4 * y * alpha.im / y ^ 2 := by
              exact div_le_div_of_nonneg_left (by positivity) hySq hdenLower
        _ = (4 / y) * alpha.im := by
          field_simp [hy.ne']
    rw [zetaUpperHyperbolicPoissonDefectSummand,
      zetaUpperSpectralHeightSummand]
    simp only [alpha] at hupper ⊢
    rw [if_pos hupper, if_pos hupper,
      normSq_imaginary_sub_conj_zetaSpectralCoordinate]
    have hmul := mul_le_mul_of_nonneg_left hcore
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho))
    convert hmul using 1
    · rfl
    · simp [alpha]
    · simp only [alpha]
      ring
  · rw [zetaUpperHyperbolicPoissonDefectSummand,
      zetaUpperSpectralHeightSummand]
    simp only [alpha] at hupper ⊢
    rw [if_neg hupper, if_neg hupper, mul_zero]

/-- Inside the central ordinate window `|gamma| <= y`, and above safe height
one, the upper-height contribution divided by `y` is bounded by its Poisson
contribution. -/
theorem zetaUpperHeight_div_le_safeAxisPoissonSummand
    {y : ℝ} (hy : 1 ≤ y) (rho : NontrivialZetaZero)
    (hrho : |(zetaSpectralCoordinate rho.1).re| ≤ y) :
    zetaUpperSpectralHeightSummand rho / y ≤
      zetaUpperHyperbolicPoissonDefectSummand
        ((y : ℂ) * Complex.I) rho := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  have hyPos : 0 < y := by linarith
  by_cases hupper : 0 < alpha.im
  · have hhalf : alpha.im ≤ 1 / 2 := by
      exact (le_abs_self alpha.im).trans
        (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le
    have hgammaBounds : -y ≤ alpha.re ∧ alpha.re ≤ y := by
      simpa [alpha] using (abs_le.mp hrho)
    have hgammaSq : alpha.re ^ 2 ≤ y ^ 2 := by
      have hprod : 0 ≤ (y - alpha.re) * (y + alpha.re) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hyAlpha : 0 ≤ y + alpha.im := by linarith
    have hthreeHalf : 0 ≤ (3 / 2 : ℝ) * y := by positivity
    have hyAlphaLe : y + alpha.im ≤ (3 / 2 : ℝ) * y := by
      linarith
    have hyAlphaSq :
        (y + alpha.im) ^ 2 ≤ ((3 / 2 : ℝ) * y) ^ 2 := by
      have hprod :
          0 ≤ (((3 / 2 : ℝ) * y) - (y + alpha.im)) *
            (((3 / 2 : ℝ) * y) + (y + alpha.im)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hdenUpper :
        alpha.re ^ 2 + (y + alpha.im) ^ 2 ≤ 4 * y ^ 2 := by
      nlinarith [sq_nonneg y]
    have hden : 0 < alpha.re ^ 2 + (y + alpha.im) ^ 2 := by
      positivity
    have hheightCross :
        alpha.im * (alpha.re ^ 2 + (y + alpha.im) ^ 2) ≤
          4 * y ^ 2 * alpha.im :=
      by simpa [mul_comm] using
        (mul_le_mul_of_nonneg_right hdenUpper hupper.le)
    have hheight :
        alpha.im ≤
          4 * y ^ 2 * alpha.im /
            (alpha.re ^ 2 + (y + alpha.im) ^ 2) := by
      exact (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hheightCross)
    have hcore :
        alpha.im / y ≤
          4 * y * alpha.im /
            (alpha.re ^ 2 + (y + alpha.im) ^ 2) := by
      calc
        alpha.im / y ≤
            (4 * y ^ 2 * alpha.im /
              (alpha.re ^ 2 + (y + alpha.im) ^ 2)) / y :=
          (div_le_div_iff_of_pos_right hyPos).2 hheight
        _ = 4 * y * alpha.im /
              (alpha.re ^ 2 + (y + alpha.im) ^ 2) := by
          field_simp [hden.ne', hyPos.ne']
    rw [zetaUpperSpectralHeightSummand,
      zetaUpperHyperbolicPoissonDefectSummand]
    simp only [alpha] at hupper ⊢
    rw [if_pos hupper, if_pos hupper,
      normSq_imaginary_sub_conj_zetaSpectralCoordinate]
    have hmul := mul_le_mul_of_nonneg_left hcore
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho))
    convert hmul using 1
    · rfl
    · simp only [alpha]
      ring
    · simp [alpha]
  · rw [zetaUpperSpectralHeightSummand,
      zetaUpperHyperbolicPoissonDefectSummand]
    simp only [alpha] at hupper ⊢
    rw [if_neg hupper, if_neg hupper, zero_div]

/-- Outside an ordinate radius `r`, one Poisson contribution is bounded by
`4 y / r^2` times its upper-height contribution. -/
theorem zetaUpperSafeAxisPoissonSummand_le_of_ordinate_ge
    {y r : ℝ} (hy : 0 < y) (hr : 0 < r)
    (rho : NontrivialZetaZero)
    (hrho : r ≤ |(zetaSpectralCoordinate rho.1).re|) :
    zetaUpperHyperbolicPoissonDefectSummand
        ((y : ℂ) * Complex.I) rho ≤
      (4 * y / r ^ 2) * zetaUpperSpectralHeightSummand rho := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  by_cases hupper : 0 < alpha.im
  · have hrSq : 0 < r ^ 2 := sq_pos_of_pos hr
    have hsquare : r ^ 2 ≤ alpha.re ^ 2 := by
      have hprod : 0 ≤ (|alpha.re| - r) * (|alpha.re| + r) := by
        apply mul_nonneg
        · simpa [alpha] using sub_nonneg.mpr hrho
        · positivity
      nlinarith [sq_abs alpha.re]
    have hdenLower :
        r ^ 2 ≤ alpha.re ^ 2 + (y + alpha.im) ^ 2 := by
      nlinarith [sq_nonneg (y + alpha.im)]
    have hcore :
        4 * y * alpha.im /
            (alpha.re ^ 2 + (y + alpha.im) ^ 2) ≤
          (4 * y / r ^ 2) * alpha.im := by
      calc
        4 * y * alpha.im /
              (alpha.re ^ 2 + (y + alpha.im) ^ 2) ≤
            4 * y * alpha.im / r ^ 2 := by
              exact div_le_div_of_nonneg_left (by positivity) hrSq hdenLower
        _ = (4 * y / r ^ 2) * alpha.im := by ring
    rw [zetaUpperHyperbolicPoissonDefectSummand,
      zetaUpperSpectralHeightSummand]
    simp only [alpha] at hupper ⊢
    rw [if_pos hupper, if_pos hupper,
      normSq_imaginary_sub_conj_zetaSpectralCoordinate]
    have hmul := mul_le_mul_of_nonneg_left hcore
      (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho))
    convert hmul using 1
    · rfl
    · simp [alpha]
    · simp only [alpha]
      ring
  · rw [zetaUpperHyperbolicPoissonDefectSummand,
      zetaUpperSpectralHeightSummand]
    simp only [alpha] at hupper ⊢
    rw [if_neg hupper, if_neg hupper, mul_zero]

/-- The central cumulative height divided by `y` is bounded by the central
Poisson window. -/
theorem upperSpectralHeightCumulative_div_le_safeAxisPoissonCumulative
    {y : ℝ} (hy : 1 ≤ y) :
    riemannXiUpperSpectralHeightCumulative y / y ≤
      riemannXiUpperSafeAxisPoissonCumulative y y := by
  unfold riemannXiUpperSpectralHeightCumulative
    riemannXiUpperSafeAxisPoissonCumulative
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro rho hrho
  exact zetaUpperHeight_div_le_safeAxisPoissonSummand hy rho
    ((mem_spectralZetaZeroWindow (by linarith) rho).mp hrho)

/-- The central Poisson window is at most four times the normalized
cumulative upper-height mass. -/
theorem upperSafeAxisPoissonCumulative_le_four_div_mul_heightCumulative
    {y : ℝ} (hy : 0 < y) :
    riemannXiUpperSafeAxisPoissonCumulative y y ≤
      (4 / y) * riemannXiUpperSpectralHeightCumulative y := by
  unfold riemannXiUpperSafeAxisPoissonCumulative
    riemannXiUpperSpectralHeightCumulative
  calc
    (∑ rho ∈ spectralZetaZeroWindow y,
        zetaUpperHyperbolicPoissonDefectSummand
          ((y : ℂ) * Complex.I) rho) ≤
        ∑ rho ∈ spectralZetaZeroWindow y,
          (4 / y) * zetaUpperSpectralHeightSummand rho := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact zetaUpperSafeAxisPoissonSummand_le_four_div_mul_height hy rho
    _ = (4 / y) *
        ∑ rho ∈ spectralZetaZeroWindow y,
          zetaUpperSpectralHeightSummand rho := by
      rw [Finset.mul_sum]

/-- The finite safe-axis Poisson windows converge to the real value of the
complete Poisson mass. -/
theorem tendsto_riemannXiUpperSafeAxisPoissonCumulative
    {y : ℝ} (hy : 0 < y) :
    Tendsto (riemannXiUpperSafeAxisPoissonCumulative y) atTop
      (nhds
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal) := by
  have hz : 0 < (((y : ℂ) * Complex.I).im) := by simpa using hy
  have hsum :=
    (summable_zetaUpperHyperbolicPoissonDefectSummand hz).hasSum.comp
      tendsto_spectralZetaZeroWindow_atTop
  rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_ofReal_tsum hz,
    ENNReal.toReal_ofReal
      (tsum_nonneg
        (zetaUpperHyperbolicPoissonDefectSummand_nonneg hz))]
  change Tendsto
    (fun T : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaUpperHyperbolicPoissonDefectSummand
          ((y : ℂ) * Complex.I) rho)
    atTop
    (nhds
      (∑' rho : NontrivialZetaZero,
        zetaUpperHyperbolicPoissonDefectSummand
          ((y : ℂ) * Complex.I) rho))
  change Tendsto
    (fun T : ℝ ↦
      ∑ rho ∈ spectralZetaZeroWindow T,
        zetaUpperHyperbolicPoissonDefectSummand
          ((y : ℂ) * Complex.I) rho)
    atTop
    (nhds
      (∑' rho : NontrivialZetaZero,
        zetaUpperHyperbolicPoissonDefectSummand
          ((y : ℂ) * Complex.I) rho)) at hsum
  exact hsum

/-- Every finite safe-axis Poisson window lies below the complete real
Poisson mass. -/
theorem riemannXiUpperSafeAxisPoissonCumulative_le_mass_toReal
    {y : ℝ} (hy : 0 < y) (T : ℝ) :
    riemannXiUpperSafeAxisPoissonCumulative y T ≤
      (riemannXiUpperHyperbolicPoissonDefectMass
        ((y : ℂ) * Complex.I)).toReal := by
  have hz : 0 < (((y : ℂ) * Complex.I).im) := by simpa using hy
  rw [riemannXiUpperHyperbolicPoissonDefectMass_eq_ofReal_tsum hz,
    ENNReal.toReal_ofReal
      (tsum_nonneg
        (zetaUpperHyperbolicPoissonDefectSummand_nonneg hz))]
  unfold riemannXiUpperSafeAxisPoissonCumulative
  exact (summable_zetaUpperHyperbolicPoissonDefectSummand hz).sum_le_tsum
    (spectralZetaZeroWindow T)
    (fun rho _ ↦ zetaUpperHyperbolicPoissonDefectSummand_nonneg hz rho)

/-- Adding one outer ordinate shell costs at most its cumulative height mass
times the inverse-square kernel at the inner radius. -/
theorem upperSafeAxisPoissonCumulative_outer_le_inner_add
    {y r R : ℝ} (hy : 0 < y) (hr : 0 < r) (hrR : r ≤ R) :
    riemannXiUpperSafeAxisPoissonCumulative y R ≤
      riemannXiUpperSafeAxisPoissonCumulative y r +
        (4 * y / r ^ 2) *
          riemannXiUpperSpectralHeightCumulative R := by
  let inner := spectralZetaZeroWindow r
  let outer := spectralZetaZeroWindow R
  let p : NontrivialZetaZero → ℝ :=
    zetaUpperHyperbolicPoissonDefectSummand ((y : ℂ) * Complex.I)
  let h : NontrivialZetaZero → ℝ := zetaUpperSpectralHeightSummand
  let c : ℝ := 4 * y / r ^ 2
  have hsubset : inner ⊆ outer := by
    exact spectralZetaZeroWindow_subset hr.le hrR
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hshellTerm : ∀ rho ∈ outer \ inner, p rho ≤ c * h rho := by
    intro rho hrho
    have hnotInner : rho ∉ inner := (Finset.mem_sdiff.mp hrho).2
    have hordinate : r ≤ |(zetaSpectralCoordinate rho.1).re| := by
      apply (not_le.mp ?_).le
      intro hle
      apply hnotInner
      exact (mem_spectralZetaZeroWindow hr.le rho).mpr hle
    exact zetaUpperSafeAxisPoissonSummand_le_of_ordinate_ge
      hy hr rho hordinate
  have hshellHeight :
      ∑ rho ∈ outer \ inner, h rho ≤ ∑ rho ∈ outer, h rho := by
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun rho _ _ ↦ zetaUpperSpectralHeightSummand_nonneg rho)
  have hdecomp := Finset.sum_sdiff hsubset (f := p)
  change
    (∑ rho ∈ outer \ inner, p rho) + ∑ rho ∈ inner, p rho =
      ∑ rho ∈ outer, p rho at hdecomp
  change
    (∑ rho ∈ outer, p rho) ≤
      (∑ rho ∈ inner, p rho) + c * ∑ rho ∈ outer, h rho
  calc
    (∑ rho ∈ outer, p rho) =
        (∑ rho ∈ outer \ inner, p rho) +
          ∑ rho ∈ inner, p rho := hdecomp.symm
    _ ≤ (∑ rho ∈ outer \ inner, c * h rho) +
          ∑ rho ∈ inner, p rho := by
      exact add_le_add (Finset.sum_le_sum hshellTerm) le_rfl
    _ = (∑ rho ∈ inner, p rho) +
        c * ∑ rho ∈ outer \ inner, h rho := by
      rw [Finset.mul_sum]
      ring
    _ ≤ (∑ rho ∈ inner, p rho) +
        c * ∑ rho ∈ outer, h rho := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hshellHeight hc)

/-- The coefficient from the `n`th dyadic shell has the exact geometric
form used in the Tauberian estimate. -/
theorem dyadicSafeAxisShellCoefficient
    {y : ℝ} (hy : 0 < y) (epsilon : ℝ) (n : ℕ) :
    (4 * y / (((2 : ℝ) ^ n * y) ^ 2)) *
        (epsilon * ((2 : ℝ) ^ (n + 1) * y)) =
      8 * epsilon * (1 / 2 : ℝ) ^ n := by
  rw [pow_succ, div_pow]
  norm_num
  field_simp [hy.ne', (pow_pos (by norm_num : (0 : ℝ) < 2) n).ne']
  ring

/-- Quantitative dyadic Tauberian estimate for every finite outer window.
If cumulative upper height is bounded by `epsilon * T` above `y`, the
Poisson mass through the `n`th dyadic window is controlled by the associated
partial geometric series. -/
theorem upperSafeAxisPoissonCumulative_dyadic_le
    {y epsilon : ℝ} (hy : 1 ≤ y)
    (hheight : ∀ T : ℝ, y ≤ T →
      riemannXiUpperSpectralHeightCumulative T ≤ epsilon * T) :
    ∀ n : ℕ,
      riemannXiUpperSafeAxisPoissonCumulative y
          ((2 : ℝ) ^ n * y) ≤
        4 * epsilon +
          8 * epsilon *
            ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
  intro n
  induction n with
  | zero =>
      have hyPos : 0 < y := by linarith
      simpa using
        (calc
          riemannXiUpperSafeAxisPoissonCumulative y y ≤
              (4 / y) * riemannXiUpperSpectralHeightCumulative y :=
            upperSafeAxisPoissonCumulative_le_four_div_mul_heightCumulative
              hyPos
          _ ≤ (4 / y) * (epsilon * y) := by
            exact mul_le_mul_of_nonneg_left (hheight y le_rfl) (by positivity)
          _ = 4 * epsilon := by
            field_simp [hyPos.ne'])
  | succ n ih =>
      let r : ℝ := (2 : ℝ) ^ n * y
      let R : ℝ := (2 : ℝ) ^ (n + 1) * y
      have hyPos : 0 < y := by linarith
      have hr : 0 < r := by
        dsimp [r]
        positivity
      have hrR : r ≤ R := by
        dsimp [r, R]
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
      have hyR : y ≤ R := by
        dsimp [R]
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
          one_le_pow₀ (by norm_num)
        nlinarith
      have hcoefficient : 0 ≤ 4 * y / r ^ 2 := by positivity
      calc
        riemannXiUpperSafeAxisPoissonCumulative y
            ((2 : ℝ) ^ (n + 1) * y) =
            riemannXiUpperSafeAxisPoissonCumulative y R := by rfl
        _ ≤ riemannXiUpperSafeAxisPoissonCumulative y r +
              (4 * y / r ^ 2) *
                riemannXiUpperSpectralHeightCumulative R :=
          upperSafeAxisPoissonCumulative_outer_le_inner_add
            hyPos hr hrR
        _ ≤ (4 * epsilon +
                8 * epsilon *
                  ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) +
              (4 * y / r ^ 2) * (epsilon * R) := by
          exact add_le_add ih
            (mul_le_mul_of_nonneg_left (hheight R hyR) hcoefficient)
        _ = 4 * epsilon +
              8 * epsilon *
                ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k := by
          rw [Finset.sum_range_succ]
          rw [show (4 * y / r ^ 2) * (epsilon * R) =
              8 * epsilon * (1 / 2 : ℝ) ^ n by
            simpa [r, R] using dyadicSafeAxisShellCoefficient hyPos epsilon n]
          ring

/-- Uniform full-divisor form of the dyadic estimate.  A sublinear bound
with coefficient `epsilon` on all windows above `y` forces the complete
safe-axis Poisson mass at height `y` below `20 * epsilon`. -/
theorem safeAxisPoissonMass_toReal_le_twenty_mul
    {y epsilon : ℝ} (hy : 1 ≤ y) (hepsilon : 0 ≤ epsilon)
    (hheight : ∀ T : ℝ, y ≤ T →
      riemannXiUpperSpectralHeightCumulative T ≤ epsilon * T) :
    (riemannXiUpperHyperbolicPoissonDefectMass
        ((y : ℂ) * Complex.I)).toReal ≤
      20 * epsilon := by
  have hyPos : 0 < y := by linarith
  have hradius : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n * y)
      atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hyPos
  have hwindow :=
    (tendsto_riemannXiUpperSafeAxisPoissonCumulative hyPos).comp hradius
  apply le_of_tendsto hwindow
  exact Eventually.of_forall fun n ↦
    calc
      riemannXiUpperSafeAxisPoissonCumulative y
          ((2 : ℝ) ^ n * y) ≤
          4 * epsilon +
            8 * epsilon *
              ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k :=
        upperSafeAxisPoissonCumulative_dyadic_le hy hheight n
      _ ≤ 4 * epsilon + 8 * epsilon * 2 := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (sum_geometric_two_le n)
            (mul_nonneg (by norm_num) hepsilon))
      _ = 20 * epsilon := by ring

/-- The normalized central cumulative height is bounded by the complete
safe-axis Poisson mass. -/
theorem upperSpectralHeightCumulative_div_le_safeAxisPoissonMass_toReal
    {y : ℝ} (hy : 1 ≤ y) :
    riemannXiUpperSpectralHeightCumulative y / y ≤
      (riemannXiUpperHyperbolicPoissonDefectMass
        ((y : ℂ) * Complex.I)).toReal := by
  calc
    riemannXiUpperSpectralHeightCumulative y / y ≤
        riemannXiUpperSafeAxisPoissonCumulative y y :=
      upperSpectralHeightCumulative_div_le_safeAxisPoissonCumulative hy
    _ ≤
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal :=
      riemannXiUpperSafeAxisPoissonCumulative_le_mass_toReal
        (by linarith) y

/-- Safe-axis Poisson decay forces sublinear cumulative upper spectral
height. -/
theorem tendsto_upperSpectralHeightCumulative_div_zero_of_safeAxisPoisson
    (hpoisson :
      Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicPoissonDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0)) :
    Tendsto
      (fun T : ℝ ↦ riemannXiUpperSpectralHeightCumulative T / T)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact div_nonneg
      (riemannXiUpperSpectralHeightCumulative_nonneg T) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact upperSpectralHeightCumulative_div_le_safeAxisPoissonMass_toReal hT
  · exact hpoisson

/-- Sublinear cumulative upper spectral height forces safe-axis Poisson
decay.  The proof uses the explicit `20 * epsilon` dyadic estimate rather
than any exchange of an infinite zero sum with a height limit. -/
theorem tendsto_safeAxisPoisson_of_upperSpectralHeightCumulative_div_zero
    (hheight :
      Tendsto
        (fun T : ℝ ↦ riemannXiUpperSpectralHeightCumulative T / T)
        atTop (nhds 0)) :
    Tendsto
      (fun y : ℝ ↦
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal)
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eta heta
  let epsilon : ℝ := eta / 21
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨Y, hY⟩ :=
    (Metric.tendsto_atTop.mp hheight) epsilon hepsilon
  refine ⟨max 1 Y, fun y hy ↦ ?_⟩
  have hyOne : 1 ≤ y := (le_max_left 1 Y).trans hy
  have hyY : Y ≤ y := (le_max_right 1 Y).trans hy
  have hlinear : ∀ T : ℝ, y ≤ T →
      riemannXiUpperSpectralHeightCumulative T ≤ epsilon * T := by
    intro T hyT
    have hTOne : 1 ≤ T := hyOne.trans hyT
    have hTY : Y ≤ T := hyY.trans hyT
    have hratioAbs :
        |riemannXiUpperSpectralHeightCumulative T / T| < epsilon := by
      have h := hY T hTY
      rw [Real.dist_eq, sub_zero] at h
      exact h
    have hratio :
        riemannXiUpperSpectralHeightCumulative T / T < epsilon :=
      (le_abs_self _).trans_lt hratioAbs
    exact ((div_lt_iff₀ (by linarith : 0 < T)).mp hratio).le
  have hbound := safeAxisPoissonMass_toReal_le_twenty_mul
    hyOne hepsilon.le hlinear
  have hmassNonneg :
      0 ≤
        (riemannXiUpperHyperbolicPoissonDefectMass
          ((y : ℂ) * Complex.I)).toReal := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hmassNonneg]
  exact hbound.trans_lt (by
    dsimp [epsilon]
    linarith)

/-- Tauberian equivalence at the current safe-axis frontier: unscaled
Poisson decay is exactly sublinear growth of the cumulative
multiplicity-weighted upper spectral height. -/
theorem tendsto_safeAxisPoisson_toReal_zero_iff_upperSpectralHeight_sublinear :
    Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicPoissonDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) ↔
      Tendsto
        (fun T : ℝ ↦ riemannXiUpperSpectralHeightCumulative T / T)
        atTop (nhds 0) := by
  exact ⟨
    tendsto_upperSpectralHeightCumulative_div_zero_of_safeAxisPoisson,
    tendsto_safeAxisPoisson_of_upperSpectralHeightCumulative_div_zero⟩

/-- The nonlinear safe-axis logarithmic defect has the same Tauberian
criterion, by the previously proved lossless Poisson linearization. -/
theorem tendsto_safeAxisLogDefect_toReal_zero_iff_upperSpectralHeight_sublinear :
    Tendsto
        (fun y : ℝ ↦
          (riemannXiUpperHyperbolicLogDefectMass
            ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) ↔
      Tendsto
        (fun T : ℝ ↦ riemannXiUpperSpectralHeightCumulative T / T)
        atTop (nhds 0) := by
  rw [tendsto_safeAxisLogDefect_toReal_zero_iff_poissonDefect_toReal_zero,
    tendsto_safeAxisPoisson_toReal_zero_iff_upperSpectralHeight_sublinear]

/-- Equivalently, decay of the height-scaled complete Blaschke derivative
variation is precisely the same sublinear cumulative-height law. -/
theorem
    tendsto_height_mul_blaschkeVariation_zero_iff_upperSpectralHeight_sublinear
    :
    Tendsto
        (fun y : ℝ ↦
          2 * y *
            (riemannXiUpperBlaschkeDerivativeVariationMass
              ((y : ℂ) * Complex.I)).toReal)
        atTop (nhds 0) ↔
      Tendsto
        (fun T : ℝ ↦ riemannXiUpperSpectralHeightCumulative T / T)
        atTop (nhds 0) := by
  rw [← tendsto_safeAxisLogDefect_toReal_zero_iff_upperSpectralHeight_sublinear]
  exact
    tendsto_safeAxisLogDefect_toReal_zero_iff_height_mul_blaschkeVariation_zero.symm

end

end RiemannGaussian
