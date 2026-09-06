import RiemannGaussian.EtaPolynomialHeatReflection
import RiemannGaussian.Hybrid.EtaCubicHeatGram

/-!
# Full mixed polynomial-phase heat matrices at second order

Every mixed entry belongs to the actual continuous support/gap phase
matrix. Its finite part and reflected limit retain both endpoint matrices
with their signs. For fixed finite families, the entrywise absolute error
converges to zero; its bound retains the square of the family size.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal NNReal Interval Topology BigOperators

namespace RiemannGaussian

noncomputable section

/-- The actual continuous phase matrix for a family of quadratic/cubic probes. -/
def pairedEtaSupportGapPolynomialPhaseGram {ι : Type*} (lambda h : ℝ)
    (kappa beta alpha : ι → ℝ) : Matrix ι ι ℝ :=
  pairedEtaSupportGapPhaseGram (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
    (fun i ↦ pairedEtaCriticalPolynomialPhase (kappa i) (beta i) (alpha i) h (Real.log (1 / h)))

/-- The complete leading mixed heat profile. -/
def pairedEtaPolynomialHeatProfileMatrix {ι : Type*} (lambda : ℝ)
    (kappa beta alpha : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaPolynomialHeatProfile lambda (kappa j - kappa i) (beta j - beta i) (alpha j - alpha i)

/-- The complete mixed second-order coefficient. -/
def pairedEtaPolynomialHeatFinitePartMatrix {ι : Type*} (lambda : ℝ)
    (kappa beta alpha : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaPolynomialHeatFinitePart lambda (kappa j - kappa i) (beta j - beta i) (alpha j - alpha i)

/-- The signed endpoint profile matrix of a family of endpoint velocities. -/
def pairedEtaSignedEndpointHeatMatrix {ι : Type*} (kappa : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaSignedEndpointHeatProfile (kappa j - kappa i)

/-- The signed endpoint cosine profile remains even in its phase. -/
theorem pairedEtaSignedEndpointHeatProfile_neg (kappa : ℝ) :
    pairedEtaSignedEndpointHeatProfile (-kappa) = pairedEtaSignedEndpointHeatProfile kappa := by
  simp only [pairedEtaSignedEndpointHeatProfile, pairedEtaHeatPhaseProfile_neg, pairedEtaLogHeatPhaseProfile_neg]

/-- Each full endpoint matrix is real symmetric, independently of its sign. -/
theorem pairedEtaSignedEndpointHeatMatrix_isHermitian {ι : Type*} (kappa : ι → ℝ) :
    (pairedEtaSignedEndpointHeatMatrix kappa).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [star_trivial, pairedEtaSignedEndpointHeatMatrix]
  rw [show kappa i - kappa j = -(kappa j - kappa i) by ring, pairedEtaSignedEndpointHeatProfile_neg]

/-- The actual signed combination of the two reflected continuous phase matrices. -/
def pairedEtaSignedPolynomialPhaseGram {ι : Type*} (lambda h : ℝ)
    (kappa beta alpha : ι → ℝ) : Matrix ι ι ℝ :=
  pairedEtaSupportGapPolynomialPhaseGram lambda h kappa beta alpha - Real.exp (-2 * lambda) •
    pairedEtaSupportGapPolynomialPhaseGram (-lambda) h
      (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha

/-- Differences of the actual polynomial phases remain in the same family. -/
theorem pairedEtaCriticalPolynomialPhase_sub (kappa kappa' beta beta' alpha alpha' h R : ℝ) :
    (fun t : ℝ ↦ pairedEtaCriticalPolynomialPhase kappa' beta' alpha' h R t -
      pairedEtaCriticalPolynomialPhase kappa beta alpha h R t) =
      pairedEtaCriticalPolynomialPhase (kappa' - kappa) (beta' - beta) (alpha' - alpha) h R := by
  funext t
  unfold pairedEtaCriticalPolynomialPhase
  ring

/-- Each mixed entry is exactly the actual heat at the corresponding phase differences. -/
theorem pairedEtaSupportGapPolynomialPhaseGram_apply {ι : Type*} (lambda h : ℝ)
    (kappa beta alpha : ι → ℝ) (i j : ι) :
    pairedEtaSupportGapPolynomialPhaseGram lambda h kappa beta alpha i j =
      pairedEtaSupportGapGaussianLeakage (pairedEtaMovingCriticalTilt lambda (Real.log (1 / h))) h
        (pairedEtaCriticalPolynomialPhase (kappa j - kappa i) (beta j - beta i) (alpha j - alpha i)
          h (Real.log (1 / h))) := by
  simp only [pairedEtaSupportGapPolynomialPhaseGram, pairedEtaSupportGapPhaseGram,
    pairedEtaCriticalPolynomialPhase_sub]

/-- The complete mixed matrix has its second-order limit in the product
topology. No off-diagonal phase channel is discarded. -/
theorem pairedEtaSupportGapPolynomialPhaseGram_finite_part_tendsto {ι : Type*}
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ h⁻¹ • pairedEtaSupportGapPolynomialPhaseGram lambda h kappa beta alpha -
      Real.log (1 / h) • pairedEtaPolynomialHeatProfileMatrix lambda kappa beta alpha) (𝓝[>] 0)
      (𝓝 (pairedEtaPolynomialHeatFinitePartMatrix lambda kappa beta alpha)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    pairedEtaSupportGapPolynomialPhaseGram_apply, pairedEtaPolynomialHeatProfileMatrix,
    pairedEtaPolynomialHeatFinitePartMatrix, div_eq_mul_inv, mul_comm] using
    pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_tendsto lambda
      (kappa j - kappa i) (beta j - beta i) (alpha j - alpha i)

/-- Exact reflection of the leading mixed matrix retains every phase difference. -/
theorem pairedEtaPolynomialHeatProfileMatrix_reflection {ι : Type*}
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    pairedEtaPolynomialHeatProfileMatrix lambda kappa beta alpha = Real.exp (-2 * lambda) •
      pairedEtaPolynomialHeatProfileMatrix (-lambda)
        (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, pairedEtaPolynomialHeatProfileMatrix]
  rw [pairedEtaPolynomialHeatProfile_reflection]
  congr 2 <;> ring

/-- The second-order mixed reflection coefficient is the signed difference
of the two full endpoint matrices. -/
theorem pairedEtaPolynomialHeatFinitePartMatrix_reflection {ι : Type*}
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    pairedEtaPolynomialHeatFinitePartMatrix lambda kappa beta alpha - Real.exp (-2 * lambda) •
      pairedEtaPolynomialHeatFinitePartMatrix (-lambda)
        (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha =
      pairedEtaSignedEndpointHeatMatrix kappa - Real.exp (-2 * lambda) •
        pairedEtaSignedEndpointHeatMatrix (fun i ↦ kappa i + beta i + 3 * alpha i) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    pairedEtaPolynomialHeatFinitePartMatrix, pairedEtaSignedEndpointHeatMatrix]
  have h0 : kappa j + beta j + 3 * alpha j - (kappa i + beta i + 3 * alpha i) =
      (kappa j - kappa i) + (beta j - beta i) + 3 * (alpha j - alpha i) := by ring
  have h1 : -beta j - 6 * alpha j - (-beta i - 6 * alpha i) =
      -(beta j - beta i) - 6 * (alpha j - alpha i) := by ring
  rw [h0, h1]
  exact pairedEtaPolynomialHeatFinitePart_reflection lambda (kappa j - kappa i) (beta j - beta i) (alpha j - alpha i)

/-- The actual signed matrix equals the difference of the two renormalized
matrices at every finite width, with exact leading cancellation. -/
theorem pairedEtaSignedPolynomialPhaseGram_eq_finite_part_difference {ι : Type*}
    (lambda h : ℝ) (kappa beta alpha : ι → ℝ) :
    h⁻¹ • pairedEtaSignedPolynomialPhaseGram lambda h kappa beta alpha =
      (h⁻¹ • pairedEtaSupportGapPolynomialPhaseGram lambda h kappa beta alpha -
        Real.log (1 / h) • pairedEtaPolynomialHeatProfileMatrix lambda kappa beta alpha) - Real.exp (-2 * lambda) •
      (h⁻¹ • pairedEtaSupportGapPolynomialPhaseGram (-lambda) h
        (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha -
        Real.log (1 / h) • pairedEtaPolynomialHeatProfileMatrix (-lambda)
          (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha) := by
  rw [pairedEtaPolynomialHeatProfileMatrix_reflection lambda kappa beta alpha]
  ext i j
  simp only [pairedEtaSignedPolynomialPhaseGram, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The full actual mixed matrix has the signed endpoint limit. This
statement asserts convergence, without inferring positivity of the difference. -/
theorem pairedEtaSignedPolynomialPhaseGram_tendsto {ι : Type*}
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ h⁻¹ • pairedEtaSignedPolynomialPhaseGram lambda h kappa beta alpha) (𝓝[>] 0)
      (𝓝 (pairedEtaSignedEndpointHeatMatrix kappa - Real.exp (-2 * lambda) •
        pairedEtaSignedEndpointHeatMatrix (fun i ↦ kappa i + beta i + 3 * alpha i))) := by
  have h := (pairedEtaSupportGapPolynomialPhaseGram_finite_part_tendsto lambda kappa beta alpha).sub
    ((pairedEtaSupportGapPolynomialPhaseGram_finite_part_tendsto (-lambda)
      (fun i ↦ kappa i + beta i + 3 * alpha i) (fun i ↦ -beta i - 6 * alpha i) alpha).const_smul (Real.exp (-2 * lambda)))
  rw [pairedEtaPolynomialHeatFinitePartMatrix_reflection] at h
  simpa only [pairedEtaSignedPolynomialPhaseGram_eq_finite_part_difference] using h

/-- The complete signed matrix error, retaining both endpoint matrices. -/
def pairedEtaSignedPolynomialPhaseGramError {ι : Type*} (lambda h : ℝ)
    (kappa beta alpha : ι → ℝ) : Matrix ι ι ℝ :=
  h⁻¹ • pairedEtaSignedPolynomialPhaseGram lambda h kappa beta alpha -
    (pairedEtaSignedEndpointHeatMatrix kappa - Real.exp (-2 * lambda) •
      pairedEtaSignedEndpointHeatMatrix (fun i ↦ kappa i + beta i + 3 * alpha i))

/-- Every mixed error entry tends to zero in the original positive heat width. -/
theorem pairedEtaSignedPolynomialPhaseGramError_tendsto {ι : Type*}
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha) (𝓝[>] 0) (𝓝 0) := by
  simpa only [pairedEtaSignedPolynomialPhaseGramError, sub_self] using
    (pairedEtaSignedPolynomialPhaseGram_tendsto lambda kappa beta alpha).sub_const
      (pairedEtaSignedEndpointHeatMatrix kappa - Real.exp (-2 * lambda) •
        pairedEtaSignedEndpointHeatMatrix (fun i ↦ kappa i + beta i + 3 * alpha i))

/-- For a fixed finite family, the sum of absolute errors over all entries
vanishes. This retains the complete matrix rather than only its trace. -/
theorem pairedEtaSignedPolynomialPhaseGramError_sum_abs_tendsto {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) :
    Tendsto (fun h : ℝ ↦ ∑ i, ∑ j, |pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha i j|)
      (𝓝[>] 0) (𝓝 0) := by
  have he := pairedEtaSignedPolynomialPhaseGramError_tendsto lambda kappa beta alpha
  have hij (i j : ι) : Tendsto (fun h : ℝ ↦ |pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha i j|)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Matrix.zero_apply, abs_zero] using ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he i)) j).abs
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun i _ ↦ tendsto_finsetSum Finset.univ (fun j _ ↦ hij i j))

/-- A simultaneous entry bound for the actual signed error costs the square
of the family size when passing to its total entrywise absolute error. -/
theorem pairedEtaSignedPolynomialPhaseGramError_sum_abs_eventually_le {ι : Type*} [Fintype ι]
    (lambda : ℝ) (kappa beta alpha : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∑ i, ∑ j, |pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha i j|) ≤
        (Fintype.card ι : ℝ) ^ 2 * epsilon := by
  have he := pairedEtaSignedPolynomialPhaseGramError_tendsto lambda kappa beta alpha
  have hij (i j : ι) : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      |pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha i j| ≤ epsilon := by
    have ht := ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he i)) j).abs
    have hlt := ht.eventually (Iio_mem_nhds (by simpa only [Matrix.zero_apply, abs_zero] using hepsilon))
    exact hlt.mono fun h hh ↦ hh.le
  have hall : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ i j,
      |pairedEtaSignedPolynomialPhaseGramError lambda h kappa beta alpha i j| ≤ epsilon :=
    eventually_all.mpr fun i ↦ eventually_all.mpr fun j ↦ hij i j
  filter_upwards [hall] with h hh
  calc
    _ ≤ ∑ _i : ι, ∑ _j : ι, epsilon :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hh i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end

end RiemannGaussian
