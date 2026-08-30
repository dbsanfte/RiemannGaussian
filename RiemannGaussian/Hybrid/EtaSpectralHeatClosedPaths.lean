import RiemannGaussian.Hybrid.EtaSpectralHeatPowerSeries

/-!
# Closed eta paths behind the positive-time spectral heat

The matrix-power expansion of eta heat retains more information when each
coefficient is left as an ordered path sum instead of being compressed to a
single scalar trace.  This module constructs that carrier.

For an arbitrary finite square matrix, `matrixPowerPathSum A k i j` recursively
sums all length-`k` directed paths from `i` to `j`, preserving every ordered
intermediate coordinate and edge factor.  Its diagonal sum is proved exactly
equal to `trace (A^k)`.  The eta specialization then opens each matrix edge as
the literal multiplicity-weighted zero-window sum of two completed finite eta
features.  Consequently every positive-time eta heat moment is a genuinely
convergent series of real parts of closed, ordered eta path correlations.

No absolute value or termwise norm is introduced.  Cutoff coordinate, channel
colour, zero multiplicity, complex phase, path order, and heat-series order all
remain present.  The length-two coefficient is checked against the existing
endpoint arithmetic correlation.  Higher closed paths are represented exactly
but are not yet estimated, and no heat crossing or zeta-zero proportion is
claimed.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {R : Type*} [Semiring R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Generic ordered matrix paths -/

/-- The sum of the weights of all ordered length-`k` matrix paths from `i` to
`j`.  The successor step retains the penultimate coordinate explicitly. -/
def matrixPowerPathSum (A : Matrix n n R) : ℕ → n → n → R
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑ a, matrixPowerPathSum A k i a * A a j

/-- The ordered path sum is exactly the corresponding matrix-power entry. -/
theorem matrixPowerPathSum_eq_pow_apply (A : Matrix n n R)
    (k : ℕ) (i j : n) :
    matrixPowerPathSum A k i j = (A ^ k) i j := by
  induction k generalizing i j with
  | zero =>
      simp [matrixPowerPathSum, Matrix.one_apply]
  | succ k ih =>
      simp only [matrixPowerPathSum, pow_succ, Matrix.mul_apply, ih]

/-- The sum of all ordered length-`k` closed paths, with the base coordinate
retained until the outer finite sum. -/
def matrixClosedPathSum (A : Matrix n n R) (k : ℕ) : R :=
  ∑ i, matrixPowerPathSum A k i i

/-- A successor closed-path sum exposes both its base and penultimate
coordinates before any summation is collapsed. -/
theorem matrixClosedPathSum_succ (A : Matrix n n R) (k : ℕ) :
    matrixClosedPathSum A (k + 1) =
      ∑ i, ∑ a, matrixPowerPathSum A k i a * A a i := by
  rfl

/-- The complete ordered closed-path sum is exactly the trace of the
corresponding matrix power. -/
theorem matrixClosedPathSum_eq_trace_pow (A : Matrix n n R) (k : ℕ) :
    matrixClosedPathSum A k = Matrix.trace (A ^ k) := by
  simp only [matrixClosedPathSum, Matrix.trace, Matrix.diag,
    matrixPowerPathSum_eq_pow_apply]

end


noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real trace of a Hermitian matrix power is the real part of its full
ordered closed-path sum.  Hermiticity is not needed for this algebraic
identity. -/
theorem rtrace_pow_eq_re_matrixClosedPathSum (A : Matrix n n K) (k : ℕ) :
    rtrace (A ^ k) = RCLike.re (matrixClosedPathSum A k) := by
  unfold rtrace
  rw [matrixClosedPathSum_eq_trace_pow]

end


end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## Literal eta edges and closed paths -/

/-- One oriented coordinate edge of the eta zero-window matrix, left as the
literal multiplicity-weighted complex sum over genuine zeta zeros. -/
def pairedEtaTopPrefixFiniteZeroWindowEdge
    {d : Type*}
    (cutoff : d → ℕ) (T : ℝ) (i j : d × Fin 2) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) *
      pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho i *
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j

/-- Every matrix entry is exactly its literal eta zero-window edge sum. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_apply_eq_edge
    {d : Type*}
    (cutoff : d → ℕ) (T : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T i j =
      pairedEtaTopPrefixFiniteZeroWindowEdge cutoff T i j := by
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
    pairedEtaTopPrefixFiniteZeroWindowEdge
  simp only [Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro rho _hrho
  ring

/-- The full complex sum of ordered length-`k` closed paths through the eta
cutoff/colour coordinates, with every edge still a signed complex zero sum. -/
def pairedEtaTopPrefixFiniteZeroWindowClosedPathSum
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) (k : ℕ) : ℂ :=
  HermitianRankTrace.matrixClosedPathSum
    (fun i j ↦ pairedEtaTopPrefixFiniteZeroWindowEdge cutoff T i j) k

/-- Every real matrix-power trace of the eta block is exactly the real part
of the corresponding literal closed eta path sum. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_rtrace_pow_eq_re_closedPathSum
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) (T : ℝ) (k : ℕ) :
    HermitianRankTrace.rtrace
        ((pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) ^ k) =
      (pairedEtaTopPrefixFiniteZeroWindowClosedPathSum cutoff T k).re := by
  have hmatrix :
      (fun i j ↦ pairedEtaTopPrefixFiniteZeroWindowEdge cutoff T i j) =
        pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T := by
    ext i j
    exact
      (pairedEtaTopPrefixFiniteZeroWindowBlock_apply_eq_edge cutoff T i j).symm
  unfold HermitianRankTrace.rtrace
    pairedEtaTopPrefixFiniteZeroWindowClosedPathSum
  rw [hmatrix, HermitianRankTrace.matrixClosedPathSum_eq_trace_pow]
  rfl

/-! ## The complete heat series on closed eta paths -/

/-- Every eta order-`k` spectral heat moment is a convergent series of the
real parts of all parity-compatible ordered closed eta path sums. -/
theorem hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_closedPaths
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (order : ℕ) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        (pairedEtaTopPrefixFiniteZeroWindowClosedPathSum
          cutoff T (order + 2 * m)).re)
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT order u) := by
  simpa only [
    pairedEtaTopPrefixFiniteZeroWindow_rtrace_pow_eq_re_closedPathSum] using
    hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_rtrace_powers
      cutoff hT order u

/-- The ordinary eta heat trace is a convergent series of all even-length
ordered closed eta path correlations. -/
theorem hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_even_closedPaths
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        (pairedEtaTopPrefixFiniteZeroWindowClosedPathSum
          cutoff T (2 * m)).re)
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 0 u) := by
  simpa only [zero_add] using
    hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_closedPaths
      cutoff hT 0 u

/-- Tsum form of the ordinary eta heat trace as the complete even closed-path
series. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_eq_tsum_even_closedPaths
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace cutoff hT 0 u =
      ∑' m : ℕ, ((-u) ^ m / (m.factorial : ℝ)) *
        (pairedEtaTopPrefixFiniteZeroWindowClosedPathSum
          cutoff T (2 * m)).re :=
  (hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_even_closedPaths
    cutoff hT u).tsum_eq.symm

/-- The length-two closed eta path is exactly the already evaluated endpoint
diagonal plus signed distinct-zero arithmetic correlation. -/
theorem pairedEtaTopPrefixFiniteZeroWindowClosedPathSum_two_re_eq_arithmetic
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (pairedEtaTopPrefixFiniteZeroWindowClosedPathSum cutoff T 2).re =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff T := by
  rw [← pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_arithmetic
    cutoff hT]
  unfold pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
  rw [HermitianRankTrace.hermitianHeatMomentTrace_zeroScale_succ]
  simpa only [one_add_one_eq_two] using
    (pairedEtaTopPrefixFiniteZeroWindow_rtrace_pow_eq_re_closedPathSum
      cutoff T 2).symm

end


end RiemannGaussian
