import RiemannGaussian.Hybrid.EtaSpectralHeatMoments
import RiemannGaussian.EtaEnergyFiniteWindowArithmeticCorrelation
import RiemannGaussian.HermitianRankTrace.Multiplicity

/-!
# Initial arithmetic data of the eta spectral heat hierarchy

The higher eta heat moments are useful only when they are connected back to
the literal arithmetic data.  This module makes the first such connection
without estimating or discarding any term.

For an arbitrary finite Hermitian matrix `A`, the zero-scale hierarchy
recovers the ordinary powers of `A`.  Consequently its first three scalar
moments are exactly the ambient dimension, the real trace of `A`, and the
squared Frobenius mass of `A`.  The latter is also the negative initial
derivative of the ordinary heat trace.

Lean then instantiates these facts on the multiplicity-weighted eta
zero-window matrix.  Its order-one initial moment is the already checked
on-line plus signed off-line trace mass.  Its order-two initial moment, and
therefore the initial heat-trace slope, is exactly the fully evaluated
odd--even endpoint correlation, retaining its positive diagonal and signed
distinct-zero off-diagonal terms.

This evaluates the first nontrivial boundary data of the new hierarchy.  It
does not evaluate positive heat times and does not improve a zero proportion.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Zero-scale Hermitian heat moments -/

/-- At zero heat scale, every positive-order spectral heat moment is the
corresponding ordinary matrix power. -/
theorem hermitianHeatMomentFlow_zeroScale_succ {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) :
    hermitianHeatMomentFlow hA (order + 1) 0 = A ^ (order + 1) := by
  unfold hermitianHeatMomentFlow
  simpa using Multiplicity.specMap_pow_succ hA order

/-- At zero heat scale, every positive-order heat trace is the real trace of
the corresponding matrix power. -/
theorem hermitianHeatMomentTrace_zeroScale_succ {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) :
    hermitianHeatMomentTrace hA (order + 1) 0 =
      rtrace (A ^ (order + 1)) := by
  unfold hermitianHeatMomentTrace
  rw [hermitianHeatMomentFlow_zeroScale_succ]

/-- The order-zero, zero-scale heat trace is the ambient dimension. -/
theorem hermitianHeatMomentTrace_zero_zero {A : Matrix n n K}
    (hA : A.IsHermitian) :
    hermitianHeatMomentTrace hA 0 0 = (Fintype.card n : ℝ) := by
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues]
  simp

/-- The order-one, zero-scale moment flow is the original Hermitian matrix. -/
theorem hermitianHeatMomentFlow_one_zero {A : Matrix n n K}
    (hA : A.IsHermitian) :
    hermitianHeatMomentFlow hA 1 0 = A := by
  simpa using hermitianHeatMomentFlow_zeroScale_succ hA 0

/-- The order-two, zero-scale moment flow is the square of the original
Hermitian matrix. -/
theorem hermitianHeatMomentFlow_two_zero {A : Matrix n n K}
    (hA : A.IsHermitian) :
    hermitianHeatMomentFlow hA 2 0 = A ^ 2 := by
  simpa using hermitianHeatMomentFlow_zeroScale_succ hA 1

/-- The order-one, zero-scale moment trace is the real trace of the original
matrix. -/
theorem hermitianHeatMomentTrace_one_zero {A : Matrix n n K}
    (hA : A.IsHermitian) :
    hermitianHeatMomentTrace hA 1 0 = rtrace A := by
  simpa using hermitianHeatMomentTrace_zeroScale_succ hA 0

/-- The order-two, zero-scale moment trace is exactly the squared Frobenius
mass of the original Hermitian matrix. -/
theorem hermitianHeatMomentTrace_two_zero_eq_frobSq {A : Matrix n n K}
    (hA : A.IsHermitian) :
    hermitianHeatMomentTrace hA 2 0 = frobSq A := by
  calc
    hermitianHeatMomentTrace hA 2 0 = rtrace (A ^ 2) := by
      simpa using hermitianHeatMomentTrace_zeroScale_succ hA 1
    _ = frobSq A := by
      unfold rtrace frobSq
      rw [hA.eq, pow_two]

/-- The initial derivative of the ordinary Hermitian heat trace is the
negative squared Frobenius mass. -/
theorem hasDerivAt_hermitianHeatMomentTrace_zero_at_zero {A : Matrix n n K}
    (hA : A.IsHermitian) :
    HasDerivAt (hermitianHeatMomentTrace hA 0) (-frobSq A) 0 := by
  have h := hasDerivAt_hermitianHeatMomentTrace hA 0 0
  simpa only [zero_add, hermitianHeatMomentTrace_two_zero_eq_frobSq] using h

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## Literal eta initial moments -/

/-- The initial eta order-zero heat trace is the dimension of its packed
cutoff/colour coordinate space. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_zero_zero
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 0 0 = (Fintype.card (d × Fin 2) : ℝ) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
  exact HermitianRankTrace.hermitianHeatMomentTrace_zero_zero _

/-- The initial eta order-one moment is the real trace of the literal
zero-window matrix. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_one_zero_eq_rtrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 1 0 =
      HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
  rw [HermitianRankTrace.hermitianHeatMomentTrace_one_zero]
  rfl

/-- The initial eta order-one moment retains the exact on-line plus signed
off-line trace decomposition. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_one_zero_eq_traceMasses
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 1 0 =
      pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_one_zero_eq_rtrace,
    pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT,
    HermitianInertia.rtrace_add,
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq_mass,
    pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq_mass]

/-- The initial eta order-two moment is the squared Frobenius mass of the
literal zero-window matrix. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_frobSq
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 2 0 =
      HermitianInertia.frobSq
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
  rw [HermitianRankTrace.hermitianHeatMomentTrace_two_zero_eq_frobSq]
  rfl

/-- The initial eta order-two moment is the coherent multiplicity-weighted
spectral Frobenius mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_coherentMass
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 2 0 =
      pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_frobSq,
    pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq_coherentMass]

/-- The initial eta order-two moment is exactly the fully evaluated endpoint
diagonal plus signed distinct-zero endpoint correlation. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_arithmetic
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT 2 0 =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_coherentMass,
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_arithmeticDiagonal_add_offDiagonal]

/-- The initial derivative of the ordinary eta heat trace is the negative of
the exact endpoint diagonal-plus-off-diagonal arithmetic correlation. -/
theorem hasDerivAt_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatTrace_at_zero_arithmetic
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace cutoff hT 0)
      (-(pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
            cutoff T +
          pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
            cutoff T)) 0 := by
  have h :=
    hasDerivAt_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
      cutoff hT 0 0
  simpa only [zero_add,
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_arithmetic]
    using h

/-- Any eta moment-Gram entry whose combined order is two and combined scale
is zero is the exact endpoint arithmetic correlation. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_apply_eq_arithmetic_of_add
    {d r : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : r → ℕ) (scale : r → ℝ) (i j : r)
    (horder : order i + order j = 2)
    (hscale : scale i + scale j = 0) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
        cutoff hT order scale i j =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff T := by
  rw [pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_apply,
    horder, hscale,
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_two_zero_eq_arithmetic]

/-- In particular, every entry of the order-one, zero-scale eta moment Gram
is the exact endpoint arithmetic correlation. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_one_zero_apply_eq_arithmetic
    {d r : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (i j : r) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
        cutoff hT (fun _ : r ↦ 1) (fun _ : r ↦ 0) i j =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff T := by
  apply
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_apply_eq_arithmetic_of_add
  · simp
  · simp

end

end RiemannGaussian
