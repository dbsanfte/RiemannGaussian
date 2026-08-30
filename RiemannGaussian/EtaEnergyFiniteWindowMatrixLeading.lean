import RiemannGaussian.EtaEnergyFiniteWindowMatrixWork
import RiemannGaussian.EtaEnergyFiniteWindowRank

/-!
# Leading and remainder currents in the finite eta matrix work

The scalar eta transport theory already separates every exact arithmetic
increment into its unique degree-one leading term and a faster remainder.
This module transports that separation through the full packed zero-window
matrix rather than first taking a trace or norm.

For each genuine nontrivial zero, the exact matrix work is split into a
leading current and a remainder current.  Both factor as sums of two outer
products and therefore have rank at most two, including analytic
multiplicity.  Summing over the finite spectral window gives an exact
matrix-valued leading-plus-remainder law and corresponding divisor-count rank
bounds.  Every statement concerns the existing complex-symmetric transpose
blocks; no Hermitian compression is assumed.
-/

open Complex
open scoped Classical ComplexConjugate Matrix

namespace RiemannGaussian

noncomputable section

/-! ## Packed leading and remainder increments -/

/-- Pack the leading hyperbolic arithmetic increment over a finite family of
cutoffs. -/
def pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    d × Fin 2 → ℂ :=
  fun j ↦
    pairedEtaTopPrefixFiniteHyperbolicLeadingArithmeticIncrement
      rho (cutoff j.1) j.2

/-- Pack the remainder hyperbolic arithmetic increment over a finite family
of cutoffs. -/
def pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    d × Fin 2 → ℂ :=
  fun j ↦
    pairedEtaTopPrefixFiniteHyperbolicRemainderArithmeticIncrement
      rho (cutoff j.1) j.2

/-- The packed arithmetic increment is exactly the sum of its packed leading
and remainder parts. -/
theorem topPrefixFiniteCutoffFamilyArithmeticIncrement_eq_leading_add_remainder
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyArithmeticIncrement cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho +
        pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho := by
  funext j
  exact congrFun
    (topPrefixFiniteHyperbolicArithmeticIncrement_eq_leading_add_remainder
      rho (cutoff j.1)) j.2

/-- The literal packed feature difference is exactly its leading arithmetic
increment plus its arithmetic remainder. -/
theorem topPrefixFiniteCutoffFamilyIncrement_eq_leading_add_remainder
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyIncrement cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho +
        pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho := by
  rw [topPrefixFiniteCutoffFamilyIncrement_eq_arithmeticIncrement,
    topPrefixFiniteCutoffFamilyArithmeticIncrement_eq_leading_add_remainder]

/-! ## Generic low-rank transport algebra -/

/-- The part of transpose-polarized matrix work containing only the leading
increment and the successor feature. -/
def complexSymmetricLeadingTransportCurrent
    {d : Type*} (leading successor : d → ℂ) : Matrix d d ℂ :=
  Matrix.vecMulVec leading leading +
    (Matrix.vecMulVec leading successor +
      Matrix.vecMulVec successor leading)

/-- The part of transpose-polarized matrix work containing at least one
remainder increment. -/
def complexSymmetricRemainderTransportCurrent
    {d : Type*} (leading remainder successor : d → ℂ) : Matrix d d ℂ :=
  Matrix.vecMulVec remainder remainder +
    (Matrix.vecMulVec leading remainder +
      Matrix.vecMulVec remainder leading) +
    (Matrix.vecMulVec remainder successor +
      Matrix.vecMulVec successor remainder)

/-- Substituting `increment = leading + remainder` into transpose
polarization gives the exact leading-plus-remainder current decomposition. -/
theorem complexSymmetricTransportCurrent_eq_leading_add_remainder
    {d : Type*} (leading remainder successor : d → ℂ) :
    Matrix.vecMulVec (leading + remainder) (leading + remainder) +
        (Matrix.vecMulVec (leading + remainder) successor +
          Matrix.vecMulVec successor (leading + remainder)) =
      complexSymmetricLeadingTransportCurrent leading successor +
        complexSymmetricRemainderTransportCurrent
          leading remainder successor := by
  ext i j
  simp only [complexSymmetricLeadingTransportCurrent,
    complexSymmetricRemainderTransportCurrent, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.add_apply]
  ring

/-- The leading current is a sum of two literal outer products. -/
theorem complexSymmetricLeadingTransportCurrent_eq_two_outerProducts
    {d : Type*} (leading successor : d → ℂ) :
    complexSymmetricLeadingTransportCurrent leading successor =
      Matrix.vecMulVec leading (leading + successor) +
        Matrix.vecMulVec successor leading := by
  ext i j
  simp only [complexSymmetricLeadingTransportCurrent, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.add_apply]
  ring

/-- The remainder current is likewise a sum of two literal outer products. -/
theorem complexSymmetricRemainderTransportCurrent_eq_two_outerProducts
    {d : Type*} (leading remainder successor : d → ℂ) :
    complexSymmetricRemainderTransportCurrent leading remainder successor =
      Matrix.vecMulVec remainder (remainder + leading + successor) +
        Matrix.vecMulVec (leading + successor) remainder := by
  ext i j
  simp only [complexSymmetricRemainderTransportCurrent, Matrix.add_apply,
    Matrix.vecMulVec_apply, Pi.add_apply]
  ring

/-- Every leading transport current has rank at most two. -/
theorem complexSymmetricLeadingTransportCurrent_rank_le_two
    {d : Type*} [Fintype d] (leading successor : d → ℂ) :
    (complexSymmetricLeadingTransportCurrent leading successor).rank ≤ 2 := by
  rw [complexSymmetricLeadingTransportCurrent_eq_two_outerProducts]
  calc
    (Matrix.vecMulVec leading (leading + successor) +
        Matrix.vecMulVec successor leading).rank ≤
      (Matrix.vecMulVec leading (leading + successor)).rank +
        (Matrix.vecMulVec successor leading).rank := matrixRank_add_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _)
    _ = 2 := rfl

/-- Every remainder transport current has rank at most two. -/
theorem complexSymmetricRemainderTransportCurrent_rank_le_two
    {d : Type*} [Fintype d]
    (leading remainder successor : d → ℂ) :
    (complexSymmetricRemainderTransportCurrent
      leading remainder successor).rank ≤ 2 := by
  rw [complexSymmetricRemainderTransportCurrent_eq_two_outerProducts]
  calc
    (Matrix.vecMulVec remainder (remainder + leading + successor) +
        Matrix.vecMulVec (leading + successor) remainder).rank ≤
      (Matrix.vecMulVec remainder (remainder + leading + successor)).rank +
        (Matrix.vecMulVec (leading + successor) remainder).rank :=
      matrixRank_add_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _)
    _ = 2 := rfl

/-! ## Eta matrix currents on genuine zero windows -/

/-- Multiplicity-weighted leading matrix current contributed by one genuine
nontrivial zero. -/
def pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) •
    complexSymmetricLeadingTransportCurrent
      (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature
        (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho)

/-- Multiplicity-weighted remainder matrix current contributed by one genuine
nontrivial zero. -/
def pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) •
    complexSymmetricRemainderTransportCurrent
      (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho)
      (pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho)
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature
        (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho)

/-- Analytic multiplicity does not raise the rank-two bound for one zero's
leading current. -/
theorem pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent_rank_le_two
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent cutoff rho).rank ≤ 2 := by
  unfold pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
  rw [complexSymmetricLeadingTransportCurrent_eq_two_outerProducts, smul_add]
  calc
    ((analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho +
              pairedEtaTopPrefixFiniteCutoffFamilyFeature
                (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho) +
        (analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature
              (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho)).rank ≤
      1 + 1 := (matrixRank_add_le _ _).trans
        (Nat.add_le_add
          (matrixRank_smul_vecMulVec_le _ _ _)
          (matrixRank_smul_vecMulVec_le _ _ _))
    _ = 2 := rfl

/-- Analytic multiplicity does not raise the rank-two bound for one zero's
remainder current. -/
theorem pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent_rank_le_two
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    (pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent cutoff rho).rank ≤ 2 := by
  unfold pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent
  rw [complexSymmetricRemainderTransportCurrent_eq_two_outerProducts, smul_add]
  calc
    ((analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho +
                pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho +
              pairedEtaTopPrefixFiniteCutoffFamilyFeature
                (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho) +
        (analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement cutoff rho +
              pairedEtaTopPrefixFiniteCutoffFamilyFeature
                (pairedEtaTopPrefixFiniteSuccessorCutoff cutoff) rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyRemainderArithmeticIncrement cutoff rho)).rank ≤
      1 + 1 := (matrixRank_add_le _ _).trans
        (Nat.add_le_add
          (matrixRank_smul_vecMulVec_le _ _ _)
          (matrixRank_smul_vecMulVec_le _ _ _))
    _ = 2 := rfl

/-- Sum of the leading currents over a genuine finite spectral zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent cutoff rho

/-- Sum of the remainder currents over a genuine finite spectral zero
window. -/
def pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent cutoff rho

/-- Exact matrix-current decomposition of the finite eta zero-window work. -/
theorem topPrefixFiniteZeroWindowMatrixWork_eq_leading_add_remainder
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowMatrixWork
    pairedEtaTopPrefixFiniteZeroWindowBlock
    pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  unfold pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent
  rw [← smul_sub, ← smul_add]
  apply congrArg ((analyticZetaZeroMultiplicity rho : ℂ) • ·)
  rw [vecMulVec_sub_vecMulVec_eq_increment_add_flux]
  have hincrement :=
    topPrefixFiniteCutoffFamilyIncrement_eq_leading_add_remainder cutoff rho
  unfold pairedEtaTopPrefixFiniteCutoffFamilyIncrement at hincrement
  rw [hincrement]
  exact complexSymmetricTransportCurrent_eq_leading_add_remainder _ _ _

/-- The leading zero-window current has rank at most twice the number of
distinct zeros represented in the window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent_rank_le_two_mul_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T).rank ≤
      2 * (spectralZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 2) ?_).trans ?_
  · intro rho _hrho
    exact pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent_rank_le_two cutoff rho
  · simp [Nat.mul_comm]

/-- The remainder zero-window current also has rank at most twice the number
of distinct zeros represented in the window. -/
theorem pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent_rank_le_two_mul_card
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent cutoff T).rank ≤
      2 * (spectralZetaZeroWindow T).card := by
  unfold pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 2) ?_).trans ?_
  · intro rho _hrho
    exact pairedEtaTopPrefixFiniteZeroRemainderMatrixCurrent_rank_le_two cutoff rho
  · simp [Nat.mul_comm]

/-- Combined terminal form of the low-rank matrix-current decomposition: the
work is exactly leading plus remainder, and each complete window current has
rank at most twice the number of represented zeros. -/
theorem topPrefixFiniteZeroWindowMatrixWork_lowRank_decomposition
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowMatrixWork cutoff T =
          pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T +
            pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent cutoff T ∧
      (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T).rank ≤
          2 * (spectralZetaZeroWindow T).card ∧
        (pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent cutoff T).rank ≤
          2 * (spectralZetaZeroWindow T).card := by
  exact ⟨topPrefixFiniteZeroWindowMatrixWork_eq_leading_add_remainder cutoff T,
    pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent_rank_le_two_mul_card
      cutoff T,
    pairedEtaTopPrefixFiniteZeroWindowRemainderMatrixCurrent_rank_le_two_mul_card
      cutoff T⟩

end

end RiemannGaussian
