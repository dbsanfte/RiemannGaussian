import RiemannGaussian.EtaEnergyFiniteWindowHeatHilbert

/-!
# Hilbert bounds for the actual eta leading matrix current

The preceding heat/Hilbert module proves the Montgomery--Vaughan inequality
for arbitrary vectors at the centered eta cutoff nodes `log(2N+1)`.  This
module applies that theorem to the literal rank-two factorization of the eta
leading matrix current.

The current uses complex-symmetric transpose outer products rather than
Hermitian outer products.  Lean therefore first rewrites each direct odd-heat
transpose form as the existing sesquilinear odd-heat form by conjugating its
second vector.  For each genuine nontrivial zero and each of the four
hyperbolic channel blocks, the heat/Hilbert transform is then exactly a sum of
two such forms, including analytic multiplicity.  The checked constant-26
inequality supplies an explicit norm envelope.

Finally, the full finite spectral-window block is proved to be the exact
signed sum of the per-zero forms before any triangle inequality is used.  Its
skew symmetry is retained explicitly: same-colour block sums vanish, while
the two mixed-colour blocks are negatives.  A coarse sum-of-envelopes bound is
also recorded.  That bound does not provide the cross-zero cancellation
required for RH; the exact signed zero sum is retained as the object on which
the next arithmetic estimate must act.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate Matrix Real

namespace RiemannGaussian

noncomputable section

/-! ## Transpose heat forms -/

/-- Bilinear, rather than sesquilinear, direct odd-heat form.  This is the
scalar sum produced by a complex-symmetric transpose outer product. -/
def finiteGaussianOddHeatTransposeBilinear
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x y : d → ℂ) : ℂ :=
  ∑ i, ∑ j,
    x i * y j * finiteGaussianOddHeatKernelIntegral frequency i j

/-- A direct odd-heat transpose form is the sesquilinear odd-heat form with
the second vector conjugated. -/
theorem finiteGaussianOddHeatTransposeBilinear_eq_sesquilinear
    {d : Type*} [Fintype d] (frequency : d → ℝ)
    (x y : d → ℂ) :
    finiteGaussianOddHeatTransposeBilinear frequency x y =
      finiteGaussianOddHeatBilinear frequency x
        (fun j ↦ conj (y j)) := by
  unfold finiteGaussianOddHeatTransposeBilinear
    finiteGaussianOddHeatBilinear
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp

/-- Constant-26 Montgomery--Vaughan bound for transpose heat forms at the
first `K` centered eta cutoff nodes. -/
theorem pairedEtaFiniteCutoffLog_oddHeatTranspose_mvHilbert_twentySix
    {K : ℕ} (hK : 0 < K) (x y : Fin K → ℂ) :
    ‖finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val) x y‖ ≤
      26 * Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2) *
        Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖y r‖ ^ 2) := by
  rw [finiteGaussianOddHeatTransposeBilinear_eq_sesquilinear]
  have hbound :=
    pairedEtaFiniteCutoffLog_oddHeat_mvHilbert_twentySix
      hK x (fun r ↦ conj (y r))
  simpa using hbound

/-! ## Channel blocks and transform linearity -/

/-- Sum of one fixed hyperbolic channel block of a matrix indexed by
`Fin K × Fin 2`. -/
def twoChannelMatrixBlockSum {K : ℕ}
    (M : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (a b : Fin 2) : ℂ :=
  ∑ r, ∑ s, M (r, a) (s, b)

/-- Restrict a two-channel vector to one fixed hyperbolic channel. -/
def twoChannelVectorSlice {K : ℕ}
    (v : Fin K × Fin 2 → ℂ) (a : Fin 2) : Fin K → ℂ :=
  fun r ↦ v (r, a)

/-- A channel block of the direct odd-heat transform of a transpose outer
product is exactly the odd-heat transpose form of the corresponding channel
slices. -/
theorem twoChannelMatrixBlockSum_oddHeatTransform_vecMulVec
    {K : ℕ} (frequency : Fin K → ℝ)
    (x y : Fin K × Fin 2 → ℂ) (a b : Fin 2) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatTransform
          (fun j : Fin K × Fin 2 ↦ frequency j.1)
          (Matrix.vecMulVec x y)) a b =
      finiteGaussianOddHeatTransposeBilinear frequency
        (twoChannelVectorSlice x a) (twoChannelVectorSlice y b) := by
  unfold twoChannelMatrixBlockSum
    finiteGaussianOddHeatTransposeBilinear
    twoChannelVectorSlice
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro s _hs
  rw [finiteGaussianOddHeatTransform_apply,
    finiteGaussianOddHeatKernelIntegral_eq]
  simp only [Matrix.vecMulVec_apply]
  by_cases hfreq : frequency r = frequency s
  · simp [hfreq]
  · simp [hfreq]
    ring

/-- Specialization of the outer-product block identity to the literal eta
cutoff heat nodes. -/
theorem twoChannelMatrixBlockSum_etaOddHeatTransform_vecMulVec
    {K : ℕ} (x y : Fin K × Fin 2 → ℂ) (a b : Fin 2) :
    twoChannelMatrixBlockSum
        (finiteGaussianOddHeatTransform
          (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
            (fun r : Fin K ↦ r.val))
          (Matrix.vecMulVec x y)) a b =
      finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (twoChannelVectorSlice x a) (twoChannelVectorSlice y b) := by
  have hnode :
      pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
          (fun r : Fin K ↦ r.val) =
        (fun j : Fin K × Fin 2 ↦
          pairedEtaCutoffLogFrequency j.1.val) := rfl
  rw [hnode]
  exact twoChannelMatrixBlockSum_oddHeatTransform_vecMulVec
    (K := K)
    (frequency := fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
    x y a b

/-- The direct odd-heat transform commutes with complex scalar
multiplication. -/
theorem finiteGaussianOddHeatTransform_smul
    {d : Type*} (frequency : d → ℝ) (c : ℂ) (A : Matrix d d ℂ) :
    finiteGaussianOddHeatTransform frequency (c • A) =
      c • finiteGaussianOddHeatTransform frequency A := by
  ext i j
  simp only [finiteGaussianOddHeatTransform_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · simp [hfreq]
    ring

/-- The direct odd-heat transform commutes with every finite matrix
sum. -/
theorem finiteGaussianOddHeatTransform_finsetSum
    {d alpha : Type*} (frequency : d → ℝ) (S : Finset alpha)
    (A : alpha → Matrix d d ℂ) :
    finiteGaussianOddHeatTransform frequency (∑ q ∈ S, A q) =
      ∑ q ∈ S, finiteGaussianOddHeatTransform frequency (A q) := by
  ext i j
  simp only [finiteGaussianOddHeatTransform_apply,
    Matrix.sum_apply]
  by_cases hfreq : frequency i = frequency j
  · simp [hfreq]
  · simp [hfreq, Finset.mul_sum]

/-- Channel block summation is additive. -/
theorem twoChannelMatrixBlockSum_add {K : ℕ}
    (M N : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (a b : Fin 2) :
    twoChannelMatrixBlockSum (M + N) a b =
      twoChannelMatrixBlockSum M a b + twoChannelMatrixBlockSum N a b := by
  unfold twoChannelMatrixBlockSum
  simp only [Matrix.add_apply, Finset.sum_add_distrib]

/-- Channel block summation commutes with complex scalar multiplication. -/
theorem twoChannelMatrixBlockSum_smul {K : ℕ} (c : ℂ)
    (M : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (a b : Fin 2) :
    twoChannelMatrixBlockSum (c • M) a b =
      c * twoChannelMatrixBlockSum M a b := by
  unfold twoChannelMatrixBlockSum
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Channel block summation commutes with every finite matrix sum. -/
theorem twoChannelMatrixBlockSum_finsetSum
    {K : ℕ} {alpha : Type*} (S : Finset alpha)
    (M : alpha → Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (a b : Fin 2) :
    twoChannelMatrixBlockSum (∑ q ∈ S, M q) a b =
      ∑ q ∈ S, twoChannelMatrixBlockSum (M q) a b := by
  unfold twoChannelMatrixBlockSum
  simp only [Matrix.sum_apply]
  calc
    (∑ r, ∑ s, ∑ q ∈ S, M q (r, a) (s, b)) =
        ∑ r, ∑ q ∈ S, ∑ s, M q (r, a) (s, b) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.sum_comm]
    _ = ∑ q ∈ S, ∑ r, ∑ s, M q (r, a) (s, b) := by
      rw [Finset.sum_comm]

/-- Swapping the two channel colours negates the block sum of a
skew-symmetric matrix. -/
theorem twoChannelMatrixBlockSum_swap_of_transpose_eq_neg
    {K : ℕ} (M : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (hM : Mᵀ = -M) (a b : Fin 2) :
    twoChannelMatrixBlockSum M b a =
      -twoChannelMatrixBlockSum M a b := by
  unfold twoChannelMatrixBlockSum
  calc
    (∑ r, ∑ s, M (r, b) (s, a)) =
        ∑ s, ∑ r, M (r, b) (s, a) := by
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ r, -M (s, a) (r, b) := by
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro r _hr
      have hij := congrFun (congrFun hM (s, a)) (r, b)
      simpa using hij
    _ = -∑ s, ∑ r, M (s, a) (r, b) := by
      simp

/-- Every same-colour block sum of a skew-symmetric two-channel matrix
vanishes. -/
theorem twoChannelMatrixBlockSum_self_eq_zero_of_transpose_eq_neg
    {K : ℕ} (M : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (hM : Mᵀ = -M) (a : Fin 2) :
    twoChannelMatrixBlockSum M a a = 0 := by
  have h := twoChannelMatrixBlockSum_swap_of_transpose_eq_neg M hM a a
  linear_combination (1 / 2 : ℂ) * h

/-! ## Symmetry of the untransformed leading current -/

/-- The literal leading transport current is complex symmetric before the
odd heat kernel is applied. -/
theorem complexSymmetricLeadingTransportCurrent_isSymm
    {d : Type*} (leading successor : d → ℂ) :
    (complexSymmetricLeadingTransportCurrent leading successor).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [complexSymmetricLeadingTransportCurrent, Matrix.add_apply,
    Matrix.vecMulVec_apply]
  ring

/-- Analytic multiplicity preserves the complex symmetry of one zero's
literal leading matrix current. -/
theorem pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent_isSymm
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent cutoff rho).IsSymm := by
  unfold pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
  exact (complexSymmetricLeadingTransportCurrent_isSymm _ _).smul _

/-- The genuine multiplicity-weighted finite zero-window leading current is
complex symmetric. -/
theorem pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent_isSymm
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent cutoff T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro rho _hrho
  exact
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent_isSymm
      cutoff rho).apply i j

/-! ## One zero's literal leading current -/

/-- Direct odd heat/Hilbert transform of the leading matrix current
contributed by one genuine nontrivial zero on the canonical cutoff prefix. -/
def pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
    (K : ℕ) (rho : NontrivialZetaZero) :
    Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOddHeatTransform
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val))
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
      (fun r : Fin K ↦ r.val) rho)

/-- One zero's direct odd heat/Hilbert leading matrix is skew-symmetric. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent_transpose_eq_neg
    (K : ℕ) (rho : NontrivialZetaZero) :
    (pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent K rho)ᵀ =
      -pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent K rho := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
  exact finiteGaussianOddHeatTransform_transpose_of_isSymm _ _
    (pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent_isSymm _ rho)

/-- One fixed channel block of a single zero's transformed leading current. -/
def pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock
    (K : ℕ) (rho : NontrivialZetaZero) (a b : Fin 2) : ℂ :=
  twoChannelMatrixBlockSum
    (pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent K rho) a b

/-- Exact two-form expansion of one zero's transformed leading channel
block. -/
def pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockForm
    (K : ℕ) (rho : NontrivialZetaZero) (a b : Fin 2) : ℂ :=
  (analyticZetaZeroMultiplicity rho : ℂ) *
    (finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (twoChannelVectorSlice
          (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
            (fun r : Fin K ↦ r.val) rho) a)
        (twoChannelVectorSlice
          (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
              (fun r : Fin K ↦ r.val) rho +
            pairedEtaTopPrefixFiniteCutoffFamilyFeature
              (pairedEtaTopPrefixFiniteSuccessorCutoff
                (fun r : Fin K ↦ r.val)) rho) b) +
      finiteGaussianOddHeatTransposeBilinear
        (fun r : Fin K ↦ pairedEtaCutoffLogFrequency r.val)
        (twoChannelVectorSlice
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature
            (pairedEtaTopPrefixFiniteSuccessorCutoff
              (fun r : Fin K ↦ r.val)) rho) a)
        (twoChannelVectorSlice
          (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
            (fun r : Fin K ↦ r.val) rho) b))

/-- The actual channel block of one zero's heat/Hilbert leading current is
exactly its multiplicity-weighted sum of two transpose heat forms. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_eq_blockForm
    (K : ℕ) (rho : NontrivialZetaZero) (a b : Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock K rho a b =
      pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockForm
        K rho a b := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteZeroLeadingMatrixCurrent
  rw [complexSymmetricLeadingTransportCurrent_eq_two_outerProducts,
    smul_add, finiteGaussianOddHeatTransform_add,
    finiteGaussianOddHeatTransform_smul,
    finiteGaussianOddHeatTransform_smul,
    twoChannelMatrixBlockSum_add,
    twoChannelMatrixBlockSum_smul,
    twoChannelMatrixBlockSum_smul,
    twoChannelMatrixBlockSum_etaOddHeatTransform_vecMulVec,
    twoChannelMatrixBlockSum_etaOddHeatTransform_vecMulVec]
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockForm
  ring

/-- Weighted Euclidean scale appearing in the centered eta cutoff
Montgomery--Vaughan bound. -/
def pairedEtaFiniteCutoffLogHilbertScale
    (K : ℕ) (x : Fin K → ℂ) : ℝ :=
  Real.sqrt ((((2 * K : ℕ) : ℝ)) * ∑ r, ‖x r‖ ^ 2)

/-- Explicit Montgomery--Vaughan envelope for one zero's transformed leading
channel block. -/
def pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockEnvelope
    (K : ℕ) (rho : NontrivialZetaZero) (a b : Fin 2) : ℝ :=
  ‖(analyticZetaZeroMultiplicity rho : ℂ)‖ *
    (26 *
        pairedEtaFiniteCutoffLogHilbertScale K
          (twoChannelVectorSlice
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
              (fun r : Fin K ↦ r.val) rho) a) *
        pairedEtaFiniteCutoffLogHilbertScale K
          (twoChannelVectorSlice
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
                (fun r : Fin K ↦ r.val) rho +
              pairedEtaTopPrefixFiniteCutoffFamilyFeature
                (pairedEtaTopPrefixFiniteSuccessorCutoff
                  (fun r : Fin K ↦ r.val)) rho) b) +
      26 *
        pairedEtaFiniteCutoffLogHilbertScale K
          (twoChannelVectorSlice
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature
              (pairedEtaTopPrefixFiniteSuccessorCutoff
                (fun r : Fin K ↦ r.val)) rho) a) *
        pairedEtaFiniteCutoffLogHilbertScale K
          (twoChannelVectorSlice
            (pairedEtaTopPrefixFiniteCutoffFamilyLeadingArithmeticIncrement
              (fun r : Fin K ↦ r.val) rho) b))

/-- The norm of every one-zero leading channel block is bounded by its
explicit constant-26 Montgomery--Vaughan envelope. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_norm_le
    {K : ℕ} (hK : 0 < K) (rho : NontrivialZetaZero)
    (a b : Fin 2) :
    ‖pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock K rho a b‖ ≤
      pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockEnvelope
        K rho a b := by
  rw [pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_eq_blockForm]
  unfold pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockForm
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockEnvelope
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact
      pairedEtaFiniteCutoffLog_oddHeatTranspose_mvHilbert_twentySix
        hK _ _
  · exact
      pairedEtaFiniteCutoffLog_oddHeatTranspose_mvHilbert_twentySix
        hK _ _

/-! ## Exact signed spectral-window aggregation -/

/-- Direct odd heat/Hilbert transform of the genuine multiplicity-weighted
leading current over a finite spectral zero window. -/
def pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent
    (K : ℕ) (T : ℝ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  finiteGaussianOddHeatTransform
    (pairedEtaTopPrefixFiniteCutoffFamilyHeatNode
      (fun r : Fin K ↦ r.val))
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
      (fun r : Fin K ↦ r.val) T)

/-- The direct odd and square-root representations of the actual transformed
leading window current agree exactly. -/
theorem pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent_eq_sqrt
    (K : ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent K T =
      pairedEtaTopPrefixFiniteHeatHilbertLeadingMatrixCurrent K T := by
  unfold pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteHeatHilbertLeadingMatrixCurrent
  exact finiteGaussianOddHeatTransform_eq_orientedSqrt _ _

/-- The complete direct odd heat/Hilbert leading window current is
skew-symmetric. -/
theorem pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent_transpose_eq_neg
    (K : ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent K T)ᵀ =
      -pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent K T := by
  unfold pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent
  exact finiteGaussianOddHeatTransform_transpose_of_isSymm _ _
    (pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent_isSymm _ T)

/-- One channel block of the complete transformed leading current over a
genuine finite spectral zero window. -/
def pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock
    (K : ℕ) (T : ℝ) (a b : Fin 2) : ℂ :=
  twoChannelMatrixBlockSum
    (pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent K T) a b

/-- The complete leading channel block is the exact signed sum of the
one-zero heat/Hilbert block forms, with analytic multiplicity retained. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_eq_zeroSum
    (K : ℕ) (T : ℝ) (a b : Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T a b =
      ∑ rho ∈ spectralZetaZeroWindow T,
        pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock K rho a b := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock
    pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteZeroWindowLeadingMatrixCurrent
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock
    pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingMatrixCurrent
  rw [finiteGaussianOddHeatTransform_finsetSum,
    twoChannelMatrixBlockSum_finsetSum]

/-- Swapping the two hyperbolic channel colours negates the complete signed
leading block. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_swap
    (K : ℕ) (T : ℝ) (a b : Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T b a =
      -pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T a b := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock
  exact twoChannelMatrixBlockSum_swap_of_transpose_eq_neg _
    (pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent_transpose_eq_neg
      K T) a b

/-- Every same-colour block of the complete signed leading current vanishes;
only the oriented mixed-colour current can remain. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_self_eq_zero
    (K : ℕ) (T : ℝ) (a : Fin 2) :
    pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T a a = 0 := by
  unfold pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock
  exact twoChannelMatrixBlockSum_self_eq_zero_of_transpose_eq_neg _
    (pairedEtaTopPrefixFiniteOddHeatHilbertLeadingMatrixCurrent_transpose_eq_neg
      K T) a

/-- Coarse finite-window envelope obtained only after retaining the exact
signed zero sum.  Improving this triangle bound by arithmetic cross-zero
cancellation is the remaining frontier. -/
theorem pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_norm_le_sum
    {K : ℕ} (hK : 0 < K) (T : ℝ) (a b : Fin 2) :
    ‖pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock K T a b‖ ≤
      ∑ rho ∈ spectralZetaZeroWindow T,
        pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlockEnvelope
          K rho a b := by
  rw [pairedEtaTopPrefixFiniteHeatHilbertWindowLeadingBlock_eq_zeroSum]
  refine (norm_sum_le _ _).trans ?_
  gcongr with rho hrho
  exact pairedEtaTopPrefixFiniteHeatHilbertZeroLeadingBlock_norm_le
    hK rho a b

end

end RiemannGaussian
