import RiemannGaussian.Hybrid.EtaGeometricPrefixVandermonde
import RiemannGaussian.EtaEnergyFiniteWindowReflectionCorrelation

/-!
# Full-rank geometric blocks of the packed eta hyperbolic feature

The literal Vandermonde theorem separates a finite zeta-zero window through
raw multiplicity-minus-one eta prefixes.  The certificate, however, uses the
two-channel completed hyperbolic feature.  This module proves that the
separation survives that exact packing.

For each geometric endpoint we use its predecessor as the feature cutoff,
because the completed finite channel evaluates its raw eta prefix at the
successor cutoff.  The original completed channel is then a nonzero diagonal
row scaling of the previously checked raw prefix matrix.  Its aligned
conjugate channel is the entrywise complex conjugate of that matrix, so it is
nonsingular as well.

Finally, one fixed complex-linear projection of the even/odd hyperbolic
coordinates recovers the aligned conjugate channel at every cutoff.  Hence
the actual packed certificate features belonging to all distinct zeros in an
arbitrary finite window are linearly independent at all sufficiently late
geometric blocks.  This is a full-information carrier theorem, not yet the
quantitative arithmetic inequality required for a zero-location certificate.
-/

open Complex Filter
open scoped BigOperators Classical ComplexConjugate Matrix

namespace RiemannGaussian

noncomputable section

/-- Feature cutoff immediately preceding the geometric raw-prefix endpoint. -/
def pairedEtaGeometricHyperbolicCutoff (q n j : ℕ) : ℕ :=
  etaGeometricOddEndpointCutoff q (n + j) - 1

/-- At every positive sample index, the successor of the feature cutoff is
exactly the intended geometric raw-prefix endpoint. -/
theorem pairedEtaGeometricHyperbolicCutoff_succ
    {q n : ℕ} (hqOdd : Odd q) (hq : 1 < q) (hn : 1 ≤ n) (j : ℕ) :
    pairedEtaGeometricHyperbolicCutoff q n j + 1 =
      etaGeometricOddEndpointCutoff q (n + j) := by
  have hpow : 1 < q ^ (n + j) :=
    one_lt_pow₀ hq (by omega)
  have hend := etaGeometricOddEndpointCutoff_endpoint hqOdd (n + j)
  have hcut : 1 ≤ etaGeometricOddEndpointCutoff q (n + j) := by
    omega
  exact Nat.sub_add_cancel hcut

/-- Nonzero completion factor multiplying one raw eta-prefix row. -/
def pairedEtaGeometricCompletionRowFactor
    (rho : NontrivialZetaZero) : ℂ :=
  pairedEtaXiCompletionFactor rho.val * rho.val

/-- The completed row factor never vanishes at a nontrivial zeta zero. -/
theorem pairedEtaGeometricCompletionRowFactor_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaGeometricCompletionRowFactor rho ≠ 0 := by
  exact mul_ne_zero
    (pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho))
    (NontrivialZetaZero.coe_ne_zero rho)

/-- Square evaluation matrix of the original completed eta channel at the
predecessors of consecutive geometric endpoints. -/
def pairedEtaGeometricOriginalChannelMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card) ℂ := fun i j ↦
  pairedEtaTopPrefixFiniteOriginalChannelTerm
    ((etaZeroWindowEquivFin s).symm i)
    (pairedEtaGeometricHyperbolicCutoff q n j)

/-- The completed original-channel matrix is exactly a nonzero diagonal row
scaling of the literal raw-prefix matrix. -/
theorem pairedEtaGeometricOriginalChannelMatrix_eq_diagonal_mul
    {q n : ℕ} (s : Finset NontrivialZetaZero)
    (hqOdd : Odd q) (hq : 1 < q) (hn : 1 ≤ n) :
    pairedEtaGeometricOriginalChannelMatrix q s n =
      Matrix.diagonal (fun i ↦
        pairedEtaGeometricCompletionRowFactor
          ((etaZeroWindowEquivFin s).symm i)) *
        pairedEtaLowerMomentGeometricPrefixMatrix q s n := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  unfold pairedEtaGeometricOriginalChannelMatrix
    pairedEtaTopPrefixFiniteOriginalChannelTerm
    pairedEtaGeometricCompletionRowFactor
  rw [pairedEtaGeometricHyperbolicCutoff_succ hqOdd hq hn]
  rfl

/-- A nonsingular raw geometric prefix block gives a nonsingular completed
original-channel block at the corresponding feature cutoffs. -/
theorem det_pairedEtaGeometricOriginalChannelMatrix_ne_zero
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hqOdd : Odd q) (hq : 1 < q) (hn : 1 ≤ n)
    (hdet : (pairedEtaLowerMomentGeometricPrefixMatrix q s n).det ≠ 0) :
    (pairedEtaGeometricOriginalChannelMatrix q s n).det ≠ 0 := by
  rw [pairedEtaGeometricOriginalChannelMatrix_eq_diagonal_mul
      s hqOdd hq hn,
    Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _hi ↦
      pairedEtaGeometricCompletionRowFactor_ne_zero
        ((etaZeroWindowEquivFin s).symm i))
    hdet

/-- Square evaluation matrix of the aligned conjugate channel carried inside
the two-coordinate hyperbolic feature. -/
def pairedEtaGeometricAlignedConjugateMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card) ℂ := fun i j ↦
  pairedEtaTopPrefixFiniteAlignedConjugateTerm
    ((etaZeroWindowEquivFin s).symm i)
    (pairedEtaGeometricHyperbolicCutoff q n j)

/-- The aligned channel matrix is the entrywise complex conjugate of the
original completed-channel matrix. -/
theorem pairedEtaGeometricAlignedConjugateMatrix_eq_map_star
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    pairedEtaGeometricAlignedConjugateMatrix q s n =
      (starRingEnd ℂ).mapMatrix
        (pairedEtaGeometricOriginalChannelMatrix q s n) := by
  ext i j
  rw [RingHom.mapMatrix_apply]
  exact topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm
    ((etaZeroWindowEquivFin s).symm i)
    (pairedEtaGeometricHyperbolicCutoff q n j)

/-- Complex conjugation preserves nonsingularity of the completed channel
matrix. -/
theorem det_pairedEtaGeometricAlignedConjugateMatrix_ne_zero
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hqOdd : Odd q) (hq : 1 < q) (hn : 1 ≤ n)
    (hdet : (pairedEtaLowerMomentGeometricPrefixMatrix q s n).det ≠ 0) :
    (pairedEtaGeometricAlignedConjugateMatrix q s n).det ≠ 0 := by
  rw [pairedEtaGeometricAlignedConjugateMatrix_eq_map_star,
    ← RingHom.map_det]
  simpa only [starRingEnd_apply, star_ne_zero] using
    det_pairedEtaGeometricOriginalChannelMatrix_ne_zero
      hqOdd hq hn hdet

/-- Fixed complex-linear projection which extracts the aligned conjugate
channel from every packed even/odd hyperbolic feature. -/
def pairedEtaHyperbolicAlignedProjection (d : Type*) :
    (d × Fin 2 → ℂ) →ₗ[ℂ] (d → ℂ) where
  toFun v j := (v (j, 0) + I * v (j, 1)) / 2
  map_add' v w := by
    funext j
    simp
    ring
  map_smul' c v := by
    funext j
    simp [smul_eq_mul]
    ring

/-- The fixed projection recovers the aligned channel at every member of an
arbitrary cutoff family. -/
theorem pairedEtaHyperbolicAlignedProjection_cutoffFamilyFeature
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaHyperbolicAlignedProjection d
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) =
      fun j ↦ pairedEtaTopPrefixFiniteAlignedConjugateTerm rho (cutoff j) := by
  funext j
  change
    (pairedEtaTopPrefixFiniteEvenCoordinate rho (cutoff j) +
        I * (I * pairedEtaTopPrefixFiniteOddCoordinate rho (cutoff j))) / 2 =
      pairedEtaTopPrefixFiniteAlignedConjugateTerm rho (cutoff j)
  unfold
    pairedEtaTopPrefixFiniteEvenCoordinate
    pairedEtaTopPrefixFiniteOddCoordinate
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- A nonsingular literal raw-prefix block makes the corresponding actual
packed eta hyperbolic features linearly independent. -/
theorem linearIndependent_pairedEtaGeometricPackedHyperbolicFeature
    {q n : ℕ} {s : Finset NontrivialZetaZero}
    (hqOdd : Odd q) (hq : 1 < q) (hn : 1 ≤ n)
    (hdet : (pairedEtaLowerMomentGeometricPrefixMatrix q s n).det ≠ 0) :
    LinearIndependent ℂ (fun i : Fin s.card ↦
      pairedEtaTopPrefixFiniteCutoffFamilyFeature
        (fun j : Fin s.card ↦
          pairedEtaGeometricHyperbolicCutoff q n j)
        ((etaZeroWindowEquivFin s).symm i)) := by
  have hrows : LinearIndependent ℂ
      (fun i ↦ pairedEtaGeometricAlignedConjugateMatrix q s n i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero
      (det_pairedEtaGeometricAlignedConjugateMatrix_ne_zero
        hqOdd hq hn hdet)
  rw [Fintype.linearIndependent_iff]
  intro c hsum i
  have hprojected := congrArg
    (pairedEtaHyperbolicAlignedProjection (Fin s.card)) hsum
  simp only [map_sum, map_smul, map_zero] at hprojected
  have hrowsum :
      ∑ k, c k • pairedEtaGeometricAlignedConjugateMatrix q s n k = 0 := by
    funext j
    have hj := congrFun hprojected j
    simpa only [Finset.sum_apply, Pi.smul_apply,
      pairedEtaGeometricAlignedConjugateMatrix,
      pairedEtaHyperbolicAlignedProjection_cutoffFamilyFeature] using hj
  exact Fintype.linearIndependent_iff.mp hrows c hrowsum i

/-- Every finite zeta-zero window has an odd prime geometric base for which
all sufficiently late blocks of its actual packed eta hyperbolic features are
linearly independent. -/
theorem exists_prime_eventually_linearIndependent_pairedEtaGeometricPackedHyperbolicFeature
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        LinearIndependent ℂ (fun i : Fin s.card ↦
          pairedEtaTopPrefixFiniteCutoffFamilyFeature
            (fun j : Fin s.card ↦
              pairedEtaGeometricHyperbolicCutoff q n j)
            ((etaZeroWindowEquivFin s).symm i)) := by
  obtain ⟨q, hqPrime, hqOdd, hq, hdet⟩ :=
    exists_prime_eventually_det_pairedEtaLowerMomentGeometricPrefixMatrix_ne_zero s
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hdet, Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hdetn hn
  exact linearIndependent_pairedEtaGeometricPackedHyperbolicFeature
    hqOdd hq hn hdetn

end

end RiemannGaussian
