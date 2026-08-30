import RiemannGaussian.Hybrid.EtaSignedHeatCertificate

/-!
# Coordinate-resolved leakage of the eta signed spectral heat

This module supplies a concrete finite interface between the literal eta
zero-window spectral heat and the abstract projection-leakage calculus.

An arbitrary decidable predicate on the packed `(cutoff, colour)` coordinates
defines a diagonal Hermitian idempotent projection.  The predicate may retain
any chosen cutoff family, either hyperbolic colour, or a coupled selection.
Lean computes compression, the complementary transition, and the full
ordered cross-scale leakage entry by entry.

For a retained predicate `keep`, the leakage entry is exactly

`if keep i ∧ keep j then sum k with ¬ keep k, H_u i k * H_v k j else 0`.

Thus the omitted coordinate, both endpoint colours, and both heat scales
remain visible.  The same leakage is also proved to be the transition Gram
`T_uᴴ * T_v`; adjunction reverses scale order, and at equal scales the
leakage is positive semidefinite.  Its real trace is exactly the transition
Frobenius mass, and the equal-scale trace ledger restores the missing mass
without replacing it by an inequality.

This is the finite coordinate-compression layer of the literal eta matrix.
It is not yet the infinite logarithmic-time eta support projection, and no
new zero-proportion estimate is asserted here.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Generic finite coordinate projections -/

/-- The diagonal projection retaining exactly the coordinates satisfying
`keep`. -/
def coordinateProjection (keep : n → Prop) [DecidablePred keep] :
    Matrix n n K :=
  Matrix.diagonal (fun i ↦ if keep i then 1 else 0)

omit [Fintype n] in
/-- Every finite coordinate projection is Hermitian. -/
theorem coordinateProjection_isHermitian (keep : n → Prop)
    [DecidablePred keep] :
    (coordinateProjection (K := K) keep).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  by_cases hi : keep i <;> simp [hi]

/-- Every finite coordinate projection is idempotent. -/
theorem coordinateProjection_mul_self (keep : n → Prop)
    [DecidablePred keep] :
    coordinateProjection (K := K) keep * coordinateProjection keep =
      coordinateProjection keep := by
  unfold coordinateProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [hi]

omit [Fintype n] in
/-- The complement of a coordinate projection retains exactly the omitted
coordinates. -/
theorem projectionComplement_coordinateProjection (keep : n → Prop)
    [DecidablePred keep] :
    projectionComplement (coordinateProjection (K := K) keep) =
      coordinateProjection (fun i ↦ ¬ keep i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : keep i <;>
      simp [projectionComplement, coordinateProjection, hi]
  · simp [projectionComplement, coordinateProjection, hij]

/-- Coordinate compression keeps an entry exactly when both endpoints are
retained. -/
theorem compressedMatrix_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H : Matrix n n K) (i j : n) :
    compressedMatrix (coordinateProjection keep) H i j =
      if keep i ∧ keep j then H i j else 0 := by
  unfold compressedMatrix coordinateProjection
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : keep i <;> by_cases hj : keep j <;> simp [hi, hj]

/-- The transition channel keeps precisely an omitted row and a retained
column. -/
theorem projectionLeakageTransition_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H : Matrix n n K) (i j : n) :
    projectionLeakageTransition (coordinateProjection keep) H i j =
      if ¬ keep i ∧ keep j then H i j else 0 := by
  unfold projectionLeakageTransition
  rw [projectionComplement_coordinateProjection]
  unfold coordinateProjection
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : keep i <;> by_cases hj : keep j <;> simp [hi, hj]

/-- Multiplication through a coordinate projection is exactly summation over
the retained intermediate coordinates. -/
theorem mul_coordinateProjection_mul_apply
    (keep : n → Prop) [DecidablePred keep]
    (H₁ H₂ : Matrix n n K) (i j : n) :
    (H₁ * coordinateProjection (K := K) keep * H₂) i j =
      ∑ k with keep k, H₁ i k * H₂ k j := by
  unfold coordinateProjection
  rw [Matrix.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Matrix.mul_diagonal]
  by_cases hkkeep : keep k <;> simp [hkkeep]

/-- Entrywise path expansion of coordinate leakage: retained endpoints are
coupled only through omitted intermediate coordinates. -/
theorem crossScaleProjectionLeakage_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H₁ H₂ : Matrix n n K) (i j : n) :
    crossScaleProjectionLeakage (coordinateProjection keep) H₁ H₂ i j =
      if keep i ∧ keep j then
        ∑ k with ¬ keep k, H₁ i k * H₂ k j
      else 0 := by
  unfold crossScaleProjectionLeakage
  rw [show coordinateProjection keep * H₁ *
        projectionComplement (coordinateProjection keep) * H₂ *
          coordinateProjection keep =
      compressedMatrix (coordinateProjection keep)
        (H₁ * coordinateProjection (fun k ↦ ¬ keep k) * H₂) by
    rw [projectionComplement_coordinateProjection]
    unfold compressedMatrix
    noncomm_ring]
  rw [compressedMatrix_coordinateProjection_apply]
  by_cases hij : keep i ∧ keep j
  · simp only [if_pos hij]
    exact mul_coordinateProjection_mul_apply (fun k ↦ ¬ keep k) H₁ H₂ i j
  · simp [hij]

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## Coordinate-resolved leakage of the literal eta spectral heat -/

/-- The eta zero-window spectral heat compressed to the packed coordinates
selected by `keep`. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.compressedMatrix
    (HermitianRankTrace.coordinateProjection keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u)

/-- The omitted-to-retained transition channel of the eta spectral heat. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.projectionLeakageTransition
    (HermitianRankTrace.coordinateProjection keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u)

/-- The complete ordered cross-scale leakage of the coordinate-compressed eta
spectral heat. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u v : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.crossScaleProjectionLeakage
    (HermitianRankTrace.coordinateProjection keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v)

/-- Entrywise formula for the coordinate-compressed eta spectral heat. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
        cutoff hT keep u i j =
      if keep i ∧ keep j then
        pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i j
      else 0 :=
  HermitianRankTrace.compressedMatrix_coordinateProjection_apply
    keep _ i j

/-- Entrywise formula for the omitted-to-retained eta transition channel. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
        cutoff hT keep u i j =
      if ¬ keep i ∧ keep j then
        pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i j
      else 0 :=
  HermitianRankTrace.projectionLeakageTransition_coordinateProjection_apply
    keep _ i j

/-- Exact eta path expansion: retained endpoints couple through the literal
sum over omitted packed cutoff/colour coordinates. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
        cutoff hT keep u v i j =
      if keep i ∧ keep j then
        ∑ k with ¬ keep k,
          pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i k *
            pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v k j
      else 0 :=
  HermitianRankTrace.crossScaleProjectionLeakage_coordinateProjection_apply
    keep _ _ i j

/-- Exact cross-scale semigroup ledger for the coordinate-compressed literal
eta spectral heat. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u v : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow cutoff hT keep u *
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow cutoff hT keep v =
      pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep (u + v) -
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
          cutoff hT keep u v := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
  rw [HermitianRankTrace.compressedMatrix_mul_compressedMatrix
    (HermitianRankTrace.coordinateProjection_mul_self keep)]
  rw [pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_add]

/-- Conjugate transpose of the eta coordinate leakage reverses its two heat
scales. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_conjTranspose
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u v : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
      cutoff hT keep u v)ᴴ =
      pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
        cutoff hT keep v u := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
  exact HermitianRankTrace.crossScaleProjectionLeakage_conjTranspose
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT v)

/-- The eta coordinate leakage is exactly the cross-scale Gram product of
its omitted-to-retained transition channels. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_eq_transitionGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u v : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
        cutoff hT keep u v =
      (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
          cutoff hT keep u)ᴴ *
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
          cutoff hT keep v := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
  exact HermitianRankTrace.crossScaleProjectionLeakage_eq_transitionGram
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)

/-- At equal scales the eta coordinate leakage is positive semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
      cutoff hT keep u u).PosSemidef := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
  exact HermitianRankTrace.projectionLeakage_posSemidef
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)

/-- The equal-scale eta coordinate leakage trace is exactly the squared
Frobenius mass of its transition channel. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_rtrace_eq_frobSq
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    HermitianRankTrace.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
          cutoff hT keep u u) =
      HermitianRankTrace.frobSq
        (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
          cutoff hT keep u) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
  exact HermitianRankTrace.projectionLeakage_rtrace_eq_frobSq
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)

/-- Equal-scale eta coordinate leakage vanishes exactly when the complete
omitted-to-retained transition channel vanishes. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_eq_zero_iff
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
        cutoff hT keep u u = 0 ↔
      pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
        cutoff hT keep u = 0 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatTransition
  exact HermitianRankTrace.projectionLeakage_eq_zero_iff
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)

/-- The real trace of equal-scale eta coordinate leakage is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage_rtrace_nonneg
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    0 ≤ HermitianRankTrace.rtrace
      (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
        cutoff hT keep u u) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
  exact HermitianRankTrace.projectionLeakage_rtrace_nonneg
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep)
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow_isHermitian cutoff hT u)

/-- Exact equal-scale trace accounting: the observed compressed square plus
the named transition mass equals the longer-time compressed heat trace. -/
theorem rtrace_pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow_sq_add_leakage
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    HermitianRankTrace.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
              cutoff hT keep u *
            pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
              cutoff hT keep u) +
        HermitianRankTrace.rtrace
          (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatLeakage
            cutoff hT keep u u) =
      HermitianRankTrace.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep (2 * u)) := by
  have h := congrArg HermitianRankTrace.rtrace
    (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow_mul
      cutoff hT keep u u)
  rw [show u + u = 2 * u by ring] at h
  simp only [HermitianRankTrace.rtrace, Matrix.trace_sub, map_sub] at h
  unfold HermitianRankTrace.rtrace
  linarith

end

end RiemannGaussian
