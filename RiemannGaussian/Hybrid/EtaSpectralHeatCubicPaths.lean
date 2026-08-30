import RiemannGaussian.Hybrid.EtaSpectralHeatClosedPaths

/-!
# Cubic support/gap paths of compressed eta spectral heat

The quadratic projection ledger retains one excursion into the omitted
channel.  At cubic order there are three distinct path colours, and merging
them would discard new information.  For a Hermitian idempotent projection
`P`, its complement `Q`, and three matrices `H₁,H₂,H₃`, this module names

* the path through `Q` at the first separator and `P` at the second;
* the path through `P` at the first separator and `Q` at the second; and
* the path through `Q` at both separators.

Lean proves that the product of three compressed matrices is the uncompressed
three-step path minus exactly these three channels.  Adjoint reverses the path:
the two one-gap channels are paired, while the two-gap channel is Hermitian at
equal inputs.  For a positive-semidefinite equal input, the two-gap path is
itself positive semidefinite and factors through the complementary compressed
matrix as a weighted transition Gram.

The final layer instantiates the identity on the literal eta zero-window
spectral heat and an arbitrary cutoff/colour coordinate selection.  Each
channel is expanded entrywise as an ordered double sum over its retained or
omitted intermediate coordinates.  No channel is replaced by its norm and no
sign is asserted for the paired one-gap trace.  This is an exact cubic
information ledger, not a heat-crossing estimate or a zeta-zero proportion.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Three channel-coloured projection paths -/

/-- Three-step compressed path which visits the complementary channel at the
first separator and the retained channel at the second. -/
def projectionCubicFirstGapPath
    (P H₁ H₂ H₃ : Matrix n n K) : Matrix n n K :=
  P * H₁ * projectionComplement P * H₂ * P * H₃ * P

/-- Three-step compressed path which visits the retained channel at the first
separator and the complementary channel at the second. -/
def projectionCubicSecondGapPath
    (P H₁ H₂ H₃ : Matrix n n K) : Matrix n n K :=
  P * H₁ * P * H₂ * projectionComplement P * H₃ * P

/-- Three-step compressed path which visits the complementary channel at both
separators. -/
def projectionCubicTwoGapPath
    (P H₁ H₂ H₃ : Matrix n n K) : Matrix n n K :=
  P * H₁ * projectionComplement P * H₂ *
    projectionComplement P * H₃ * P

/-- Exact cubic path ledger: the fully retained path is the uncompressed
three-step path minus the two ordered one-gap paths and the two-gap path. -/
theorem compressedMatrix_mul_three
    (P H₁ H₂ H₃ : Matrix n n K) (hPid : P * P = P) :
    compressedMatrix P H₁ * compressedMatrix P H₂ * compressedMatrix P H₃ =
      compressedMatrix P (H₁ * H₂ * H₃) -
        projectionCubicFirstGapPath P H₁ H₂ H₃ -
        projectionCubicSecondGapPath P H₁ H₂ H₃ -
        projectionCubicTwoGapPath P H₁ H₂ H₃ := by
  unfold compressedMatrix projectionCubicFirstGapPath
    projectionCubicSecondGapPath projectionCubicTwoGapPath
    projectionComplement
  noncomm_ring [hPid]
  simp only [← Matrix.mul_assoc, hPid]

/-- Adjoint path reversal exchanges the first-gap and second-gap channels. -/
theorem projectionCubicFirstGapPath_conjTranspose
    {P H₁ H₂ H₃ : Matrix n n K}
    (hP : P.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) (hH₃ : H₃.IsHermitian) :
    (projectionCubicFirstGapPath P H₁ H₂ H₃)ᴴ =
      projectionCubicSecondGapPath P H₃ H₂ H₁ := by
  have hQ := projectionComplement_isHermitian hP
  unfold projectionCubicFirstGapPath projectionCubicSecondGapPath
  simp only [conjTranspose_mul, hP.eq, hH₁.eq, hH₂.eq, hH₃.eq, hQ.eq]
  noncomm_ring

/-- Adjoint path reversal reverses the three inputs of the two-gap channel. -/
theorem projectionCubicTwoGapPath_conjTranspose
    {P H₁ H₂ H₃ : Matrix n n K}
    (hP : P.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) (hH₃ : H₃.IsHermitian) :
    (projectionCubicTwoGapPath P H₁ H₂ H₃)ᴴ =
      projectionCubicTwoGapPath P H₃ H₂ H₁ := by
  have hQ := projectionComplement_isHermitian hP
  unfold projectionCubicTwoGapPath
  simp only [conjTranspose_mul, hP.eq, hH₁.eq, hH₂.eq, hH₃.eq, hQ.eq]
  noncomm_ring

/-- At equal Hermitian inputs, the two-gap path is a weighted transition Gram
whose middle weight is the heat compressed to the complementary channel. -/
theorem projectionCubicTwoGapPath_eq_weightedTransitionGram
    {P H : Matrix n n K} (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    projectionCubicTwoGapPath P H H H =
      (projectionLeakageTransition P H)ᴴ *
        compressedMatrix (projectionComplement P) H *
          projectionLeakageTransition P H := by
  have hQ := projectionComplement_isHermitian hP
  have hQid := projectionComplement_mul_self hPid
  symm
  calc
    (projectionLeakageTransition P H)ᴴ *
          compressedMatrix (projectionComplement P) H *
            projectionLeakageTransition P H =
        P * H * projectionComplement P *
          (projectionComplement P * H * projectionComplement P) *
          (projectionComplement P * H * P) := by
      unfold projectionLeakageTransition compressedMatrix
      simp only [conjTranspose_mul, hP.eq, hH.eq, hQ.eq]
      noncomm_ring
    _ = P * H *
          (projectionComplement P * projectionComplement P) * H *
          (projectionComplement P * projectionComplement P) * H * P := by
      noncomm_ring
    _ = P * H * projectionComplement P * H *
          projectionComplement P * H * P := by rw [hQid]
    _ = projectionCubicTwoGapPath P H H H := rfl

/-- The equal-input two-gap path is positive semidefinite whenever the input
matrix is positive semidefinite. -/
theorem projectionCubicTwoGapPath_posSemidef
    {P H : Matrix n n K} (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.PosSemidef) :
    (projectionCubicTwoGapPath P H H H).PosSemidef := by
  rw [projectionCubicTwoGapPath_eq_weightedTransitionGram
    hP hPid hH.isHermitian]
  exact
    (compressedMatrix_posSemidef (projectionComplement_isHermitian hP) hH)
      |>.conjTranspose_mul_mul_same _

omit [DecidableEq n] in
/-- Real trace is unchanged by conjugate transpose. -/
theorem rtrace_conjTranspose (A : Matrix n n K) :
    rtrace Aᴴ = rtrace A := by
  simp [rtrace, Matrix.trace_conjTranspose]

/-- At equal Hermitian inputs, the two ordered one-gap channels have equal
real traces because they are adjoints. -/
theorem rtrace_projectionCubicFirstGapPath_eq_second
    {P H : Matrix n n K} (hP : P.IsHermitian) (hH : H.IsHermitian) :
    rtrace (projectionCubicFirstGapPath P H H H) =
      rtrace (projectionCubicSecondGapPath P H H H) := by
  rw [← rtrace_conjTranspose
    (projectionCubicFirstGapPath P H H H)]
  rw [projectionCubicFirstGapPath_conjTranspose hP hH hH hH]

/-- The equal-input two-gap trace is nonnegative. -/
theorem rtrace_projectionCubicTwoGapPath_nonneg
    {P H : Matrix n n K} (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.PosSemidef) :
    0 ≤ rtrace (projectionCubicTwoGapPath P H H H) :=
  rtrace_nonneg_of_posSemidef
    (projectionCubicTwoGapPath_posSemidef hP hPid hH)

/-! ## Coordinate-resolved three-step paths -/

/-- A three-step path through two independently selected coordinate channels
is the ordered double sum over those two intermediate coordinates. -/
theorem mul_coordinateProjection_mul_coordinateProjection_mul_apply
    (middle₁ middle₂ : n → Prop)
    [DecidablePred middle₁] [DecidablePred middle₂]
    (H₁ H₂ H₃ : Matrix n n K) (i j : n) :
    (H₁ * coordinateProjection (K := K) middle₁ * H₂ *
      coordinateProjection (K := K) middle₂ * H₃) i j =
      ∑ a with middle₁ a, ∑ b with middle₂ b,
        H₁ i a * H₂ a b * H₃ b j := by
  rw [show H₁ * coordinateProjection (K := K) middle₁ * H₂ *
      coordinateProjection middle₂ * H₃ =
    H₁ * coordinateProjection middle₁ *
      (H₂ * coordinateProjection middle₂ * H₃) by
    noncomm_ring]
  rw [mul_coordinateProjection_mul_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [mul_coordinateProjection_mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- Entrywise first-gap path: omitted first intermediate coordinate, retained
second intermediate coordinate, and retained endpoints. -/
theorem projectionCubicFirstGapPath_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H₁ H₂ H₃ : Matrix n n K) (i j : n) :
    projectionCubicFirstGapPath
        (coordinateProjection keep) H₁ H₂ H₃ i j =
      if keep i ∧ keep j then
        ∑ a with ¬ keep a, ∑ b with keep b,
          H₁ i a * H₂ a b * H₃ b j
      else 0 := by
  rw [show projectionCubicFirstGapPath
        (coordinateProjection keep) H₁ H₂ H₃ =
      compressedMatrix (coordinateProjection keep)
        (H₁ * coordinateProjection (fun a ↦ ¬ keep a) * H₂ *
          coordinateProjection keep * H₃) by
    unfold projectionCubicFirstGapPath compressedMatrix
    rw [projectionComplement_coordinateProjection]
    noncomm_ring]
  rw [compressedMatrix_coordinateProjection_apply]
  by_cases hij : keep i ∧ keep j
  · simp only [if_pos hij]
    exact mul_coordinateProjection_mul_coordinateProjection_mul_apply
      (fun a ↦ ¬ keep a) keep H₁ H₂ H₃ i j
  · simp [hij]

/-- Entrywise second-gap path: retained first intermediate coordinate,
omitted second intermediate coordinate, and retained endpoints. -/
theorem projectionCubicSecondGapPath_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H₁ H₂ H₃ : Matrix n n K) (i j : n) :
    projectionCubicSecondGapPath
        (coordinateProjection keep) H₁ H₂ H₃ i j =
      if keep i ∧ keep j then
        ∑ a with keep a, ∑ b with ¬ keep b,
          H₁ i a * H₂ a b * H₃ b j
      else 0 := by
  rw [show projectionCubicSecondGapPath
        (coordinateProjection keep) H₁ H₂ H₃ =
      compressedMatrix (coordinateProjection keep)
        (H₁ * coordinateProjection keep * H₂ *
          coordinateProjection (fun b ↦ ¬ keep b) * H₃) by
    unfold projectionCubicSecondGapPath compressedMatrix
    rw [projectionComplement_coordinateProjection]
    noncomm_ring]
  rw [compressedMatrix_coordinateProjection_apply]
  by_cases hij : keep i ∧ keep j
  · simp only [if_pos hij]
    exact mul_coordinateProjection_mul_coordinateProjection_mul_apply
      keep (fun b ↦ ¬ keep b) H₁ H₂ H₃ i j
  · simp [hij]

/-- Entrywise two-gap path: both intermediate coordinates are omitted while
both endpoints remain retained. -/
theorem projectionCubicTwoGapPath_coordinateProjection_apply
    (keep : n → Prop) [DecidablePred keep]
    (H₁ H₂ H₃ : Matrix n n K) (i j : n) :
    projectionCubicTwoGapPath
        (coordinateProjection keep) H₁ H₂ H₃ i j =
      if keep i ∧ keep j then
        ∑ a with ¬ keep a, ∑ b with ¬ keep b,
          H₁ i a * H₂ a b * H₃ b j
      else 0 := by
  rw [show projectionCubicTwoGapPath
        (coordinateProjection keep) H₁ H₂ H₃ =
      compressedMatrix (coordinateProjection keep)
        (H₁ * coordinateProjection (fun a ↦ ¬ keep a) * H₂ *
          coordinateProjection (fun b ↦ ¬ keep b) * H₃) by
    unfold projectionCubicTwoGapPath compressedMatrix
    rw [projectionComplement_coordinateProjection]
    noncomm_ring]
  rw [compressedMatrix_coordinateProjection_apply]
  by_cases hij : keep i ∧ keep j
  · simp only [if_pos hij]
    exact mul_coordinateProjection_mul_coordinateProjection_mul_apply
      (fun a ↦ ¬ keep a) (fun b ↦ ¬ keep b) H₁ H₂ H₃ i j
  · simp [hij]

/-! ## Cubic paths of the Hermitian heat semigroup -/

/-- First-gap cubic path of a projected Hermitian heat flow at three ordered
scales. -/
def hermitianHeatProjectionCubicFirstGapPath {A : Matrix n n K}
    (hA : A.IsHermitian) (P : Matrix n n K) (u v w : ℝ) : Matrix n n K :=
  projectionCubicFirstGapPath P (hermitianHeatFlow hA u)
    (hermitianHeatFlow hA v) (hermitianHeatFlow hA w)

/-- Second-gap cubic path of a projected Hermitian heat flow at three ordered
scales. -/
def hermitianHeatProjectionCubicSecondGapPath {A : Matrix n n K}
    (hA : A.IsHermitian) (P : Matrix n n K) (u v w : ℝ) : Matrix n n K :=
  projectionCubicSecondGapPath P (hermitianHeatFlow hA u)
    (hermitianHeatFlow hA v) (hermitianHeatFlow hA w)

/-- Two-gap cubic path of a projected Hermitian heat flow at three ordered
scales. -/
def hermitianHeatProjectionCubicTwoGapPath {A : Matrix n n K}
    (hA : A.IsHermitian) (P : Matrix n n K) (u v w : ℝ) : Matrix n n K :=
  projectionCubicTwoGapPath P (hermitianHeatFlow hA u)
    (hermitianHeatFlow hA v) (hermitianHeatFlow hA w)

/-- Exact three-scale cubic ledger for a projected Hermitian heat semigroup. -/
theorem compressedHermitianHeatFlow_mul_three
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (u v w : ℝ) :
    compressedHermitianHeatFlow hA P u *
        compressedHermitianHeatFlow hA P v *
          compressedHermitianHeatFlow hA P w =
      compressedHermitianHeatFlow hA P (u + v + w) -
        hermitianHeatProjectionCubicFirstGapPath hA P u v w -
        hermitianHeatProjectionCubicSecondGapPath hA P u v w -
        hermitianHeatProjectionCubicTwoGapPath hA P u v w := by
  unfold compressedHermitianHeatFlow
    hermitianHeatProjectionCubicFirstGapPath
    hermitianHeatProjectionCubicSecondGapPath
    hermitianHeatProjectionCubicTwoGapPath
  rw [compressedMatrix_mul_three _ _ _ _ hPid]
  rw [← hermitianHeatFlow_add hA u v]
  rw [← hermitianHeatFlow_add hA (u + v) w]

/-- At one heat scale the first-gap and second-gap traces are equal. -/
theorem rtrace_hermitianHeatProjectionCubicFirstGapPath_eq_second
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (u : ℝ) :
    rtrace (hermitianHeatProjectionCubicFirstGapPath hA P u u u) =
      rtrace (hermitianHeatProjectionCubicSecondGapPath hA P u u u) := by
  unfold hermitianHeatProjectionCubicFirstGapPath
    hermitianHeatProjectionCubicSecondGapPath
  exact rtrace_projectionCubicFirstGapPath_eq_second hP
    (hermitianHeatFlow_isHermitian hA u)

/-- At one heat scale the two-gap heat path is positive semidefinite. -/
theorem hermitianHeatProjectionCubicTwoGapPath_posSemidef
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P) (u : ℝ) :
    (hermitianHeatProjectionCubicTwoGapPath hA P u u u).PosSemidef := by
  unfold hermitianHeatProjectionCubicTwoGapPath
  exact projectionCubicTwoGapPath_posSemidef hP hPid
    (hermitianHeatFlow_posSemidef hA u)

end


end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## Literal eta coordinate-channel instantiation -/

/-- First-gap cubic path of the eta spectral heat under an arbitrary retained
cutoff/colour coordinate selection. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianHeatProjectionCubicFirstGapPath
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    (HermitianRankTrace.coordinateProjection keep) u v w

/-- Second-gap cubic path of the eta spectral heat under an arbitrary retained
cutoff/colour coordinate selection. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianHeatProjectionCubicSecondGapPath
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    (HermitianRankTrace.coordinateProjection keep) u v w

/-- Two-gap cubic path of the eta spectral heat under an arbitrary retained
cutoff/colour coordinate selection. -/
def pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianHeatProjectionCubicTwoGapPath
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    (HermitianRankTrace.coordinateProjection keep) u v w

/-- Exact cubic path ledger for the coordinate-compressed literal eta
spectral heat. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow_mul_three
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep u *
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep v *
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep w =
      pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
          cutoff hT keep (u + v + w) -
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath
          cutoff hT keep u v w -
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath
          cutoff hT keep u v w -
        pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
          cutoff hT keep u v w := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatFlow
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
  exact HermitianRankTrace.compressedHermitianHeatFlow_mul_three
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    (HermitianRankTrace.coordinateProjection_mul_self keep) u v w

/-- Entrywise literal first-gap eta path: omitted, then retained,
intermediate cutoff/colour coordinates. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath
        cutoff hT keep u v w i j =
      if keep i ∧ keep j then
        ∑ a with ¬ keep a, ∑ b with keep b,
          pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i a *
            pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v a b *
              pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT w b j
      else 0 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicFirstGapPath
    HermitianRankTrace.hermitianHeatProjectionCubicFirstGapPath
  exact
    HermitianRankTrace.projectionCubicFirstGapPath_coordinateProjection_apply
      keep _ _ _ i j

/-- Entrywise literal second-gap eta path: retained, then omitted,
intermediate cutoff/colour coordinates. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath
        cutoff hT keep u v w i j =
      if keep i ∧ keep j then
        ∑ a with keep a, ∑ b with ¬ keep b,
          pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i a *
            pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v a b *
              pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT w b j
      else 0 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicSecondGapPath
    HermitianRankTrace.hermitianHeatProjectionCubicSecondGapPath
  exact
    HermitianRankTrace.projectionCubicSecondGapPath_coordinateProjection_apply
      keep _ _ _ i j

/-- Entrywise literal two-gap eta path: both intermediate cutoff/colour
coordinates are omitted. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep]
    (u v w : ℝ) (i j : d × Fin 2) :
    pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
        cutoff hT keep u v w i j =
      if keep i ∧ keep j then
        ∑ a with ¬ keep a, ∑ b with ¬ keep b,
          pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT u i a *
            pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT v a b *
              pairedEtaTopPrefixFiniteZeroWindowSpectralHeatFlow cutoff hT w b j
      else 0 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
    HermitianRankTrace.hermitianHeatProjectionCubicTwoGapPath
  exact
    HermitianRankTrace.projectionCubicTwoGapPath_coordinateProjection_apply
      keep _ _ _ i j

/-- At one scale, the two-gap eta cubic path is positive semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (keep : d × Fin 2 → Prop) [DecidablePred keep] (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
      cutoff hT keep u u u).PosSemidef := by
  unfold pairedEtaTopPrefixFiniteZeroWindowCoordinateSpectralHeatCubicTwoGapPath
  exact HermitianRankTrace.hermitianHeatProjectionCubicTwoGapPath_posSemidef
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    (HermitianRankTrace.coordinateProjection_isHermitian keep)
    (HermitianRankTrace.coordinateProjection_mul_self keep) u

end


end RiemannGaussian
