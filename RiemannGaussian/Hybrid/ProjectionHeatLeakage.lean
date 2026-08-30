import RiemannGaussian.Hybrid.SignedHeatInertia

/-!
# Information-preserving projection leakage for spectral heat

This module records exactly what is lost when a finite Hermitian heat
semigroup is compressed by one or two orthogonal projections.  For an
idempotent Hermitian matrix `P`, write `Q = 1 - P` and

`K_u = P * H_u * P`.

Instead of replacing the missing `Q` channel by an inequality, Lean retains
the ordered cross-scale leakage

`L_(u,v) = P * H_u * Q * H_v * P`.

It obeys

`K_u * K_v = K_(u+v) - L_(u,v)`

and factors as the cross-scale Gram matrix `T_uᴴ * T_v`, where
`T_u = Q * H_u * P`.  Thus scale ordering is retained, adjunction swaps the
two scales, and the same-scale leakage is positive semidefinite.  Its real
trace is exactly the squared Frobenius mass of the transition channel.

A second Hermitian projection `C` gives a finite-compression layer.  Lean
keeps the support-channel and finite-compression leakages separate and proves
the exact two-stage ledger

`M_u * M_v = M_(u+v) - supportLeakage_(u,v) - compressionLeakage_(u,v)`.

At equal scales both corrections are positive semidefinite and their traces
are exact transition Frobenius masses.  This is finite matrix algebra; no eta
support operator or zeta-zero estimate is assumed in this module.
-/

open Matrix Finset
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## One projection and its retained transition channel -/

/-- The complementary matrix `1 - P` associated with a candidate projection
`P`. -/
def projectionComplement (P : Matrix n n K) : Matrix n n K :=
  1 - P

/-- Compression of a matrix `H` to the range selected by `P`. -/
def compressedMatrix (P H : Matrix n n K) : Matrix n n K :=
  P * H * P

/-- The ordered leakage left by compressing two matrices at distinct scales.
The order of `H₁` and `H₂` is deliberately retained. -/
def crossScaleProjectionLeakage (P H₁ H₂ : Matrix n n K) : Matrix n n K :=
  P * H₁ * projectionComplement P * H₂ * P

/-- The transition from the retained `P` channel into its complementary
channel after application of `H`. -/
def projectionLeakageTransition (P H : Matrix n n K) : Matrix n n K :=
  projectionComplement P * H * P

omit [DecidableEq n] in
/-- Compression by a Hermitian matrix preserves Hermitian symmetry. -/
theorem compressedMatrix_isHermitian {P H : Matrix n n K}
    (hP : P.IsHermitian) (hH : H.IsHermitian) :
    (compressedMatrix P H).IsHermitian := by
  unfold compressedMatrix
  rw [Matrix.IsHermitian]
  simp only [conjTranspose_mul, hP.eq, hH.eq]
  noncomm_ring

omit [DecidableEq n] in
/-- Compression by a Hermitian matrix preserves positive semidefiniteness. -/
theorem compressedMatrix_posSemidef {P H : Matrix n n K}
    (hP : P.IsHermitian) (hH : H.PosSemidef) :
    (compressedMatrix P H).PosSemidef := by
  unfold compressedMatrix
  have h := hH.conjTranspose_mul_mul_same P
  rwa [hP.eq] at h

/-- The real trace of a positive-semidefinite finite matrix is nonnegative. -/
theorem rtrace_nonneg_of_posSemidef {H : Matrix n n K}
    (hH : H.PosSemidef) :
    0 ≤ rtrace H := by
  rw [rtrace_eq_sum_eigenvalues hH.isHermitian]
  exact Finset.sum_nonneg fun i _hi ↦ hH.eigenvalues_nonneg i

omit [Fintype n] in
/-- The complement of a Hermitian matrix is Hermitian. -/
theorem projectionComplement_isHermitian {P : Matrix n n K}
    (hP : P.IsHermitian) :
    (projectionComplement P).IsHermitian := by
  exact isHermitian_one.sub hP

/-- The complement of an idempotent matrix is idempotent. -/
theorem projectionComplement_mul_self {P : Matrix n n K}
    (hPid : P * P = P) :
    projectionComplement P * projectionComplement P =
      projectionComplement P := by
  unfold projectionComplement
  noncomm_ring [hPid]

/-- An idempotent matrix annihilates its complement on the right. -/
theorem projection_mul_complement {P : Matrix n n K}
    (hPid : P * P = P) :
    P * projectionComplement P = 0 := by
  unfold projectionComplement
  noncomm_ring [hPid]

/-- The complement of an idempotent matrix annihilates it on the right. -/
theorem complement_mul_projection {P : Matrix n n K}
    (hPid : P * P = P) :
    projectionComplement P * P = 0 := by
  unfold projectionComplement
  noncomm_ring [hPid]

/-- Exact one-stage compression ledger at two ordered scales.  The correction
is retained as a matrix rather than discarded into a bound. -/
theorem compressedMatrix_mul_compressedMatrix
    {P H₁ H₂ : Matrix n n K} (hPid : P * P = P) :
    compressedMatrix P H₁ * compressedMatrix P H₂ =
      compressedMatrix P (H₁ * H₂) -
        crossScaleProjectionLeakage P H₁ H₂ := by
  calc
    compressedMatrix P H₁ * compressedMatrix P H₂ =
        P * H₁ * (P * P) * H₂ * P := by
      unfold compressedMatrix
      noncomm_ring
    _ = P * H₁ * P * H₂ * P := by rw [hPid]
    _ = compressedMatrix P (H₁ * H₂) -
        crossScaleProjectionLeakage P H₁ H₂ := by
      unfold compressedMatrix crossScaleProjectionLeakage projectionComplement
      noncomm_ring

/-- Conjugate transpose reverses the scale order of the cross-scale
leakage. -/
theorem crossScaleProjectionLeakage_conjTranspose
    {P H₁ H₂ : Matrix n n K}
    (hP : P.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hH₂ : H₂.IsHermitian) :
    (crossScaleProjectionLeakage P H₁ H₂)ᴴ =
      crossScaleProjectionLeakage P H₂ H₁ := by
  have hQ := projectionComplement_isHermitian hP
  unfold crossScaleProjectionLeakage
  simp only [conjTranspose_mul, hP.eq, hH₁.eq, hH₂.eq, hQ.eq]
  noncomm_ring

/-- The ordered leakage is exactly the cross-scale Gram product of the two
retained transition channels.  Only the first input must be Hermitian because
it is the factor subjected to conjugate transpose. -/
theorem crossScaleProjectionLeakage_eq_transitionGram
    {P H₁ H₂ : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH₁ : H₁.IsHermitian) :
    crossScaleProjectionLeakage P H₁ H₂ =
      (projectionLeakageTransition P H₁)ᴴ *
        projectionLeakageTransition P H₂ := by
  have hQid := projectionComplement_mul_self hPid
  have hQ := projectionComplement_isHermitian hP
  symm
  calc
    (projectionLeakageTransition P H₁)ᴴ *
          projectionLeakageTransition P H₂ =
        P * H₁ * (projectionComplement P * projectionComplement P) * H₂ * P := by
      unfold projectionLeakageTransition
      simp only [conjTranspose_mul, hP.eq, hH₁.eq, hQ.eq]
      noncomm_ring
    _ = P * H₁ * projectionComplement P * H₂ * P := by rw [hQid]
    _ = crossScaleProjectionLeakage P H₁ H₂ := rfl

/-- At one scale the leakage is the ordinary Gram matrix of its transition
channel. -/
theorem projectionLeakage_eq_gram {P H : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    crossScaleProjectionLeakage P H H =
      (projectionLeakageTransition P H)ᴴ *
        projectionLeakageTransition P H :=
  crossScaleProjectionLeakage_eq_transitionGram hP hPid hH

/-- Same-scale projection leakage is positive semidefinite. -/
theorem projectionLeakage_posSemidef {P H : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    (crossScaleProjectionLeakage P H H).PosSemidef := by
  rw [projectionLeakage_eq_gram hP hPid hH]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Same-scale leakage vanishes exactly when the complementary transition
channel vanishes. -/
theorem projectionLeakage_eq_zero_iff {P H : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    crossScaleProjectionLeakage P H H = 0 ↔
      projectionLeakageTransition P H = 0 := by
  rw [projectionLeakage_eq_gram hP hPid hH,
    Matrix.conjTranspose_mul_self_eq_zero]

/-- The trace of the same-scale leakage is exactly the squared Frobenius mass
of the complementary transition channel. -/
theorem projectionLeakage_rtrace_eq_frobSq {P H : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    rtrace (crossScaleProjectionLeakage P H H) =
      frobSq (projectionLeakageTransition P H) := by
  rw [projectionLeakage_eq_gram hP hPid hH]
  rfl

/-- The real trace of same-scale projection leakage is nonnegative. -/
theorem projectionLeakage_rtrace_nonneg {P H : Matrix n n K}
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hH : H.IsHermitian) :
    0 ≤ rtrace (crossScaleProjectionLeakage P H H) := by
  exact rtrace_nonneg_of_posSemidef
    (projectionLeakage_posSemidef hP hPid hH)

/-! ## One projection applied to the Hermitian spectral heat semigroup -/

/-- The spectral heat flow compressed by a candidate projection `P`. -/
def compressedHermitianHeatFlow {A : Matrix n n K}
    (hA : A.IsHermitian) (P : Matrix n n K) (u : ℝ) : Matrix n n K :=
  compressedMatrix P (hermitianHeatFlow hA u)

/-- The exact ordered cross-scale leakage of the projected Hermitian heat
flow. -/
def hermitianHeatProjectionLeakage {A : Matrix n n K}
    (hA : A.IsHermitian) (P : Matrix n n K) (u v : ℝ) : Matrix n n K :=
  crossScaleProjectionLeakage P (hermitianHeatFlow hA u)
    (hermitianHeatFlow hA v)

/-- The product of two compressed spectral heat flows is the longer-time
compressed flow minus the retained ordered leakage. -/
theorem compressedHermitianHeatFlow_mul
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (u v : ℝ) :
    compressedHermitianHeatFlow hA P u *
        compressedHermitianHeatFlow hA P v =
      compressedHermitianHeatFlow hA P (u + v) -
        hermitianHeatProjectionLeakage hA P u v := by
  unfold compressedHermitianHeatFlow hermitianHeatProjectionLeakage
  rw [compressedMatrix_mul_compressedMatrix hPid]
  rw [hermitianHeatFlow_add]

/-- Adjoint reverses the two heat scales in the projected heat leakage. -/
theorem hermitianHeatProjectionLeakage_conjTranspose
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (u v : ℝ) :
    (hermitianHeatProjectionLeakage hA P u v)ᴴ =
      hermitianHeatProjectionLeakage hA P v u := by
  unfold hermitianHeatProjectionLeakage
  exact crossScaleProjectionLeakage_conjTranspose hP
    (hermitianHeatFlow_isHermitian hA u)
    (hermitianHeatFlow_isHermitian hA v)

/-- Equal-scale projected spectral heat leakage is positive semidefinite. -/
theorem hermitianHeatProjectionLeakage_posSemidef
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P) (u : ℝ) :
    (hermitianHeatProjectionLeakage hA P u u).PosSemidef := by
  unfold hermitianHeatProjectionLeakage
  exact projectionLeakage_posSemidef hP hPid
    (hermitianHeatFlow_isHermitian hA u)

/-- Equal-scale specialization of the projected heat-semigroup ledger. -/
theorem compressedHermitianHeatFlow_sq
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (u : ℝ) :
    compressedHermitianHeatFlow hA P u *
        compressedHermitianHeatFlow hA P u =
      compressedHermitianHeatFlow hA P (2 * u) -
        hermitianHeatProjectionLeakage hA P u u := by
  rw [compressedHermitianHeatFlow_mul hA hPid u u]
  congr 3
  ring

/-! ## Two-stage projection and finite-compression leakage -/

/-- A second projection `C` applied after the first projected heat flow. -/
def twoStageCompressedHermitianHeatFlow {A : Matrix n n K}
    (hA : A.IsHermitian) (P C : Matrix n n K) (u : ℝ) : Matrix n n K :=
  compressedMatrix C (compressedHermitianHeatFlow hA P u)

/-- Leakage created specifically by the second, finite-compression
projection. -/
def finiteCompressionHeatLeakage {A : Matrix n n K}
    (hA : A.IsHermitian) (P C : Matrix n n K) (u v : ℝ) : Matrix n n K :=
  crossScaleProjectionLeakage C
    (compressedHermitianHeatFlow hA P u)
    (compressedHermitianHeatFlow hA P v)

/-- The first projection's support-complement leakage, retained after
compression by the second projection. -/
def compressedSupportHeatLeakage {A : Matrix n n K}
    (hA : A.IsHermitian) (P C : Matrix n n K) (u v : ℝ) : Matrix n n K :=
  compressedMatrix C (hermitianHeatProjectionLeakage hA P u v)

/-- The first projection's complementary transition channel after the second
compression. -/
def compressedSupportLeakageTransition {A : Matrix n n K}
    (hA : A.IsHermitian) (P C : Matrix n n K) (u : ℝ) : Matrix n n K :=
  projectionLeakageTransition P (hermitianHeatFlow hA u) * C

/-- The complementary transition channel created by the second projection. -/
def finiteCompressionLeakageTransition {A : Matrix n n K}
    (hA : A.IsHermitian) (P C : Matrix n n K) (u : ℝ) : Matrix n n K :=
  projectionLeakageTransition C (compressedHermitianHeatFlow hA P u)

/-- A projected Hermitian heat flow remains Hermitian. -/
theorem compressedHermitianHeatFlow_isHermitian
    {A P : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (u : ℝ) :
    (compressedHermitianHeatFlow hA P u).IsHermitian := by
  unfold compressedHermitianHeatFlow
  exact compressedMatrix_isHermitian hP
    (hermitianHeatFlow_isHermitian hA u)

/-- Exact ordered two-stage ledger.  The first-projection leakage and the
second-projection leakage remain distinct matrix observables. -/
theorem twoStageCompressedHermitianHeatFlow_mul
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (hCid : C * C = C) (u v : ℝ) :
    twoStageCompressedHermitianHeatFlow hA P C u *
        twoStageCompressedHermitianHeatFlow hA P C v =
      twoStageCompressedHermitianHeatFlow hA P C (u + v) -
        compressedSupportHeatLeakage hA P C u v -
        finiteCompressionHeatLeakage hA P C u v := by
  unfold twoStageCompressedHermitianHeatFlow
  rw [compressedMatrix_mul_compressedMatrix hCid]
  rw [compressedHermitianHeatFlow_mul hA hPid]
  unfold compressedSupportHeatLeakage finiteCompressionHeatLeakage
  unfold compressedMatrix
  noncomm_ring

/-- Adjoint reverses scale order in the second-projection leakage. -/
theorem finiteCompressionHeatLeakage_conjTranspose
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hC : C.IsHermitian) (u v : ℝ) :
    (finiteCompressionHeatLeakage hA P C u v)ᴴ =
      finiteCompressionHeatLeakage hA P C v u := by
  unfold finiteCompressionHeatLeakage
  exact crossScaleProjectionLeakage_conjTranspose hC
    (compressedHermitianHeatFlow_isHermitian hA hP u)
    (compressedHermitianHeatFlow_isHermitian hA hP v)

/-- The compressed first-projection leakage is the cross-scale Gram product
of its retained transition channels. -/
theorem compressedSupportHeatLeakage_eq_transitionGram
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hC : C.IsHermitian) (u v : ℝ) :
    compressedSupportHeatLeakage hA P C u v =
      (compressedSupportLeakageTransition hA P C u)ᴴ *
        compressedSupportLeakageTransition hA P C v := by
  unfold compressedSupportHeatLeakage hermitianHeatProjectionLeakage
  rw [crossScaleProjectionLeakage_eq_transitionGram hP hPid
    (hermitianHeatFlow_isHermitian hA u)]
  unfold compressedMatrix compressedSupportLeakageTransition
  simp only [conjTranspose_mul, hC.eq]
  noncomm_ring

/-- The second-projection leakage is the cross-scale Gram product of its own
retained transition channels. -/
theorem finiteCompressionHeatLeakage_eq_transitionGram
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hC : C.IsHermitian)
    (hCid : C * C = C) (u v : ℝ) :
    finiteCompressionHeatLeakage hA P C u v =
      (finiteCompressionLeakageTransition hA P C u)ᴴ *
        finiteCompressionLeakageTransition hA P C v := by
  unfold finiteCompressionHeatLeakage
  exact crossScaleProjectionLeakage_eq_transitionGram hC hCid
    (compressedHermitianHeatFlow_isHermitian hA hP u)

/-- At equal scales the compressed first-projection leakage is positive
semidefinite. -/
theorem compressedSupportHeatLeakage_posSemidef
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hC : C.IsHermitian) (u : ℝ) :
    (compressedSupportHeatLeakage hA P C u u).PosSemidef := by
  unfold compressedSupportHeatLeakage
  exact compressedMatrix_posSemidef hC
    (hermitianHeatProjectionLeakage_posSemidef hA hP hPid u)

/-- At equal scales the second-projection leakage is positive semidefinite. -/
theorem finiteCompressionHeatLeakage_posSemidef
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hC : C.IsHermitian)
    (hCid : C * C = C) (u : ℝ) :
    (finiteCompressionHeatLeakage hA P C u u).PosSemidef := by
  unfold finiteCompressionHeatLeakage
  exact projectionLeakage_posSemidef hC hCid
    (compressedHermitianHeatFlow_isHermitian hA hP u)

/-- Real-trace form of the exact ordered two-stage ledger. -/
theorem rtrace_twoStageCompressedHermitianHeatFlow_mul
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (hCid : C * C = C) (u v : ℝ) :
    rtrace
        (twoStageCompressedHermitianHeatFlow hA P C u *
          twoStageCompressedHermitianHeatFlow hA P C v) =
      rtrace (twoStageCompressedHermitianHeatFlow hA P C (u + v)) -
        rtrace (compressedSupportHeatLeakage hA P C u v) -
        rtrace (finiteCompressionHeatLeakage hA P C u v) := by
  rw [twoStageCompressedHermitianHeatFlow_mul hA hPid hCid]
  simp [rtrace, Matrix.trace_sub, map_sub]

/-- The trace of the compressed first-projection leakage is nonnegative at
equal scales. -/
theorem compressedSupportHeatLeakage_rtrace_nonneg
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hC : C.IsHermitian) (u : ℝ) :
    0 ≤ rtrace (compressedSupportHeatLeakage hA P C u u) :=
  rtrace_nonneg_of_posSemidef
    (compressedSupportHeatLeakage_posSemidef hA hP hPid hC u)

/-- The trace of the second-projection leakage is nonnegative at equal
scales. -/
theorem finiteCompressionHeatLeakage_rtrace_nonneg
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hC : C.IsHermitian)
    (hCid : C * C = C) (u : ℝ) :
    0 ≤ rtrace (finiteCompressionHeatLeakage hA P C u u) :=
  rtrace_nonneg_of_posSemidef
    (finiteCompressionHeatLeakage_posSemidef hA hP hC hCid u)

/-- The trace of the compressed first-projection leakage is exactly its
transition-channel Frobenius mass. -/
theorem compressedSupportHeatLeakage_rtrace_eq_frobSq
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hPid : P * P = P)
    (hC : C.IsHermitian) (u : ℝ) :
    rtrace (compressedSupportHeatLeakage hA P C u u) =
      frobSq (compressedSupportLeakageTransition hA P C u) := by
  rw [compressedSupportHeatLeakage_eq_transitionGram hA hP hPid hC]
  rfl

/-- The trace of the second-projection leakage is exactly its own
transition-channel Frobenius mass. -/
theorem finiteCompressionHeatLeakage_rtrace_eq_frobSq
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hP : P.IsHermitian) (hC : C.IsHermitian)
    (hCid : C * C = C) (u : ℝ) :
    rtrace (finiteCompressionHeatLeakage hA P C u u) =
      frobSq (finiteCompressionLeakageTransition hA P C u) := by
  rw [finiteCompressionHeatLeakage_eq_transitionGram hA hP hC hCid]
  rfl

/-- Equal-scale matrix form of the two-stage information ledger. -/
theorem twoStageCompressedHermitianHeatFlow_sq
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (hCid : C * C = C) (u : ℝ) :
    twoStageCompressedHermitianHeatFlow hA P C u *
        twoStageCompressedHermitianHeatFlow hA P C u =
      twoStageCompressedHermitianHeatFlow hA P C (2 * u) -
        compressedSupportHeatLeakage hA P C u u -
        finiteCompressionHeatLeakage hA P C u u := by
  rw [twoStageCompressedHermitianHeatFlow_mul hA hPid hCid u u]
  congr 3
  ring

/-- Equal-scale trace accounting: the observed squared mass plus both named
leakage masses equals the longer-time twice-compressed heat trace. -/
theorem rtrace_twoStageCompressedHermitianHeatFlow_sq_add_leakages
    {A P C : Matrix n n K} (hA : A.IsHermitian)
    (hPid : P * P = P) (hCid : C * C = C) (u : ℝ) :
    rtrace
          (twoStageCompressedHermitianHeatFlow hA P C u *
            twoStageCompressedHermitianHeatFlow hA P C u) +
        rtrace (compressedSupportHeatLeakage hA P C u u) +
        rtrace (finiteCompressionHeatLeakage hA P C u u) =
      rtrace (twoStageCompressedHermitianHeatFlow hA P C (2 * u)) := by
  have h := rtrace_twoStageCompressedHermitianHeatFlow_mul
    hA hPid hCid u u
  rw [show u + u = 2 * u by ring] at h
  linarith

end

end RiemannGaussian.HermitianRankTrace
