import RiemannGaussian.Hybrid.EtaSignedHeatCoordinateLeakage

/-!
# Higher and cross-scale spectral heat moments for the eta zero window

This module enriches the signed spectral heat carrier without reducing it to
one trace snapshot.  For a finite Hermitian matrix `A`, Lean defines the full
matrix hierarchy

`A^k * exp (-u*A^2)`

through the already checked spectral functional calculus.  Products add both
moment order and heat scale, even orders are positive semidefinite, and the
derivative of the order-`k` heat trace is the negative order-`k+2` heat trace.

For any finite family of orders and scales, Lean then retains the complete
cross-scale moment matrix.  It is a positive-semidefinite Gram matrix, and its
`(i,j)` entry is exactly both

`tr(A^(k_i+k_j) exp (-(u_i+u_j) A^2))`

and the trace product of the two separate matrix-valued moment flows.  This
keeps mixed orders and distinct heat scales as simultaneous measurements.

The entire construction is instantiated on the literal multiplicity-weighted
eta zero-window matrix.  These are genuine additional certificate
observables, but this module does not yet derive their arithmetic values or a
new zeta-zero proportion.
-/

open Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The complete Hermitian heat-moment hierarchy -/

/-- The matrix-valued order-`k` spectral heat flow
`A^k * exp (-u*A^2)`. -/
def hermitianHeatMomentFlow {A : Matrix n n K} (hA : A.IsHermitian)
    (order : ℕ) (u : ℝ) : Matrix n n K :=
  specMap hA (fun x ↦ x ^ order * Real.exp (-u * x ^ 2))

/-- The real trace of the order-`k` spectral heat flow. -/
def hermitianHeatMomentTrace {A : Matrix n n K} (hA : A.IsHermitian)
    (order : ℕ) (u : ℝ) : ℝ :=
  rtrace (hermitianHeatMomentFlow hA order u)

/-- Every order of the spectral heat-moment flow remains Hermitian. -/
theorem hermitianHeatMomentFlow_isHermitian {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    (hermitianHeatMomentFlow hA order u).IsHermitian :=
  specMap_isHermitian hA _

/-- Every even-order spectral heat-moment flow is positive semidefinite. -/
theorem hermitianHeatMomentFlow_even_posSemidef {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    (hermitianHeatMomentFlow hA (2 * order) u).PosSemidef := by
  unfold hermitianHeatMomentFlow
  apply specMap_posSemidef hA
  intro i
  apply mul_nonneg
  · rw [show 2 * order = order * 2 by omega, pow_mul]
    positivity
  · exact (Real.exp_pos _).le

/-- Order zero is the ordinary complete Hermitian heat flow. -/
theorem hermitianHeatMomentFlow_zero {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    hermitianHeatMomentFlow hA 0 u = hermitianHeatFlow hA u := by
  unfold hermitianHeatMomentFlow hermitianHeatFlow
  congr 1
  funext x
  simp

/-- Order one is the sign-bearing Hermitian heat flow. -/
theorem hermitianHeatMomentFlow_one {A : Matrix n n K}
    (hA : A.IsHermitian) (u : ℝ) :
    hermitianHeatMomentFlow hA 1 u = hermitianSignedHeatFlow hA u := by
  unfold hermitianHeatMomentFlow hermitianSignedHeatFlow
  congr 1
  funext x
  simp

/-- Exact product law: multiplying moment flows adds their orders and heat
scales. -/
theorem hermitianHeatMomentFlow_mul {A : Matrix n n K}
    (hA : A.IsHermitian) (order₁ order₂ : ℕ) (u v : ℝ) :
    hermitianHeatMomentFlow hA order₁ u *
        hermitianHeatMomentFlow hA order₂ v =
      hermitianHeatMomentFlow hA (order₁ + order₂) (u + v) := by
  unfold hermitianHeatMomentFlow
  rw [← specMap_mul]
  congr 1
  funext x
  simp only [Pi.mul_apply, pow_add]
  calc
    x ^ order₁ * Real.exp (-u * x ^ 2) *
        (x ^ order₂ * Real.exp (-v * x ^ 2)) =
      (x ^ order₁ * x ^ order₂) *
        (Real.exp (-u * x ^ 2) * Real.exp (-v * x ^ 2)) := by ring
    _ = (x ^ order₁ * x ^ order₂) *
        Real.exp ((-u * x ^ 2) + (-v * x ^ 2)) := by
      rw [Real.exp_add]
    _ = x ^ order₁ * x ^ order₂ * Real.exp (-(u + v) * x ^ 2) := by
      rw [show (-u * x ^ 2) + (-v * x ^ 2) =
        -(u + v) * x ^ 2 by ring]

/-- The order-`k` heat trace is the complete eigenvalue moment sum. -/
theorem hermitianHeatMomentTrace_eq_sum_eigenvalues {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    hermitianHeatMomentTrace hA order u =
      ∑ i, (hA.eigenvalues i) ^ order *
        Real.exp (-u * (hA.eigenvalues i) ^ 2) := by
  unfold hermitianHeatMomentTrace hermitianHeatMomentFlow
  exact rtrace_specMap hA _

/-- A cross-scale matrix-product trace is the combined-order,
combined-scale moment trace. -/
theorem rtrace_hermitianHeatMomentFlow_mul {A : Matrix n n K}
    (hA : A.IsHermitian) (order₁ order₂ : ℕ) (u v : ℝ) :
    rtrace
        (hermitianHeatMomentFlow hA order₁ u *
          hermitianHeatMomentFlow hA order₂ v) =
      hermitianHeatMomentTrace hA (order₁ + order₂) (u + v) := by
  rw [hermitianHeatMomentFlow_mul]
  rfl

/-- Scalar differentiation raises spectral moment order by two and changes
the sign. -/
theorem hasDerivAt_heatMomentScalar (x : ℝ) (order : ℕ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ x ^ order * Real.exp (-v * x ^ 2))
      (-x ^ (order + 2) * Real.exp (-u * x ^ 2)) u := by
  have hinner : HasDerivAt (fun v : ℝ ↦ -v * x ^ 2) (-x ^ 2) u := by
    simpa using (hasDerivAt_id u).neg.mul_const (x ^ 2)
  have hexp := (Real.hasDerivAt_exp (-u * x ^ 2)).comp u hinner
  have h := hexp.const_mul (x ^ order)
  change HasDerivAt
    (fun v : ℝ ↦ x ^ order * Real.exp (-v * x ^ 2))
    (x ^ order * (Real.exp (-u * x ^ 2) * (-x ^ 2))) u at h
  have hderiv :
      x ^ order * (Real.exp (-u * x ^ 2) * (-x ^ 2)) =
        -x ^ (order + 2) * Real.exp (-u * x ^ 2) := by
    rw [pow_add]
    ring
  rwa [hderiv] at h

/-- Differentiating the complete order-`k` heat trace gives the negative
order-`k+2` trace. -/
theorem hasDerivAt_hermitianHeatMomentTrace {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    HasDerivAt (hermitianHeatMomentTrace hA order)
      (-hermitianHeatMomentTrace hA (order + 2) u) u := by
  have hsum : HasDerivAt
      (fun v : ℝ ↦ ∑ i, (hA.eigenvalues i) ^ order *
        Real.exp (-v * (hA.eigenvalues i) ^ 2))
      (∑ i, -(hA.eigenvalues i) ^ (order + 2) *
        Real.exp (-u * (hA.eigenvalues i) ^ 2)) u := by
    exact HasDerivAt.fun_sum fun i _hi ↦
      hasDerivAt_heatMomentScalar (hA.eigenvalues i) order u
  rw [show hermitianHeatMomentTrace hA order =
      (fun v : ℝ ↦ ∑ i, (hA.eigenvalues i) ^ order *
        Real.exp (-v * (hA.eigenvalues i) ^ 2)) by
    funext v
    exact hermitianHeatMomentTrace_eq_sum_eigenvalues hA order v]
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues]
  convert hsum using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-! ## Positive multi-order, multi-scale moment matrices -/

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- The real spectral feature attached to one eigenvalue at a selected moment
order and heat scale. -/
def hermitianHeatMomentFeature {A : Matrix n n K} (hA : A.IsHermitian)
    (order : r → ℕ) (scale : r → ℝ) (a : n) (i : r) : ℝ :=
  (hA.eigenvalues a) ^ (order i) *
    Real.exp (-(scale i) * (hA.eigenvalues a) ^ 2)

/-- The simultaneous Gram matrix of an arbitrary finite family of heat
moment orders and scales. -/
def hermitianHeatMomentGram {A : Matrix n n K} (hA : A.IsHermitian)
    (order : r → ℕ) (scale : r → ℝ) : Matrix r r ℝ :=
  ∑ a, Matrix.vecMulVec
    (hermitianHeatMomentFeature hA order scale a)
    (hermitianHeatMomentFeature hA order scale a)

omit [DecidableEq r] in
/-- Every finite multi-order, multi-scale moment matrix is positive
semidefinite. -/
theorem hermitianHeatMomentGram_posSemidef {A : Matrix n n K}
    (hA : A.IsHermitian) (order : r → ℕ) (scale : r → ℝ) :
    (hermitianHeatMomentGram hA order scale).PosSemidef := by
  classical
  unfold hermitianHeatMomentGram
  induction (Finset.univ : Finset n) using Finset.induction_on with
  | empty =>
      simp
      exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have haPos :
          (Matrix.vecMulVec
            (hermitianHeatMomentFeature hA order scale a)
            (hermitianHeatMomentFeature hA order scale a)).PosSemidef := by
        simpa using Matrix.posSemidef_vecMulVec_self_star
          (hermitianHeatMomentFeature hA order scale a)
      exact haPos.add ih

omit [Fintype r] [DecidableEq r] in
/-- Each moment-Gram entry is the combined-order, combined-scale heat
trace. -/
theorem hermitianHeatMomentGram_apply {A : Matrix n n K}
    (hA : A.IsHermitian) (order : r → ℕ) (scale : r → ℝ)
    (i j : r) :
    hermitianHeatMomentGram hA order scale i j =
      hermitianHeatMomentTrace hA (order i + order j)
        (scale i + scale j) := by
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues]
  unfold hermitianHeatMomentGram hermitianHeatMomentFeature
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [pow_add]
  calc
    hA.eigenvalues a ^ order i * Real.exp (-scale i * hA.eigenvalues a ^ 2) *
        (hA.eigenvalues a ^ order j * Real.exp (-scale j * hA.eigenvalues a ^ 2)) =
      (hA.eigenvalues a ^ order i * hA.eigenvalues a ^ order j) *
        (Real.exp (-scale i * hA.eigenvalues a ^ 2) *
          Real.exp (-scale j * hA.eigenvalues a ^ 2)) := by ring
    _ = (hA.eigenvalues a ^ order i * hA.eigenvalues a ^ order j) *
        Real.exp ((-scale i * hA.eigenvalues a ^ 2) +
          (-scale j * hA.eigenvalues a ^ 2)) := by rw [Real.exp_add]
    _ = hA.eigenvalues a ^ order i * hA.eigenvalues a ^ order j *
        Real.exp (-(scale i + scale j) * hA.eigenvalues a ^ 2) := by
      rw [show (-scale i * hA.eigenvalues a ^ 2) +
        (-scale j * hA.eigenvalues a ^ 2) =
          -(scale i + scale j) * hA.eigenvalues a ^ 2 by ring]

omit [Fintype r] [DecidableEq r] in
/-- Each moment-Gram entry is also the trace product of the two separate
matrix-valued moment flows. -/
theorem hermitianHeatMomentGram_apply_eq_rtrace_mul
    {A : Matrix n n K} (hA : A.IsHermitian)
    (order : r → ℕ) (scale : r → ℝ) (i j : r) :
    hermitianHeatMomentGram hA order scale i j =
      rtrace
        (hermitianHeatMomentFlow hA (order i) (scale i) *
          hermitianHeatMomentFlow hA (order j) (scale j)) := by
  rw [hermitianHeatMomentGram_apply,
    rtrace_hermitianHeatMomentFlow_mul]

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## The hierarchy on the literal eta zero-window matrix -/

/-- The order-`k` matrix-valued spectral heat flow of the literal eta
zero-window matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : ℕ) (u : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  HermitianRankTrace.hermitianHeatMomentFlow
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) order u

/-- The order-`k` spectral heat trace of the literal eta zero-window
matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : ℕ) (u : ℝ) : ℝ :=
  HermitianRankTrace.hermitianHeatMomentTrace
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) order u

/-- Every eta spectral heat-moment flow remains Hermitian. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : ℕ) (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
      cutoff hT order u).IsHermitian :=
  HermitianRankTrace.hermitianHeatMomentFlow_isHermitian
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) order u

/-- Every even-order eta spectral heat-moment flow is positive
semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow_even_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : ℕ) (u : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
      cutoff hT (2 * order) u).PosSemidef :=
  HermitianRankTrace.hermitianHeatMomentFlow_even_posSemidef
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) order u

/-- Products of eta moment flows add order and heat scale exactly. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order₁ order₂ : ℕ) (u v : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
        cutoff hT order₁ u *
      pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
        cutoff hT order₂ v =
      pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
        cutoff hT (order₁ + order₂) (u + v) :=
  HermitianRankTrace.hermitianHeatMomentFlow_mul
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order₁ order₂ u v

/-- The simultaneous multi-order, multi-scale moment Gram matrix of the
literal eta zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
    {d r : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : r → ℕ) (scale : r → ℝ) : Matrix r r ℝ :=
  HermitianRankTrace.hermitianHeatMomentGram
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order scale

/-- Every finite eta multi-order, multi-scale moment matrix is positive
semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_posSemidef
    {d r : Type*} [Fintype d] [DecidableEq d]
    [Fintype r]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : r → ℕ) (scale : r → ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
      cutoff hT order scale).PosSemidef :=
  HermitianRankTrace.hermitianHeatMomentGram_posSemidef
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order scale

/-- Each eta moment-Gram entry is the corresponding combined-order,
combined-scale eta heat trace. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_apply
    {d r : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : r → ℕ) (scale : r → ℝ) (i j : r) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
        cutoff hT order scale i j =
      pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT (order i + order j) (scale i + scale j) :=
  HermitianRankTrace.hermitianHeatMomentGram_apply
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order scale i j

/-- Each eta moment-Gram entry is also the exact trace product of the two
separate eta moment flows. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram_apply_eq_rtrace_mul
    {d r : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : r → ℕ) (scale : r → ℝ) (i j : r) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentGram
        cutoff hT order scale i j =
      HermitianRankTrace.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
            cutoff hT (order i) (scale i) *
          pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentFlow
            cutoff hT (order j) (scale j)) :=
  HermitianRankTrace.hermitianHeatMomentGram_apply_eq_rtrace_mul
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order scale i j

/-- Differentiation raises the eta spectral moment order by two with a
negative sign. -/
theorem hasDerivAt_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (order : ℕ) (u : ℝ) :
    HasDerivAt
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT order)
      (-pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT (order + 2) u) u :=
  HermitianRankTrace.hasDerivAt_hermitianHeatMomentTrace
    (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT)
    order u

end

end RiemannGaussian
