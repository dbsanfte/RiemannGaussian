import RiemannGaussian.Hybrid.EtaGeometricDecayVandermonde
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Eventual finite Vandermonde separation of literal eta prefixes

The preceding module constructs a nonsingular finite Vandermonde block for
the limiting raw eta decay modes.  This module transfers that exact finite
separation to the literal arithmetic prefixes.

For a finite zeta-zero window of cardinality `d`, rows are indexed by its
actual zeros and columns by `d` consecutive geometric sample indices
`n, ..., n + d - 1`.  The entry in the row of `rho` is the literal centered
paired-eta prefix of order one below the analytic multiplicity of `rho`, at
the cutoff `(q^(n+j)-1)/2`.

Multiplying row `rho` by `((q : ℂ)^rho)^n` produces a matrix converging
entrywise to its nonzero asymptotic constant times the powers of the raw decay
mode.  The limit is therefore a nonvanishing diagonal matrix times the checked
Vandermonde block.  Continuity of the determinant makes the row-scaled literal
matrix eventually nonsingular, and its exact diagonal factorization transfers
that conclusion back to the unscaled literal prefix matrix.

Thus every finite zeta-zero window has one odd prime base and arbitrarily late
finite blocks of literal eta cutoffs with full row rank.  This is a complete
finite information-separation theorem; it does not yet prove the arithmetic
rank--trace estimate needed to turn that information into an `18/18`
zero-location certificate.
-/

open Complex Filter Topology

namespace RiemannGaussian

noncomputable section

/-- Nonzero complex limit of the geometrically normalized eta prefix one
moment order below the analytic multiplicity. -/
def pairedEtaLowerMomentGeometricLimit
    (rho : NontrivialZetaZero) : ℂ :=
  -((((analyticZetaZeroMultiplicity rho - 1).factorial : ℕ) : ℂ) *
      (rho.val ^ (analyticZetaZeroMultiplicity rho - 1 + 1))⁻¹ / 2)

/-- Literal multiplicity-minus-one centered eta prefix at the `n`th geometric
cutoff for base `q`. -/
def pairedEtaLowerMomentGeometricPrefix
    (q : ℕ) (rho : NontrivialZetaZero) (n : ℕ) : ℂ :=
  pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
    (analyticZetaZeroMultiplicity rho - 1) rho.val
    (etaGeometricOddEndpointCutoff q n)

/-- The lower-moment geometric limit is nonzero at every nontrivial zeta
zero. -/
theorem pairedEtaLowerMomentGeometricLimit_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaLowerMomentGeometricLimit rho ≠ 0 := by
  simpa only [pairedEtaLowerMomentGeometricLimit] using
    pairedEtaLowerMomentGeometricAsymptoticValue_ne_zero rho

/-- After scaling only by the common row factor at index `n`, a fixed shifted
prefix coordinate converges to the lower-moment constant times the matching
power of the raw decay mode. -/
theorem tendsto_pairedEtaLowerMomentGeometricPrefix_rowScaled
    (rho : NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q) (j : ℕ) :
    Tendsto (fun n : ℕ ↦
      (((q : ℂ) ^ rho.val) ^ n) *
        pairedEtaLowerMomentGeometricPrefix q rho (n + j))
      atTop
      (nhds (pairedEtaLowerMomentGeometricLimit rho *
        etaGeometricDecayMode q rho.val ^ j)) := by
  have hbase : ((q : ℂ) ^ rho.val) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast (by omega : q ≠ 0)
  have hshift :=
    (tendsto_etaGeometricCutoff_cpow_mul_pairedEtaLowerMomentCenteredPartialSum
      rho hqOdd hq).comp (tendsto_add_atTop_nat j)
  have hmul := Filter.Tendsto.const_mul
    (etaGeometricDecayMode q rho.val ^ j) hshift
  convert hmul using 1
  · funext n
    unfold pairedEtaLowerMomentGeometricPrefix etaGeometricDecayMode
    simp only [Function.comp_apply]
    have hinv : (((q : ℂ) ^ rho.val) ^ j) *
        ((((q : ℂ) ^ rho.val)⁻¹) ^ j) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero j hbase)]
    calc
      _ = ((((q : ℂ) ^ rho.val) ^ j) *
            ((((q : ℂ) ^ rho.val)⁻¹) ^ j)) *
          ((((q : ℂ) ^ rho.val) ^ n) *
            pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
              (analyticZetaZeroMultiplicity rho - 1) rho.val
              (etaGeometricOddEndpointCutoff q (n + j))) := by
            rw [hinv, one_mul]
      _ = _ := by rw [pow_add]; ring_nf
  · unfold pairedEtaLowerMomentGeometricLimit
    ring_nf

/-- Literal square eta-prefix evaluation matrix on consecutive geometric
sample indices starting at `n`. -/
def pairedEtaLowerMomentGeometricPrefixMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card) ℂ := fun i j ↦
  pairedEtaLowerMomentGeometricPrefix q
    ((etaZeroWindowEquivFin s).symm i) (n + (j : ℕ))

/-- Each literal matrix entry is the centered eta prefix belonging to its
actual zero and shifted geometric cutoff. -/
theorem pairedEtaLowerMomentGeometricPrefixMatrix_apply
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ)
    (i j : Fin s.card) :
    pairedEtaLowerMomentGeometricPrefixMatrix q s n i j =
      pairedEtaLogLaplaceMomentCutoffCenteredPartialSum
        (analyticZetaZeroMultiplicity ((etaZeroWindowEquivFin s).symm i) - 1)
        ((etaZeroWindowEquivFin s).symm i).val
        (etaGeometricOddEndpointCutoff q (n + (j : ℕ))) :=
  rfl

/-- Row-scaled literal prefix matrix used to expose its finite geometric
limit. -/
def pairedEtaLowerMomentGeometricPrefixRowScaledMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    Matrix (Fin s.card) (Fin s.card) ℂ := fun i j ↦
  (((q : ℂ) ^ ((etaZeroWindowEquivFin s).symm i).val.val) ^ n) *
    pairedEtaLowerMomentGeometricPrefixMatrix q s n i j

/-- Finite limiting matrix: a nonzero row constant times the raw-mode
Vandermonde powers. -/
def pairedEtaLowerMomentGeometricLimitMatrix
    (q : ℕ) (s : Finset NontrivialZetaZero) :
    Matrix (Fin s.card) (Fin s.card) ℂ := fun i j ↦
  pairedEtaLowerMomentGeometricLimit ((etaZeroWindowEquivFin s).symm i) *
    etaGeometricDecayMode q
      ((etaZeroWindowEquivFin s).symm i).val ^ (j : ℕ)

/-- The complete row-scaled literal matrix converges entrywise to its finite
geometric limit matrix. -/
theorem tendsto_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix
    (s : Finset NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q) :
    Tendsto (pairedEtaLowerMomentGeometricPrefixRowScaledMatrix q s) atTop
      (nhds (pairedEtaLowerMomentGeometricLimitMatrix q s)) := by
  change Tendsto
    (fun n i j ↦
      pairedEtaLowerMomentGeometricPrefixRowScaledMatrix q s n i j) atTop
    (nhds (fun i j ↦ pairedEtaLowerMomentGeometricLimitMatrix q s i j))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_pairedEtaLowerMomentGeometricPrefix_rowScaled
    ((etaZeroWindowEquivFin s).symm i) hqOdd hq j

/-- The finite limit matrix is exactly its nonzero diagonal row factor times
the raw decay-mode Vandermonde matrix. -/
theorem pairedEtaLowerMomentGeometricLimitMatrix_eq_diagonal_mul
    (q : ℕ) (s : Finset NontrivialZetaZero) :
    pairedEtaLowerMomentGeometricLimitMatrix q s =
      Matrix.diagonal (fun i ↦
        pairedEtaLowerMomentGeometricLimit
          ((etaZeroWindowEquivFin s).symm i)) *
        etaGeometricDecayModeVandermonde q s := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  rfl

/-- Separation of the raw modes makes the complete finite geometric limit
matrix nonsingular. -/
theorem det_pairedEtaLowerMomentGeometricLimitMatrix_ne_zero
    {q : ℕ} {s : Finset NontrivialZetaZero}
    (hinj : Set.InjOn
      (fun rho : NontrivialZetaZero ↦
        etaGeometricDecayMode q rho.val) s) :
    (pairedEtaLowerMomentGeometricLimitMatrix q s).det ≠ 0 := by
  rw [pairedEtaLowerMomentGeometricLimitMatrix_eq_diagonal_mul,
    Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _hi ↦
      pairedEtaLowerMomentGeometricLimit_ne_zero
        ((etaZeroWindowEquivFin s).symm i))
    (det_etaGeometricDecayModeVandermonde_ne_zero hinj)

/-- Determinants of the row-scaled literal prefix matrices converge to the
determinant of the finite geometric limit. -/
theorem tendsto_det_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix
    (s : Finset NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q) :
    Tendsto (fun n ↦
      (pairedEtaLowerMomentGeometricPrefixRowScaledMatrix q s n).det) atTop
      (nhds (pairedEtaLowerMomentGeometricLimitMatrix q s).det) := by
  have hmatrix :=
    tendsto_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix s hqOdd hq
  have hcontinuous : Continuous
      (fun M : Matrix (Fin s.card) (Fin s.card) ℂ ↦ M.det) := by
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp hmatrix

/-- At a separating base, all sufficiently late row-scaled literal prefix
matrices are nonsingular. -/
theorem eventually_det_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix_ne_zero
    (s : Finset NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q)
    (hinj : Set.InjOn
      (fun rho : NontrivialZetaZero ↦
        etaGeometricDecayMode q rho.val) s) :
    ∀ᶠ n in atTop,
      (pairedEtaLowerMomentGeometricPrefixRowScaledMatrix q s n).det ≠ 0 := by
  exact
    (tendsto_det_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix
      s hqOdd hq).eventually
      (eventually_ne_nhds
        (det_pairedEtaLowerMomentGeometricLimitMatrix_ne_zero hinj))

/-- The row-scaled literal matrix is an exact diagonal row scaling of the raw
literal prefix matrix. -/
theorem pairedEtaLowerMomentGeometricPrefixRowScaledMatrix_eq_diagonal_mul
    (q : ℕ) (s : Finset NontrivialZetaZero) (n : ℕ) :
    pairedEtaLowerMomentGeometricPrefixRowScaledMatrix q s n =
      Matrix.diagonal (fun i ↦
        (((q : ℂ) ^ ((etaZeroWindowEquivFin s).symm i).val.val) ^ n)) *
        pairedEtaLowerMomentGeometricPrefixMatrix q s n := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  rfl

/-- At a separating base, all sufficiently late unscaled matrices of literal
finite eta prefixes are nonsingular. -/
theorem eventually_det_pairedEtaLowerMomentGeometricPrefixMatrix_ne_zero
    (s : Finset NontrivialZetaZero) {q : ℕ}
    (hqOdd : Odd q) (hq : 1 < q)
    (hinj : Set.InjOn
      (fun rho : NontrivialZetaZero ↦
        etaGeometricDecayMode q rho.val) s) :
    ∀ᶠ n in atTop,
      (pairedEtaLowerMomentGeometricPrefixMatrix q s n).det ≠ 0 := by
  filter_upwards
    [eventually_det_pairedEtaLowerMomentGeometricPrefixRowScaledMatrix_ne_zero
      s hqOdd hq hinj] with n hn
  intro hzero
  apply hn
  rw [pairedEtaLowerMomentGeometricPrefixRowScaledMatrix_eq_diagonal_mul,
    Matrix.det_mul, hzero, mul_zero]

/-- Every finite zeta-zero window has one odd prime base for which all
sufficiently late square blocks of literal multiplicity-aware eta prefixes
are nonsingular. -/
theorem exists_prime_eventually_det_pairedEtaLowerMomentGeometricPrefixMatrix_ne_zero
    (s : Finset NontrivialZetaZero) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        (pairedEtaLowerMomentGeometricPrefixMatrix q s n).det ≠ 0 := by
  obtain ⟨q, hqprime, hqodd, hq, hinj⟩ :=
    exists_prime_etaGeometricDecayMode_injOn_zetaZeros s
  exact ⟨q, hqprime, hqodd, hq,
    eventually_det_pairedEtaLowerMomentGeometricPrefixMatrix_ne_zero
      s hqodd hq hinj⟩

end

end RiemannGaussian
