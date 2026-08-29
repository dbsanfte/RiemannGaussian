import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapFinite

/-!
# Euler acceleration of the finite arithmetic eta-gap error

The first finite bound treats the eta tail by its absolute mass.  This module
extracts the cancellation that bound leaves unused.  The difference between
one support summand and its adjacent gap summand is the second difference

`(2n+1)^(-s) - 2(2n+2)^(-s) + (2n+3)^(-s)`.

Its complete series is `2 * pairedEtaCore s - 1`.  Combining this Euler
second-difference series with the exact support--gap telescope gives an exact
finite decomposition: the gap error is `-1/2` times the odd endpoint plus
`1/2` times the remaining second-difference tail.  At a zeta zero the complete
Euler series is exactly `-1`.

This isolates the next quantitative task without assuming it: prove that the
second-difference tail is smaller by one power of the odd endpoint.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The Euler second difference obtained from one support interval and its
adjacent gap interval. -/
def pairedEtaEulerSecondDiffSummand (s : ℂ) (n : ℕ) : ℂ :=
  pairedEtaCoreSummand s n - pairedEtaGapCoreSummand s n

/-- The first `N` Euler second differences. -/
def pairedEtaEulerSecondDiffPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaEulerSecondDiffSummand s n

/-- The complete Euler second-difference series. -/
def pairedEtaEulerSecondDiffCore (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaEulerSecondDiffSummand s n

/-- The support-minus-gap summand is literally a consecutive second
difference. -/
theorem pairedEtaEulerSecondDiffSummand_eq (s : ℂ) (n : ℕ) :
    pairedEtaEulerSecondDiffSummand s n =
      ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        2 * ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ^ (-s) +
          ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
  unfold pairedEtaEulerSecondDiffSummand pairedEtaCoreSummand
    pairedEtaGapCoreSummand
  ring

/-- The Euler second differences are absolutely summable throughout the
positive half-plane. -/
theorem summable_pairedEtaEulerSecondDiffSummand
    {s : ℂ} (hs : 0 < s.re) :
    Summable (pairedEtaEulerSecondDiffSummand s) := by
  unfold pairedEtaEulerSecondDiffSummand
  exact (summable_pairedEtaCoreSummand hs).sub
    (summable_pairedEtaGapCoreSummand hs)

/-- The finite Euler sum is exactly the finite support sum minus the finite
gap sum. -/
theorem pairedEtaEulerSecondDiffPartialSum_eq_sub
    (N : ℕ) (s : ℂ) :
    pairedEtaEulerSecondDiffPartialSum N s =
      pairedEtaCorePartialSum N s - pairedEtaGapCorePartialSum N s := by
  unfold pairedEtaEulerSecondDiffPartialSum
    pairedEtaEulerSecondDiffSummand pairedEtaCorePartialSum
    pairedEtaGapCorePartialSum
  rw [Finset.sum_sub_distrib]

/-- The complete Euler series is exactly twice paired eta minus one. -/
theorem pairedEtaEulerSecondDiffCore_eq_two_mul_sub_one
    {s : ℂ} (hs : 0 < s.re) :
    pairedEtaEulerSecondDiffCore s = 2 * pairedEtaCore s - 1 := by
  have hsupport := summable_pairedEtaCoreSummand hs
  have hgap := summable_pairedEtaGapCoreSummand hs
  unfold pairedEtaEulerSecondDiffCore pairedEtaEulerSecondDiffSummand
  rw [hsupport.tsum_sub hgap]
  change pairedEtaCore s - pairedEtaGapCore s = _
  rw [pairedEtaGapCore_eq_one_sub_pairedEtaCore hs]
  ring

/-- At every nontrivial zeta zero, the complete Euler second-difference
series is exactly `-1`. -/
theorem pairedEtaEulerSecondDiffCore_eq_neg_one_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaEulerSecondDiffCore rho.1 = -1 := by
  have hre := NontrivialZetaZero.zero_lt_re rho
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      hre rho.2.2.2, rho.2.1, mul_zero]
  rw [pairedEtaEulerSecondDiffCore_eq_two_mul_sub_one hre, hcore]
  ring

/-- Solving the finite telescope and Euler difference for the eta support
partial sum. -/
theorem pairedEtaCorePartialSum_eq_half_telescope_add_euler
    (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s =
      (1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) +
        pairedEtaEulerSecondDiffPartialSum N s) / 2 := by
  rw [pairedEtaEulerSecondDiffPartialSum_eq_sub]
  rw [← pairedEtaCorePartialSum_add_gapCorePartialSum N s]
  ring

/-- Solving the same two finite identities for the arithmetic-gap partial
sum. -/
theorem pairedEtaGapCorePartialSum_eq_half_telescope_sub_euler
    (N : ℕ) (s : ℂ) :
    pairedEtaGapCorePartialSum N s =
      (1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        pairedEtaEulerSecondDiffPartialSum N s) / 2 := by
  rw [pairedEtaEulerSecondDiffPartialSum_eq_sub]
  rw [← pairedEtaCorePartialSum_add_gapCorePartialSum N s]
  ring

/-- The finite eta tail is exactly one half of the odd endpoint plus one half
of the unresolved Euler second-difference tail. -/
theorem pairedEtaCore_sub_partialSum_eq_half_endpoint_add_eulerTail
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2 +
        (pairedEtaEulerSecondDiffCore s -
          pairedEtaEulerSecondDiffPartialSum N s) / 2 := by
  rw [pairedEtaCorePartialSum_eq_half_telescope_add_euler,
    pairedEtaEulerSecondDiffCore_eq_two_mul_sub_one hs]
  ring

/-- The finite gap error is exactly negative one half of the odd endpoint
plus one half of the Euler second-difference tail. -/
theorem pairedEtaGapCorePartialSum_sub_core_eq_neg_half_endpoint_add_eulerTail
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaGapCorePartialSum N s - pairedEtaGapCore s =
      -(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2) +
        (pairedEtaEulerSecondDiffCore s -
          pairedEtaEulerSecondDiffPartialSum N s) / 2 := by
  rw [pairedEtaGapCorePartialSum_eq_half_telescope_sub_euler,
    pairedEtaGapCore_eq_one_sub_pairedEtaCore hs,
    pairedEtaEulerSecondDiffCore_eq_two_mul_sub_one hs]
  ring

/-- At a zeta zero, the finite gap error from one has the exact accelerated
endpoint-plus-second-difference-tail decomposition. -/
theorem nontrivialZetaZero_etaGapFiniteError_eq_eulerTail
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaGapCorePartialSum N rho.1 - 1 =
      -(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-rho.1) / 2) +
        (-1 - pairedEtaEulerSecondDiffPartialSum N rho.1) / 2 := by
  have h :=
    pairedEtaGapCorePartialSum_sub_core_eq_neg_half_endpoint_add_eulerTail
      (NontrivialZetaZero.zero_lt_re rho) N
  rw [pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho,
    pairedEtaEulerSecondDiffCore_eq_neg_one_of_nontrivialZetaZero rho] at h
  exact h

/-- A hypothetical off-critical zero forces the accelerated finite error
identity at both complementary exponents, which are distinct. -/
theorem nontrivialZetaZero_offCritical_etaGapEulerTail_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    rho.1.re ≠ 1 - rho.1.re ∧
      ∀ N : ℕ,
        (pairedEtaGapCorePartialSum N rho.1 - 1 =
          -(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-rho.1) / 2) +
            (-1 - pairedEtaEulerSecondDiffPartialSum N rho.1) / 2) ∧
        (pairedEtaGapCorePartialSum N
              (NontrivialZetaZero.conjugatePartner rho).1 - 1 =
          -(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
              (-(NontrivialZetaZero.conjugatePartner rho).1) / 2) +
            (-1 - pairedEtaEulerSecondDiffPartialSum N
              (NontrivialZetaZero.conjugatePartner rho).1) / 2) := by
  constructor
  · intro heq
    apply hoff
    linarith
  · intro N
    exact ⟨nontrivialZetaZero_etaGapFiniteError_eq_eulerTail rho N,
      nontrivialZetaZero_etaGapFiniteError_eq_eulerTail
        (NontrivialZetaZero.conjugatePartner rho) N⟩

end

end RiemannGaussian
