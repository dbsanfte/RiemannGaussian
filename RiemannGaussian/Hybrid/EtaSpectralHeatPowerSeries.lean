import RiemannGaussian.Hybrid.EtaSpectralHeatArithmeticBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The complete matrix-power expansion of eta spectral heat

Positive heat time must not hide which finite arithmetic correlations created
the heat trace.  This module proves an exact convergent power-series carrier
for every Hermitian spectral heat moment:

`H_k(u) = sum_m (-u)^m / m! * rtr(A^(k+2m))`.

Thus the value at one positive scale retains the entire tower of ordinary
matrix-power traces, rather than only the low-order zero-scale jet.  Lean first
proves the scalar exponential series, performs the finite spectral sum without
an unproved interchange, and then rewrites every eigenvalue power sum as the
real trace of the corresponding matrix power.

The final theorems instantiate both the full hierarchy and the ordinary heat
trace on the literal multiplicity-weighted eta zero-window matrix.  This is an
exact information-preserving bridge.  It does not estimate the resulting
power traces, prove a heat crossing, or improve a zeta-zero proportion.
-/

open Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Scalar and finite-spectral power series -/

/-- Every nonnegative integer power sum of the eigenvalues of a Hermitian
matrix is the real trace of the corresponding matrix power, including power
zero. -/
theorem rtrace_pow_eq_sum_eigenvalues {A : Matrix n n K}
    (hA : A.IsHermitian) (order : ℕ) :
    rtrace (A ^ order) = ∑ i, hA.eigenvalues i ^ order := by
  cases order with
  | zero =>
      simp [rtrace, Matrix.trace]
  | succ order =>
      simpa [Nat.succ_eq_add_one] using
        Multiplicity.rtrace_pow_succ hA order

/-- The scalar order-`k` heat moment is the convergent exponential series of
all powers whose parity agrees with `k`. -/
theorem hasSum_heatMomentPowerSeries (x u : ℝ) (order : ℕ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        x ^ (order + 2 * m))
      (x ^ order * Real.exp (-u * x ^ 2)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (-u * x ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at h
  have hm := h.mul_left (x ^ order)
  have hterm (m : ℕ) :
      x ^ order * ((-u * x ^ 2) ^ m / (m.factorial : ℝ)) =
        ((-u) ^ m / (m.factorial : ℝ)) * x ^ (order + 2 * m) := by
    rw [mul_pow]
    rw [show (x ^ 2) ^ m = x ^ (2 * m) by rw [pow_mul]]
    rw [pow_add]
    ring
  simpa only [hterm] using hm

private theorem hasSum_finset_heatMomentPowerSeries
    {A : Matrix n n K} (hA : A.IsHermitian)
    (s : Finset n) (order : ℕ) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ∑ i ∈ s,
        ((-u) ^ m / (m.factorial : ℝ)) *
          hA.eigenvalues i ^ (order + 2 * m))
      (∑ i ∈ s, hA.eigenvalues i ^ order *
        Real.exp (-u * hA.eigenvalues i ^ 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using
        (hasSum_heatMomentPowerSeries (hA.eigenvalues a) u order).add ih

/-! ## Exact matrix-power carrier -/

/-- The complete order-`k` Hermitian heat trace is the sum of its full tower
of ordinary matrix-power traces.  The `HasSum` conclusion records convergence,
not just equality with a totalized infinite sum. -/
theorem hasSum_hermitianHeatMomentTrace_rtrace_powers
    {A : Matrix n n K} (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        rtrace (A ^ (order + 2 * m)))
      (hermitianHeatMomentTrace hA order u) := by
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues]
  have h := hasSum_finset_heatMomentPowerSeries
    hA (Finset.univ : Finset n) order u
  have hterm (m : ℕ) :
      ((-u) ^ m / (m.factorial : ℝ)) *
          rtrace (A ^ (order + 2 * m)) =
        ∑ i, ((-u) ^ m / (m.factorial : ℝ)) *
          hA.eigenvalues i ^ (order + 2 * m) := by
    rw [rtrace_pow_eq_sum_eigenvalues hA]
    rw [Finset.mul_sum]
  simpa only [hterm] using h

/-- Tsum form of the complete matrix-power expansion of a Hermitian spectral
heat moment. -/
theorem hermitianHeatMomentTrace_eq_tsum_rtrace_powers
    {A : Matrix n n K} (hA : A.IsHermitian) (order : ℕ) (u : ℝ) :
    hermitianHeatMomentTrace hA order u =
      ∑' m : ℕ, ((-u) ^ m / (m.factorial : ℝ)) *
        rtrace (A ^ (order + 2 * m)) :=
  (hasSum_hermitianHeatMomentTrace_rtrace_powers hA order u).tsum_eq.symm

/-- The ordinary Hermitian heat trace retains exactly every even matrix-power
trace. -/
theorem hermitianHeatMomentTrace_zero_eq_tsum_even_rtrace_powers
    {A : Matrix n n K} (hA : A.IsHermitian) (u : ℝ) :
    hermitianHeatMomentTrace hA 0 u =
      ∑' m : ℕ, ((-u) ^ m / (m.factorial : ℝ)) *
        rtrace (A ^ (2 * m)) := by
  simpa only [zero_add] using
    hermitianHeatMomentTrace_eq_tsum_rtrace_powers hA 0 u

end


end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

/-! ## Literal eta zero-window instantiation -/

/-- The literal eta order-`k` spectral heat trace is the convergent series of
all parity-compatible powers of its genuine multiplicity-weighted zero-window
matrix. -/
theorem hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_rtrace_powers
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (order : ℕ) (u : ℝ) :
    HasSum
      (fun m : ℕ ↦ ((-u) ^ m / (m.factorial : ℝ)) *
        HermitianRankTrace.rtrace
          ((pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) ^
            (order + 2 * m)))
      (pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT order u) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
  exact
    HermitianRankTrace.hasSum_hermitianHeatMomentTrace_rtrace_powers
      (pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian cutoff hT) order u

/-- Tsum form of the complete matrix-power expansion for every literal eta
spectral heat moment. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_eq_tsum_rtrace_powers
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (order : ℕ) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace
        cutoff hT order u =
      ∑' m : ℕ, ((-u) ^ m / (m.factorial : ℝ)) *
        HermitianRankTrace.rtrace
          ((pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) ^
            (order + 2 * m)) :=
  (hasSum_pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_rtrace_powers
    cutoff hT order u).tsum_eq.symm

/-- The ordinary literal eta heat trace retains exactly the complete tower of
even powers of its multiplicity-weighted zero-window matrix. -/
theorem pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_zero_eq_tsum_even_rtrace_powers
    {d : Type*} [Fintype d] [DecidableEq d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace cutoff hT 0 u =
      ∑' m : ℕ, ((-u) ^ m / (m.factorial : ℝ)) *
        HermitianRankTrace.rtrace
          ((pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) ^ (2 * m)) := by
  simpa only [zero_add] using
    pairedEtaTopPrefixFiniteZeroWindowSpectralHeatMomentTrace_eq_tsum_rtrace_powers
      cutoff hT 0 u

end


end RiemannGaussian
