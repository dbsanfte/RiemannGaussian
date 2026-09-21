/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeEulerResponse
import RiemannGaussian.ZetaRieszReflectedLinear
import RiemannGaussian.ZetaMoebiusWronskian
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Signed prime-count generating series

The Mobius sign is retained. In particular the z=1 specialization is
1/zeta(s), not the analytic squarefree quotient zeta(s)/zeta(2s).
The Euler product is asserted in its absolute-convergence domain.
-/

namespace RiemannGaussian.PrimeCountEuler
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius LSeries.notation

/-- Actual distinct-prime count, including nonsquarefree integers. -/
def count (n : ℕ) : ℕ := ArithmeticFunction.cardDistinctFactors n

theorem count_eq_card (n : ℕ) : count n = n.primeFactors.card := by
  rw [count, ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
    Nat.toFinset_factors]

/-- The signed coefficient vanishes off squarefree support. -/
def coefficient (z : ℂ) (n : ℕ) : ℂ := (μ n : ℂ)*z^count n

theorem coefficient_mul (z : ℂ) {m n : ℕ} (h : m.Coprime n) :
    coefficient z (m*n) = coefficient z m*coefficient z n := by
  rw [coefficient, coefficient, coefficient, count, ArithmeticFunction.cardDistinctFactors_mul h,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul, pow_add]
  dsimp only [count]
  ring

theorem coefficient_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖coefficient z n‖ ≤ 1 := by
  have hm : ‖(μ n : ℂ)‖ ≤ 1 := by
    norm_cast
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  rw [coefficient, norm_mul, norm_pow]
  exact (mul_le_mul hm (pow_le_one₀ (norm_nonneg z) hz) (by positivity) (by norm_num)).trans_eq
    (one_mul 1)

/-- The genuine complete signed generating series. -/
def generating (z s : ℂ) : ℂ := LSeries (coefficient z) s

theorem summable_generating {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re) :
    LSeriesSummable (coefficient z) s := by
  apply (LSeriesSummable_one_iff.mpr hs).norm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
  simpa only [Pi.one_apply, norm_one] using
    div_le_div_of_nonneg_right (coefficient_norm_le_one hz n) (norm_nonneg ((n : ℂ)^s))

/-- The full signed Euler product, with all prime-count classes coupled. -/
theorem hasProd_generating {z s : ℂ} (hz : ‖z‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1-z*(p : ℂ)^(-s)) (generating z s) := by
  let g := riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  let f : ℕ → ℂ := fun n => coefficient z n*g n
  have hterm (n : ℕ) : f n = LSeries.term (coefficient z) s n := by
    by_cases hn : n = 0
    · simp [f, coefficient, hn, LSeries.term]
    · simp only [f, g, riemannZetaSummandHom, LSeries.term_of_ne_zero hn,
        Complex.cpow_neg, div_eq_mul_inv]
      rfl
  have hf : Summable (fun n => ‖f n‖) := by
    simpa only [hterm] using (summable_generating hz hs).norm
  have h1 : f 1 = 1 := by simp [f, coefficient, count]
  have h0 : f 0 = 0 := by simp [f, coefficient]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m*f n := by
    dsimp only [f]
    rw [coefficient_mul z h, map_mul]
    ring
  have hp := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} h => hm h) hf h0
  have he (p : Nat.Primes) : (∑' k : ℕ, f (p.val^k)) = 1-z*(p : ℂ)^(-s) := by
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [f, coefficient, count, Finset.sum_range_succ, g, riemannZetaSummandHom,
        ArithmeticFunction.moebius_apply_prime p.property,
        ArithmeticFunction.cardDistinctFactors_apply_prime p.property, sub_eq_add_neg]
    · intro k hk
      have hk2 : 2 ≤ k := by simp only [Finset.mem_range] at hk; omega
      have hsf : ¬Squarefree (p.val^k) := by
        rw [Nat.squarefree_pow_iff p.property.ne_one (by omega)]
        omega
      simp [f, coefficient, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  have hp' : HasProd (fun p : Nat.Primes => 1-z*(p : ℂ)^(-s)) (∑' n, f n) := by
    simpa only [he] using hp
  simpa only [hterm, generating, LSeries] using hp'

/-- At z=1 the complete signed series is exactly the reciprocal zeta
function; this identity does not remove a hypothetical zero singularity. -/
theorem generating_one {s : ℂ} (hs : 1 < s.re) :
    generating 1 s = (riemannZeta s)⁻¹ := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  change LSeries (coefficient 1) s = _
  have hc : coefficient 1 = fun n => (μ n : ℂ) := by funext n; simp [coefficient]
  rw [hc]
  apply (mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs))
  simpa only [mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs)] using h

/-- The continued z=1 response has the full opposite divisor order at
each actual nontrivial zero. No arithmetic floor follows from the product. -/
theorem reciprocal_order_at_zero (rho : NontrivialZetaZero) :
    meromorphicOrderAt (fun s => (riemannZeta s)⁻¹) rho.1 =
      -((analyticZetaZeroMultiplicity rho : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt (riemannZeta⁻¹) rho.1 = _
  rw [meromorphicOrderAt_inv,
    meromorphicOrderAt_riemannZeta_nontrivialZero]

end
end RiemannGaussian.PrimeCountEuler
