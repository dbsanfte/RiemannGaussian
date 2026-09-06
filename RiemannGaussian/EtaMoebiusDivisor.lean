import RiemannGaussian.EtaCurrentReturnSharpGrowth
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact finite Möbius cancellation of the eta Dirichlet coefficients

Classical Möbius inversion is applied to the actual odd-even coefficients
of paired eta. The divisor convolution is supported exactly at one and
two. All sums here are finite, and every complex Dirichlet phase is kept.
The next interface groups these coefficients into the original completed
eta prefixes and their genuine zero tails.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual odd-positive, even-negative Dirichlet coefficient of eta. -/
def pairedEtaDirichletSign (n : ℕ) : ℤ := if Even n then -1 else 1

/-- The two exact coefficients left by Möbius inversion of eta. -/
def pairedEtaDyadicDirichletSource (n : ℕ) : ℂ :=
  (if n = 1 then 1 else 0) - 2 * (if n = 2 then 1 else 0)

/-- Summing the two supported source coefficients over the divisors
recovers the literal eta sign at every positive integer. -/
theorem sum_divisors_pairedEtaDyadicDirichletSource (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, pairedEtaDyadicDirichletSource d) = (pairedEtaDirichletSign n : ℂ) := by
  unfold pairedEtaDyadicDirichletSource
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Nat.mem_divisors, one_dvd]
  by_cases he : Even n
  · have hd : 2 ∣ n := even_iff_two_dvd.mp he
    norm_num [pairedEtaDirichletSign, he, hd, hn.ne']
  · have hd : ¬ 2 ∣ n := fun h ↦ he (even_iff_two_dvd.mpr h)
    simp [pairedEtaDirichletSign, he, hd, hn.ne']

/-- The full signed divisor convolution collapses to the two dyadic
source coefficients by Mathlib's classical Möbius inversion theorem. -/
theorem sum_moebius_mul_pairedEtaDirichletSign (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℂ) * (pairedEtaDirichletSign p.2 : ℂ)) =
      pairedEtaDyadicDirichletSource n :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp sum_divisors_pairedEtaDyadicDirichletSource) n hn

/-- The divisor cancellation retains both exact complex Dirichlet
phases and their common arithmetic product. -/
theorem sum_moebius_mul_pairedEtaDirichletTerm (s : ℂ) (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ n.divisorsAntidiagonal, (μ p.1 : ℂ) * (p.1 : ℂ) ^ (-s) *
      ((pairedEtaDirichletSign p.2 : ℂ) * (p.2 : ℂ) ^ (-s))) =
        pairedEtaDyadicDirichletSource n * (n : ℂ) ^ (-s) := by
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        ((μ p.1 : ℂ) * (pairedEtaDirichletSign p.2 : ℂ)) * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← hp', Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      ring
    _ = _ := by rw [← Finset.sum_mul, sum_moebius_mul_pairedEtaDirichletSign n hn]

/-- At every finite integer cutoff at least two, the complete
Möbius-weighted eta divisor sum is the same exact dyadic factor. -/
theorem sum_Icc_moebius_mul_pairedEtaDirichletTerm (s : ℂ) {M : ℕ} (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, ∑ p ∈ n.divisorsAntidiagonal,
      (μ p.1 : ℂ) * (p.1 : ℂ) ^ (-s) * ((pairedEtaDirichletSign p.2 : ℂ) * (p.2 : ℂ) ^ (-s))) =
        1 - 2 * (2 : ℂ) ^ (-s) := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, pairedEtaDyadicDirichletSource n * (n : ℂ) ^ (-s) :=
      Finset.sum_congr rfl (fun n hn ↦ sum_moebius_mul_pairedEtaDirichletTerm s n (Finset.mem_Icc.mp hn).1)
    _ = _ := by
      simp only [pairedEtaDyadicDirichletSource, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
      simp only [mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq', Finset.mem_Icc, hM, show 1 ≤ M by omega]

end

end RiemannGaussian
