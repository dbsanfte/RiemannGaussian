/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ChebyshevMoebiusCancellation
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.ModEq

/-!
# Signed integer-carry constraints on the actual prime measure

Prime factorization and the additive integer lattice give exact factorial
observations of the literal von Mangoldt sequence. Central binomial carries
then yield a signed all-scale estimate, with a logarithmic total defect and
a reciprocal-size adjacent defect. These are arithmetic theorems, not
claims of a bound for the Suzuki potential or Weil quadratic.
-/

namespace RiemannGaussian.SuzukiIntegerCarry
noncomputable section
open scoped BigOperators

/-- A complete integer-multiple observation of an arithmetic sequence. -/
def factorialObservation (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (N / d : ℕ) * f d

/-- The binary carry at an integer factorial cutoff. Natural subtraction
is exact because the doubled quotient is at least twice the quotient. -/
def carry (N d : ℕ) : ℕ := (2 * N) / d - 2 * (N / d)

/-- All prime powers remain inside the same signed carry observation. -/
def primeCarry (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (2 * N), (carry N d : ℝ) * ArithmeticFunction.vonMangoldt d

/-- The logarithm of the factorial is its exact complete log prefix. -/
theorem logFactorial_eq_log_factorial (N : ℕ) :
    chebyshevLogFactorial N = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp [chebyshevLogFactorial]
  | succ N ih =>
    unfold chebyshevLogFactorial at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- Literal integer-prime mass reproduces every factorial observation,
including all quotient jumps; a smooth density need not satisfy this. -/
theorem factorialObservation_vonMangoldt (N : ℕ) :
    factorialObservation ArithmeticFunction.vonMangoldt N = Real.log (N.factorial : ℝ) := by
  have hconv (n : ℕ) :
      (∑ p ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.1) = Real.log n := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      ArithmeticFunction.vonMangoldt_mul_zeta
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro p hp
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).2]
  have hsum := sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d _ => (ArithmeticFunction.vonMangoldt d : ℂ))
  have hreal : (∑ n ∈ Finset.Icc 1 N, Real.log n) =
      ∑ d ∈ Finset.Icc 1 N, (N / d : ℕ) * ArithmeticFunction.vonMangoldt d := by
    simp_rw [← hconv]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
    exact_mod_cast hsum
  rw [← logFactorial_eq_log_factorial]
  exact hreal.symm

/-- Quotients outside the factorial prefix are zero, so extending its
support to a common larger cutoff is exact. -/
theorem extended_factorialObservation {N M : ℕ} (hNM : N ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, (N / d : ℕ) * ArithmeticFunction.vonMangoldt d) =
      Real.log (N.factorial : ℝ) := by
  rw [← factorialObservation_vonMangoldt]
  unfold factorialObservation
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hNM)
  intro d hdM hd
  have hdN : N < d := by
    have := (Finset.mem_Icc.mp hdM).1
    simp only [Finset.mem_Icc] at hd
    omega
  rw [Nat.div_eq_of_lt hdN, Nat.cast_zero, zero_mul]

/-- Every binary carry is zero or one, without a prime or asymptotic
hypothesis on its denominator. -/
theorem carry_eq_zero_or_one (N d : ℕ) : carry N d = 0 ∨ carry N d = 1 := by
  have hlo := Nat.div_add_div_le_add_div (x := N) (y := N) (z := d)
  have hhi := Nat.add_div_le_div_add_div_add_one N N d
  unfold carry
  simp only [← two_mul] at hlo hhi
  omega

/-- The carry is the parity colour of the exact integer quotient. This
identifies its arithmetic oscillation, including the quotient endpoints. -/
theorem carry_eq_mod_two (N d : ℕ) : carry N d = ((2 * N) / d) % 2 := by
  have hhalf : ((2 * N) / d) / 2 = N / d := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm d 2, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left N (by norm_num : 0 < 2)]
  have h := Nat.mod_add_div ((2 * N) / d) 2
  rw [hhalf] at h
  unfold carry
  omega

/-- Additive carry and exact prime factorization meet at the size of an
integer binomial coefficient. No estimate separates the contributing primes. -/
theorem primeCarry_eq_log_centralBinom (N : ℕ) :
    primeCarry N = Real.log (Nat.centralBinom N : ℝ) := by
  have hlo (d : ℕ) : 2 * (N / d) ≤ (2 * N) / d := by
    simpa only [← two_mul] using Nat.div_add_div_le_add_div (x := N) (y := N) (z := d)
  have he : primeCarry N = Real.log ((2 * N).factorial : ℝ) -
      2 * Real.log (N.factorial : ℝ) := by
    unfold primeCarry carry
    simp_rw [Nat.cast_sub (hlo _), Nat.cast_mul, Nat.cast_ofNat, sub_mul]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [extended_factorialObservation le_rfl,
      extended_factorialObservation (by omega : N ≤ 2 * N)]
  have hf : (Nat.centralBinom N : ℝ) * (N.factorial : ℝ) * (N.factorial : ℝ) =
      ((2 * N).factorial : ℝ) := by
    exact_mod_cast (by simpa only [Nat.centralBinom, ← two_mul] using
      Nat.add_choose_mul_factorial_mul_factorial N N)
  have hlog := congrArg Real.log hf
  rw [Real.log_mul (mul_ne_zero (by exact_mod_cast Nat.centralBinom_ne_zero N)
      (by exact_mod_cast Nat.factorial_ne_zero N)) (by positivity),
    Real.log_mul (by exact_mod_cast (Nat.centralBinom_pos N).ne') (by positivity)] at hlog
  rw [he]
  linarith

/-- Binomial carries give an actual signed prime bound at every integer
scale. Its total defect is only logarithmic, not a PNT-size absolute error. -/
theorem primeCarry_bounds (N : ℕ) :
    (N : ℝ) * Real.log 4 - Real.log (2 * N + 1 : ℕ) ≤ primeCarry N ∧
      primeCarry N ≤ (N : ℝ) * Real.log 4 := by
  have hnat : 4 ^ N ≤ (2 * N + 1) * Nat.centralBinom N := by
    calc
      4 ^ N = ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k := by
        rw [Nat.sum_range_choose, show 4 = 2 ^ 2 by norm_num, ← pow_mul]
      _ ≤ ∑ k ∈ Finset.range (2 * N + 1), Nat.centralBinom N :=
        Finset.sum_le_sum (fun k _ => Nat.choose_le_centralBinom k N)
      _ = _ := by simp
  have hlo := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ N)
    (show (4 : ℝ) ^ N ≤ (2 * N + 1 : ℕ) * (Nat.centralBinom N : ℝ) by exact_mod_cast hnat)
  have hhi := Real.log_le_log (show (0 : ℝ) < Nat.centralBinom N by
      exact_mod_cast Nat.centralBinom_pos N)
    (show (Nat.centralBinom N : ℝ) ≤ (4 : ℝ) ^ N by
      exact_mod_cast Nat.centralBinom_le_four_pow N)
  rw [Real.log_mul (by positivity) (by exact_mod_cast (Nat.centralBinom_pos N).ne'),
    Real.log_pow] at hlo
  rw [Real.log_pow] at hhi
  rw [primeCarry_eq_log_centralBinom]
  constructor <;> linarith

/-- The joined, signed adjacent carry sum is an explicit logarithm.
The positive and negative prime incidences have already been combined. -/
theorem primeCarry_succ_sub (N : ℕ) :
    primeCarry (N + 1) - primeCarry N =
      Real.log 4 - Real.log ((2 * (N : ℝ) + 2) / (2 * N + 1)) := by
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ)) (Nat.succ_mul_centralBinom_succ N)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  rw [Real.log_mul (by positivity) (by exact_mod_cast Nat.centralBinom_ne_zero (N + 1)),
    Real.log_mul (by positivity) (by exact_mod_cast Nat.centralBinom_ne_zero N),
    Real.log_mul (by norm_num) (by positivity)] at h
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hnum : Real.log (2 * (N : ℝ) + 2) = Real.log 2 + Real.log ((N : ℝ) + 1) := by
    rw [show 2 * (N : ℝ) + 2 = 2 * ((N : ℝ) + 1) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [primeCarry_eq_log_centralBinom, primeCarry_eq_log_centralBinom,
    Real.log_div (by positivity) (by positivity), hnum, h4]
  linarith

/-- An unconditional reciprocal-size signed bound for the actual prime
measure across adjacent integer-carry profiles. It is not a Suzuki floor. -/
theorem primeCarry_adjacent_defect_bounds (N : ℕ) :
    1 / (2 * (N : ℝ) + 2) ≤
        Real.log 4 - (primeCarry (N + 1) - primeCarry N) ∧
      Real.log 4 - (primeCarry (N + 1) - primeCarry N) ≤ 1 / (2 * (N : ℝ) + 1) := by
  have hden : 0 < 2 * (N : ℝ) + 1 := by positivity
  have hnum : 0 < 2 * (N : ℝ) + 2 := by positivity
  have hlo := Real.one_sub_inv_le_log_of_pos (div_pos hnum hden)
  have hhi := Real.log_le_sub_one_of_pos (div_pos hnum hden)
  have hleft : 1 - ((2 * (N : ℝ) + 2) / (2 * N + 1))⁻¹ =
      1 / (2 * (N : ℝ) + 2) := by field_simp; ring
  have hright : (2 * (N : ℝ) + 2) / (2 * N + 1) - 1 =
      1 / (2 * (N : ℝ) + 1) := by field_simp; ring
  rw [hleft] at hlo
  rw [hright] at hhi
  rw [primeCarry_succ_sub]
  constructor <;> linarith

/-- Every factorial observation together determines the literal von
Mangoldt sequence. This is stronger than matching smooth mass or PNT scale. -/
theorem eq_vonMangoldt_of_factorialObservations (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (hobs : ∀ N, factorialObservation f N = Real.log (N.factorial : ℝ)) :
    f = ArithmeticFunction.vonMangoldt := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa using hf0
    | succ n =>
      have he := (hobs (n + 1)).trans (factorialObservation_vonMangoldt (n + 1)).symm
      unfold factorialObservation at he
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)] at he
      have hp : (∑ d ∈ Finset.Icc 1 n, ((n + 1) / d : ℕ) * f d) =
          ∑ d ∈ Finset.Icc 1 n, ((n + 1) / d : ℕ) * ArithmeticFunction.vonMangoldt d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [ih d (by have := (Finset.mem_Icc.mp hd).2; omega)]
      rw [hp, Nat.div_self (by omega : 0 < n + 1), Nat.cast_one, one_mul, one_mul] at he
      linarith

/-- A genuinely altered arithmetic sequence must violate at least one
exact integer-factorial observation. Approximate mass agreement does not
satisfy the complete system. -/
theorem exists_factorialObservation_ne_of_ne_vonMangoldt (f : ℕ → ℝ)
    (hf0 : f 0 = 0) (hne : f ≠ ArithmeticFunction.vonMangoldt) :
    ∃ N, factorialObservation f N ≠ Real.log (N.factorial : ℝ) := by
  by_contra h
  push Not at h
  exact hne (eq_vonMangoldt_of_factorialObservations f hf0 h)

/-- No carry remains when the denominator is above the physical doubled
integer cutoff. -/
theorem carry_eq_zero_of_lt {N d : ℕ} (hd : 2 * N < d) : carry N d = 0 := by
  have hNd : N < d := by omega
  simp [carry, Nat.div_eq_of_lt hd, Nat.div_eq_of_lt hNd]

/-- The same literal common support retains the signed prime profile
before taking any norm or dividing its incidences into populations. -/
theorem primeCarry_succ_sub_eq_signed_prime_sum (N : ℕ) :
    primeCarry (N + 1) - primeCarry N =
      ∑ d ∈ Finset.Icc 1 (2 * (N + 1)),
        ((carry (N + 1) d : ℝ) - carry N d) * ArithmeticFunction.vonMangoldt d := by
  have he : (∑ d ∈ Finset.Icc 1 (2 * (N + 1)),
      (carry N d : ℝ) * ArithmeticFunction.vonMangoldt d) = primeCarry N := by
    unfold primeCarry
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    intro d hdM hdN
    have hd : 2 * N < d := by
      have := (Finset.mem_Icc.mp hdM).1
      simp only [Finset.mem_Icc] at hdN
      omega
    rw [carry_eq_zero_of_lt hd, Nat.cast_zero, zero_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, he]
  rfl

/-- A literal signed sum over all prime powers has an unconditional
one-sided interval of reciprocal width. There is no zero hypothesis. -/
theorem signed_prime_carry_bounds (N : ℕ) :
    Real.log 4 - 1 / (2 * (N : ℝ) + 1) ≤
        ∑ d ∈ Finset.Icc 1 (2 * (N + 1)),
          ((carry (N + 1) d : ℝ) - carry N d) * ArithmeticFunction.vonMangoldt d ∧
      (∑ d ∈ Finset.Icc 1 (2 * (N + 1)),
        ((carry (N + 1) d : ℝ) - carry N d) * ArithmeticFunction.vonMangoldt d) ≤
          Real.log 4 - 1 / (2 * (N : ℝ) + 2) := by
  rw [← primeCarry_succ_sub_eq_signed_prime_sum]
  obtain ⟨hlo, hhi⟩ := primeCarry_adjacent_defect_bounds N
  constructor <;> linarith

/-- Complex tests in the integer-cutoff variable preserve the same
joined arithmetic cancellation. This does not insert a new prime phase
inside the carry profile. -/
theorem norm_weighted_joined_carry_defect_le (S : Finset ℕ) (w : ℕ → ℂ) :
    ‖∑ N ∈ S, w N *
      ((Real.log 4 - (primeCarry (N + 1) - primeCarry N) : ℝ) : ℂ)‖ ≤
        ∑ N ∈ S, ‖w N‖ / (2 * (N : ℝ) + 1) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro N _
  obtain ⟨hlo, hhi⟩ := primeCarry_adjacent_defect_bounds N
  have hnonneg : 0 ≤ Real.log 4 - (primeCarry (N + 1) - primeCarry N) :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) + 2)).trans hlo
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    div_eq_mul_inv]
  simpa only [one_div] using mul_le_mul_of_nonneg_left hhi (norm_nonneg (w N))

end
end RiemannGaussian.SuzukiIntegerCarry
