/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorRamanujanPayment

/-!
# Exact factorial data are not arbitrary-weight data

The cutoff/divisor operator is invertible on each finite integer prefix.
An arbitrary measure does not reproduce all literal Gamma/factorial
observations: those observations determine every Mangoldt coefficient.
This does not turn leading, source-blind Mellin estimates of those data
into a source-sensitive stability bound for the inverse operator.
-/

namespace RiemannGaussian.ArithmeticOperatorFactorialUniqueness
noncomputable section
open scoped BigOperators

/-- The complete integer-quotient observation, with complex weights. -/
def factorialPrefix (w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, ((N/d : ℕ) : ℂ)*w d

/-- All actual prime powers reproduce the literal factorial. -/
theorem factorialPrefix_mangoldt (N : ℕ) :
    factorialPrefix (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) N =
      (Real.log (N.factorial : ℝ) : ℂ) := by
  have he := SuzukiIntegerCarry.factorialObservation_vonMangoldt N
  unfold SuzukiIntegerCarry.factorialObservation at he
  unfold factorialPrefix
  have hc := congrArg Complex.ofReal he
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast] at hc
  exact hc

/-- Complete finite cutoff data determine every arithmetic column. No
positivity, multiplicativity, exposure or zeta hypothesis is needed. -/
theorem finite_prefix_injective {X : ℕ} {w v : ℕ → ℂ}
    (he : ∀ N ≤ X, factorialPrefix w N = factorialPrefix v N) :
    ∀ n : ℕ, 0 < n → n ≤ X → w n = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnX
    have hsum : (∑ d ∈ Finset.Icc 1 n, ((n/d : ℕ) : ℂ)*(w d-v d)) = w n-v n := by
      rw [Finset.sum_eq_single n]
      · rw [Nat.div_self hn,Nat.cast_one,one_mul]
      · intro d hd hdn
        have hdpos := (Finset.mem_Icc.mp hd).1
        have hdnlt : d < n := lt_of_le_of_ne (Finset.mem_Icc.mp hd).2 hdn
        rw [ih d hdnlt hdpos (le_trans (Finset.mem_Icc.mp hd).2 hnX),sub_self,mul_zero]
      · intro hnot
        exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hn,le_rfl⟩))
    have hz : (∑ d ∈ Finset.Icc 1 n, ((n/d : ℕ) : ℂ)*(w d-v d)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (he n hnX)
    exact sub_eq_zero.mp (hsum.symm.trans hz)

/-- A counterfeit measure satisfying every exact factorial observation
on a prefix is literally the Mangoldt sequence on that prefix. Thus the
Gamma constraints themselves must not be called free Gram identities. -/
theorem mangoldt_unique_on_prefix {X : ℕ} {w : ℕ → ℂ}
    (hGamma : ∀ N ≤ X, factorialPrefix w N = (Real.log (N.factorial : ℝ) : ℂ)) :
    ∀ n : ℕ, 0 < n → n ≤ X → w n = (ArithmeticFunction.vonMangoldt n : ℂ) := by
  apply finite_prefix_injective
  intro N hN
  rw [factorialPrefix_mangoldt]
  exact hGamma N hN

/-- All exact integer Gamma observations eliminate arbitrary-weight
countermodels globally. What is missing is a quantitative signed estimate
using them, not an additional identity determining the literal sequence. -/
theorem mangoldt_unique {w : ℕ → ℂ}
    (hGamma : ∀ N, factorialPrefix w N = (Real.log (N.factorial : ℝ) : ℂ)) :
    ∀ n : ℕ, 0 < n → w n = (ArithmeticFunction.vonMangoldt n : ℂ) := by
  intro n hn
  exact mangoldt_unique_on_prefix (X := n) (fun N _ => hGamma N) n hn le_rfl

end
end RiemannGaussian.ArithmeticOperatorFactorialUniqueness
