/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorKummerCutoff
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Fourier.ZMod

/-!
# Fixed-modulus Ramanujan and quotient preflight

The divisor form is used explicitly. Its identification with the sum over
primitive additive characters is not assumed here. The finite Fourier
inversion audit is separate and applies to every residue array.
-/

namespace RiemannGaussian.ArithmeticOperatorRamanujanAudit
noncomputable section
open scoped BigOperators

/-- Literal divisor-form Ramanujan coefficient with every gcd endpoint. -/
def ramanujanDivisor (q n : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd q n).divisors, (d : ℤ)*ArithmeticFunction.moebius (q/d)

/-- All moduli are joined before the prime measure is introduced. -/
def code (Q : Finset ℕ) (lambda : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ q ∈ Q, lambda q*(ramanujanDivisor q n : ℂ)

/-- The coefficient shared by every prime coprime to the fixed moduli. -/
def principalCoefficient (Q : Finset ℕ) (lambda : ℕ → ℂ) : ℂ :=
  ∑ q ∈ Q, lambda q*(ArithmeticFunction.moebius q : ℂ)

theorem ramanujanDivisor_of_coprime {q n : ℕ} (h : Nat.Coprime q n) :
    ramanujanDivisor q n = ArithmeticFunction.moebius q := by
  simp [ramanujanDivisor,h.gcd_eq_one]

/-- Fixed-modulus codes see the same scalar on the entire coprime population. -/
theorem code_of_coprime (Q : Finset ℕ) (lambda : ℕ → ℂ) {n : ℕ}
    (h : ∀ q ∈ Q, Nat.Coprime q n) :
    code Q lambda n = principalCoefficient Q lambda := by
  unfold code principalCoefficient
  exact Finset.sum_congr rfl (fun q hq => by rw [ramanujanDivisor_of_coprime (h q hq)])

/-- Pole cancellation at fixed moduli deletes every coprime prime power,
not just its density contribution. -/
theorem code_zero_on_coprime_of_centered (Q : Finset ℕ) (lambda : ℕ → ℂ)
    (hc : principalCoefficient Q lambda = 0) {n : ℕ}
    (h : ∀ q ∈ Q, Nat.Coprime q n) : code Q lambda n = 0 := by
  rw [code_of_coprime Q lambda h,hc]

/-- No scalar principal-channel pole cancellation can preserve a second
source in that same channel. This is algebraic, not an assumed prime bound. -/
theorem principal_density_source_cancellation (Q : Finset ℕ) (lambda : ℕ → ℂ)
    {density : ℂ} (hd : density ≠ 0) (source : ℂ)
    (hc : principalCoefficient Q lambda*density = 0) :
    principalCoefficient Q lambda*source = 0 := by
  exact mul_eq_zero.mpr (Or.inl ((mul_eq_zero.mp hc).resolve_right hd))

/-- A genuine source in the common coprime channel survives exactly when
the principal coefficient survives; finite modulus selection alone cannot
separate it from a nonzero density response. -/
theorem principal_source_nonzero_iff (Q : Finset ℕ) (lambda : ℕ → ℂ)
    {source : ℂ} (hs : source ≠ 0) :
    principalCoefficient Q lambda*source ≠ 0 ↔ principalCoefficient Q lambda ≠ 0 := by
  exact mul_ne_zero_iff_right hs

/-- Exact finite carrier decomposition for arbitrary weights, including
cutoffs, factorial kernels and height phases encoded by w. -/
theorem weighted_code_split (S Q : Finset ℕ) (lambda w : ℕ → ℂ) :
    (∑ n ∈ S, w n*code Q lambda n) =
      principalCoefficient Q lambda*(∑ n ∈ S, w n)+
        ∑ n ∈ S, w n*(code Q lambda n-principalCoefficient Q lambda) := by
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The exact correction is confined to prime powers not coprime to a
chosen modulus. No actual-prime cancellation estimate follows from it. -/
theorem mangoldt_correction_support (Q : Finset ℕ) (lambda : ℕ → ℂ) (n : ℕ)
    (hn : (ArithmeticFunction.vonMangoldt n : ℂ)*
      (code Q lambda n-principalCoefficient Q lambda) ≠ 0) :
    IsPrimePow n ∧ ∃ q ∈ Q, ¬Nat.Coprime q n := by
  have hp : ArithmeticFunction.vonMangoldt n ≠ 0 := by
    intro h
    apply hn
    rw [h,Complex.ofReal_zero,zero_mul]
  refine ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hp,?_⟩
  by_contra hh
  push Not at hh
  have he := code_of_coprime Q lambda hh
  exact hn (by rw [he,sub_self,mul_zero])

/-- Fourier inversion has no prime-specific content: every arbitrary
residue array satisfies the same exact round trip. -/
theorem arbitrary_residue_fourier_roundtrip {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ZMod.dft.symm (ZMod.dft f) = f := ZMod.dft.symm_apply_apply f

end
end RiemannGaussian.ArithmeticOperatorRamanujanAudit
