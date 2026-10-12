/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFullRamanujanAudit

/-!
# Centered prime-modulus codes freely reweight actual prime towers

The full-scale reconstruction is not special to constant coefficients.
Every finite prime-base weight is realized by a principal-centered
Ramanujan code. All proper powers of that base receive the same weight.
With any physical kernel, phase and factorial mask retained, the entire
code is exactly that scalar prime-base reweighting. This is a collapse
theorem for these codes, NOT a statement about nonprincipal characters,
all composite moduli, or a prime-distribution bound.
-/

namespace RiemannGaussian.ArithmeticOperatorRamanujanFreedom
noncomputable section
open Complex ArithmeticOperatorRamanujanAudit ArithmeticOperatorFullRamanujanAudit
open scoped BigOperators

/-- Arbitrary complex weight per prime modulus, including its centering. -/
def weightedCode (Q : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ Q, a p*(((ramanujanDivisor p n : ℂ)+1)/(p : ℂ))

/-- The unit modulus is part of the actual finite code. -/
def weightedCoefficients (Q : Finset ℕ) (a : ℕ → ℂ) (q : ℕ) : ℂ :=
  if q = 1 then ∑ p ∈ Q, a p/(p : ℂ) else a q/(q : ℂ)

theorem weightedCode_eq_indicators {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    (a : ℕ → ℂ) (n : ℕ) :
    weightedCode Q a n = ∑ p ∈ Q, if p ∣ n then a p else 0 := by
  unfold weightedCode
  apply Finset.sum_congr rfl
  intro p hp
  rw [ramanujanDivisor_prime (hQ p hp)]
  split_ifs <;> push_cast <;> simp [(hQ p hp).ne_zero]

/-- Exact finite code, not an infinite Ramanujan expansion. -/
theorem code_eq_weightedCode {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    (a : ℕ → ℂ) (n : ℕ) :
    code (insert 1 Q) (weightedCoefficients Q a) n = weightedCode Q a n := by
  have h1 : 1 ∉ Q := fun hh => (hQ 1 hh).ne_one rfl
  unfold code
  rw [Finset.sum_insert h1]
  simp only [weightedCoefficients, ite_true]
  have hr : ramanujanDivisor 1 n = 1 := by simp [ramanujanDivisor]
  rw [hr]
  simp only [Int.cast_one, mul_one]
  have he : (∑ p ∈ Q,
      (if p = 1 then ∑ p ∈ Q, a p/(p : ℂ) else a p/(p : ℂ))*
        (ramanujanDivisor p n : ℂ)) =
      ∑ p ∈ Q, (a p/(p : ℂ))*(ramanujanDivisor p n : ℂ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_right (hQ p hp).ne_one]
  rw [he, ← Finset.sum_add_distrib]
  unfold weightedCode
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Principal centering imposes no restriction whatsoever on the
arbitrary prime-base profile `a`. This is not pole removal for primes. -/
theorem principalCoefficient_weighted_eq_zero {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (a : ℕ → ℂ) :
    principalCoefficient (insert 1 Q) (weightedCoefficients Q a) = 0 := by
  have h1 : 1 ∉ Q := fun hh => (hQ 1 hh).ne_one rfl
  unfold principalCoefficient
  rw [Finset.sum_insert h1]
  simp only [weightedCoefficients, ite_true, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, mul_one]
  have he : (∑ p ∈ Q,
      (if p = 1 then ∑ p ∈ Q, a p/(p : ℂ) else a p/(p : ℂ))*
        (ArithmeticFunction.moebius p : ℂ)) = -∑ p ∈ Q, a p/(p : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ite_eq_right (hQ p hp).ne_one, ArithmeticFunction.moebius_apply_prime (hQ p hp)]
    simp
  rw [he, add_neg_cancel]

/-- Every proper power keeps exactly its base-prime profile, with no
count or order restriction on the exponent. -/
theorem weightedCode_prime_pow {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    (a : ℕ → ℂ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    weightedCode Q a (p^k) = if p ∈ Q then a p else 0 := by
  rw [weightedCode_eq_indicators hQ]
  have hd {q : ℕ} (hq : q ∈ Q) : q ∣ p^k ↔ q = p := by
    constructor
    · intro hh
      exact ((Nat.dvd_prime hp).mp ((hQ q hq).dvd_of_dvd_pow hh)).resolve_left
        (hQ q hq).ne_one
    · intro he
      rw [he]
      exact dvd_pow_self p hk.ne'
  have he : (∑ q ∈ Q, if q ∣ p^k then a q else 0) =
      ∑ q ∈ Q, if q = p then a q else 0 :=
    Finset.sum_congr rfl (fun q hq => by simp only [hd hq])
  rw [he, Finset.sum_ite_eq']

/-- Explicit surjectivity onto ALL finite prime-tower profiles, despite
zero common coprime coefficient. Hence the code gives no cross-prime
constraint beyond the original profile chosen by the user. -/
theorem exists_centered_code_with_any_profile {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (a : ℕ → ℂ) :
    ∃ lambda : ℕ → ℂ,
      principalCoefficient (insert 1 Q) lambda = 0 ∧
      ∀ p ∈ Q, ∀ k : ℕ, 0 < k → code (insert 1 Q) lambda (p^k) = a p := by
  refine ⟨weightedCoefficients Q a,principalCoefficient_weighted_eq_zero hQ a,?_⟩
  intro p hp k hk
  rw [code_eq_weightedCode hQ, weightedCode_prime_pow hQ a (hQ p hp) hk, ite_eq_left hp]

private theorem minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p^k).minFac = p := by
  have hn : p^k ≠ 1 := by
    have hh := (Nat.le_self_pow hk.ne' p)
    have hp2 := hp.two_le
    omega
  have hm := Nat.minFac_prime hn
  have hd := hm.dvd_of_dvd_pow (Nat.minFac_dvd (p^k))
  exact ((Nat.dvd_prime hp).mp hd).resolve_left hm.ne_one

/-- All actual Mangoldt labels join to ONE prime-base scalar profile.
The identity applies at every size of the chosen finite modulus set. -/
theorem mangoldt_mul_code_eq_profile {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    (a : ℕ → ℂ) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℂ)*weightedCode Q a n =
      (ArithmeticFunction.vonMangoldt n : ℂ)*
        (if n.minFac ∈ Q then a n.minFac else 0) := by
  by_cases hz : ArithmeticFunction.vonMangoldt n = 0
  · simp [hz]
  · obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hz)
    rw [← he, weightedCode_prime_pow hQ a hp hk, minFac_prime_pow hp hk]

/-- Keep any correlated phase, physical support and factorial weight
inside `w`: the entire code still is exactly scalar reweighting, not a
new estimate. No prime powers or cutoff boundaries are removed. -/
theorem native_weighted_eq_scalar (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (a : ℕ → ℂ) (X : ℕ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*
      code (insert 1 Q) (weightedCoefficients Q a) n) =
    ∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.vonMangoldt n : ℂ)*w n*
      (if n.minFac ∈ Q then a n.minFac else 0) := by
  simp_rw [code_eq_weightedCode hQ]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = w n*((ArithmeticFunction.vonMangoldt n : ℂ)*weightedCode Q a n) := by ring
    _ = _ := by rw [mangoldt_mul_code_eq_profile hQ]; ring

end
end RiemannGaussian.ArithmeticOperatorRamanujanFreedom
