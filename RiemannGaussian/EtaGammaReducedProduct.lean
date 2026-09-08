import RiemannGaussian.EtaCoprimeRadicalCutoff

/-!
# Complete reduced product coefficients and exact prime cancellation

The complete coprime product fibre is evaluated before its two zeta
convolutions. Its coefficient is `mu(n) * 2 ^ card(primeFactors n)` on
squarefree integers coprime to the fixed gcd, and zero otherwise. The
two actual finite Dirichlet convolutions have coefficient `1-k` at a
nonexceptional prime power `p^k`, so their first-order prime term is zero.
These are finite arithmetic identities. Absolute convergence in a larger
half-plane and control of the finite rectangular boundary are not assumed.
-/

open Finset Nat
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RiemannGaussian.EtaGammaGcd

noncomputable section

/-- The complete reduced coprime product fibre before either zeta cofactor is summed. -/
def reducedProductCoefficient (g : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ ∑ p ∈ n.divisorsAntidiagonal,
    if p.1.Coprime p.2 ∧ g.Coprime p.1 ∧ g.Coprime p.2 then μ p.1 * μ p.2 else 0,
    by simp⟩

private theorem card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    (n.divisors.card : ℤ) = 2 ^ n.primeFactors.card := by
  have h := ArithmeticFunction.isMultiplicative_zeta.natCast.prodPrimeFactors_one_add_of_squarefree
    (R := ℤ) hn
  have hs : (∑ d ∈ n.divisors, (ζ : ArithmeticFunction ℤ) d) = (n.divisors.card : ℤ) := by
    trans ∑ _d ∈ n.divisors, (1 : ℤ)
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]
    · simp
  rw [hs] at h
  rw [← h]
  trans ∏ _p ∈ n.primeFactors, (2 : ℤ)
  · apply Finset.prod_congr rfl
    intro p hp
    simp only [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne (Nat.prime_of_mem_primeFactors hp).ne_zero, Nat.cast_one]
    norm_num
  · simp

/-- Every complete supported product fibre is the Moebius sign times the number of prime assignments to its two ordered factors. -/
theorem reducedProductCoefficient_eq (g n : ℕ) :
    reducedProductCoefficient g n =
      if Squarefree n ∧ g.Coprime n then μ n * 2 ^ n.primeFactors.card else 0 := by
  change (∑ p ∈ n.divisorsAntidiagonal,
    if p.1.Coprime p.2 ∧ g.Coprime p.1 ∧ g.Coprime p.2 then μ p.1 * μ p.2 else 0) = _
  by_cases hc : Squarefree n ∧ g.Coprime n
  · rw [if_pos hc]
    have he (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) :
        (if p.1.Coprime p.2 ∧ g.Coprime p.1 ∧ g.Coprime p.2 then μ p.1 * μ p.2 else 0) = μ n := by
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hsq : Squarefree (p.1 * p.2) := hprod.symm ▸ hc.1
      have hcop := Nat.coprime_of_squarefree_mul hsq
      have hg : g.Coprime p.1 ∧ g.Coprime p.2 :=
        Nat.coprime_mul_iff_right.mp (hprod.symm ▸ hc.2)
      rw [if_pos ⟨hcop, hg⟩, ← ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        hprod]
    rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
    have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
      rw [← Nat.map_div_right_divisors]
      simp
    rw [hcard, card_divisors_of_squarefree hc.1, mul_comm]
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hpair : p.1.Coprime p.2 ∧ g.Coprime p.1 ∧ g.Coprime p.2
    · rw [if_pos hpair]
      by_contra hmu
      have ha := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (left_ne_zero_of_mul hmu)
      have hb := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (right_ne_zero_of_mul hmu)
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
      apply hc
      rw [← hprod]
      exact ⟨(Nat.squarefree_mul_iff).mpr ⟨hpair.1, ha, hb⟩,
        Nat.coprime_mul_iff_right.mpr hpair.2⟩
    · exact if_neg hpair

/-- The complete product fibre has unit coefficient at one for every fixed gcd. -/
theorem reducedProductCoefficient_one (g : ℕ) : reducedProductCoefficient g 1 = 1 := by
  simp [reducedProductCoefficient_eq]

/-- At a prime not dividing the fixed gcd, only exponents zero and one survive in the complete product coefficient. -/
theorem reducedProductCoefficient_prime_pow {p : ℕ} (hp : p.Prime) {g : ℕ} (hpg : ¬p ∣ g)
    (k : ℕ) :
    reducedProductCoefficient g (p ^ k) =
      (if k = 0 then 1 else 0) - 2 * (if k = 1 then 1 else 0) := by
  by_cases hk0 : k = 0
  · simp [hk0, reducedProductCoefficient_one]
  by_cases hk1 : k = 1
  · have hgp : g.Coprime p := (hp.coprime_iff_not_dvd.mpr hpg).symm
    simp [hk1, reducedProductCoefficient_eq, hp.squarefree, hgp,
      ArithmeticFunction.moebius_apply_prime hp, hp.primeFactors]
  · have hs : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk0]
      tauto
    simp [reducedProductCoefficient_eq, hs, hk0, hk1]

/-- After one complete zeta cofactor, every positive power of a nonexceptional prime has coefficient minus one. -/
theorem zeta_mul_reducedProduct_prime_pow {p : ℕ} (hp : p.Prime) {g : ℕ} (hpg : ¬p ∣ g)
    (k : ℕ) :
    ((ζ : ArithmeticFunction ℤ) * reducedProductCoefficient g) (p ^ k) =
      if k = 0 then 1 else -1 := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp only [reducedProductCoefficient_prime_pow hp hpg, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  by_cases hk : k = 0
  · simp [hk]
  · have hk1 : 1 < k + 1 := by omega
    simp [hk, hk1]

/-- The actual two zeta convolutions of the complete reduced product coefficient, defined coefficientwise without an Euler-product assumption. -/
def reducedZetaSquareCoefficient (g : ℕ) : ArithmeticFunction ℤ :=
  (ζ : ArithmeticFunction ℤ) ^ 2 * reducedProductCoefficient g

/-- The complete finite convolution has coefficient `1-k` at every nonexceptional prime power, including zero at the first prime power. -/
theorem reducedZetaSquareCoefficient_prime_pow {p : ℕ} (hp : p.Prime) {g : ℕ} (hpg : ¬p ∣ g)
    (k : ℕ) : reducedZetaSquareCoefficient g (p ^ k) = 1 - (k : ℤ) := by
  rw [reducedZetaSquareCoefficient, pow_two, mul_assoc, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  simp only [zeta_mul_reducedProduct_prime_pow hp hpg, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, if_false, if_true, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_range]
  ring

/-- Every prime not dividing the fixed gcd cancels exactly after the two zeta convolutions. -/
theorem reducedZetaSquareCoefficient_prime {p : ℕ} (hp : p.Prime) {g : ℕ} (hpg : ¬p ∣ g) :
    reducedZetaSquareCoefficient g p = 0 := by
  simpa using reducedZetaSquareCoefficient_prime_pow hp hpg 1

/-- The first remaining nonexceptional local coefficient is minus one at the prime square. -/
theorem reducedZetaSquareCoefficient_prime_sq {p : ℕ} (hp : p.Prime) {g : ℕ} (hpg : ¬p ∣ g) :
    reducedZetaSquareCoefficient g (p ^ 2) = -1 := by
  simpa using reducedZetaSquareCoefficient_prime_pow hp hpg 2

end

end RiemannGaussian.EtaGammaGcd
