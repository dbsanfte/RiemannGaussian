import RiemannGaussian.EtaMoebiusDyadicPhase
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Complete arithmetic periods of the literal eta divisor phases

The phase at divisor `d` is the original eta sign at `floor(M/d)`.
Chinese remainders retain the complete correlation of two odd coprime
divisors; opposite parity gives cancellation over the common period.
These identities are the arithmetic input for growing divisor families.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The product of two literal eta signs depends only on the sum
of their parity arguments, with the eta sign convention retained. -/
theorem pairedEtaDirichletSign_mul_eq_neg_add (m n : ℕ) :
    pairedEtaDirichletSign m * pairedEtaDirichletSign n = -pairedEtaDirichletSign (m + n) := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, hm, hn]

/-- Every complete pair of consecutive literal eta signs cancels. -/
theorem sum_range_pairedEtaDirichletSign_even (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), pairedEtaDirichletSign k) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod]

/-- An odd-length literal eta sign sum keeps its first unmatched
negative sign. -/
theorem sum_range_pairedEtaDirichletSign_odd {n : ℕ} (hn : Odd n) :
    (∑ k ∈ Finset.range n, pairedEtaDirichletSign k) = -1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [Finset.sum_range_succ, sum_range_pairedEtaDirichletSign_even]
  norm_num [pairedEtaDirichletSign, Nat.even_iff]

/-- Coprime residue coordinates enumerate their complete rectangular
grid exactly once; this preserves both phase positions before summation. -/
theorem sum_range_mul_mod_eq_product_of_coprime {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (u v : ℕ → ℤ) :
    (∑ n ∈ Finset.range (a * b), u (n % a) * v (n % b)) =
      (∑ i ∈ Finset.range a, u i) * (∑ j ∈ Finset.range b, v j) := by
  let e : Fin (a * b) ≃ Fin a × Fin b := {
    toFun := fun n ↦ (⟨n.1 % a, Nat.mod_lt _ ha⟩, ⟨n.1 % b, Nat.mod_lt _ hb⟩)
    invFun := fun p ↦ ⟨Nat.chineseRemainder hab p.1.1 p.2.1,
      Nat.chineseRemainder_lt_mul hab _ _ ha.ne' hb.ne'⟩
    left_inv := by
      intro n
      apply Fin.ext
      exact ((Nat.chineseRemainder_modEq_unique hab (a := n.1 % a) (b := n.1 % b)
        (by simp [Nat.ModEq]) (by simp [Nat.ModEq])).eq_of_lt_of_lt n.2
          (Nat.chineseRemainder_lt_mul hab _ _ ha.ne' hb.ne')).symm
    right_inv := by
      intro p
      apply Prod.ext <;> apply Fin.ext
      · exact Eq.trans (show (Nat.chineseRemainder hab p.1.1 p.2.1).1 % a = p.1.1 % a from
          (Nat.chineseRemainder hab p.1.1 p.2.1).2.1) (Nat.mod_eq_of_lt p.1.2)
      · exact Eq.trans (show (Nat.chineseRemainder hab p.1.1 p.2.1).1 % b = p.2.1 % b from
          (Nat.chineseRemainder hab p.1.1 p.2.1).2.2) (Nat.mod_eq_of_lt p.2.2)
  }
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p : Fin a × Fin b, u p.1.1 * v p.2.1 :=
      Equiv.sum_comp e (fun p ↦ u p.1.1 * v p.2.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, Fin.sum_univ_eq_sum_range]

/-- For odd divisors, the product of the two quotient signs equals the
product of the two residue signs; no averaging or absolute value is used here. -/
theorem pairedEtaDirichletSign_div_mul_eq_mod {a b : ℕ} (ha : Odd a) (hb : Odd b) (n : ℕ) :
    pairedEtaDirichletSign (n / a) * pairedEtaDirichletSign (n / b) =
      pairedEtaDirichletSign (n % a) * pairedEtaDirichletSign (n % b) := by
  have hna := congrArg (fun k : ℕ ↦ k % 2) (Nat.mod_add_div n a)
  have hnb := congrArg (fun k : ℕ ↦ k % 2) (Nat.mod_add_div n b)
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.odd_iff.mp ha, Nat.odd_iff.mp hb, one_mul] at hna hnb
  rw [pairedEtaDirichletSign_mul_eq_neg_add, pairedEtaDirichletSign_mul_eq_neg_add]
  have he : (n / a + n / b) % 2 = (n % a + n % b) % 2 := by omega
  simp only [pairedEtaDirichletSign, Nat.even_iff, he]

/-- The complete coprime odd-divisor correlation has the exact
nonzero numerator one over a half-period. -/
theorem sum_range_pairedEtaDivisorParity_coprime_odd {a b : ℕ}
    (ha : Odd a) (hb : Odd b) (hab : a.Coprime b) :
    (∑ n ∈ Finset.range (a * b), pairedEtaDirichletSign (n / a) * pairedEtaDirichletSign (n / b)) = 1 := by
  have hap : 0 < a := by obtain ⟨k, rfl⟩ := ha; omega
  have hbp : 0 < b := by obtain ⟨k, rfl⟩ := hb; omega
  simp_rw [pairedEtaDirichletSign_div_mul_eq_mod ha hb]
  rw [sum_range_mul_mod_eq_product_of_coprime hap hbp hab,
    sum_range_pairedEtaDirichletSign_odd ha, sum_range_pairedEtaDirichletSign_odd hb]
  norm_num

end

end RiemannGaussian
