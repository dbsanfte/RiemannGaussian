import RiemannGaussian.EtaDivisorParityPeriod
import Mathlib.Data.Nat.Periodic

/-!
# The complete gcd covariance of literal eta divisor phases

The exact arithmetic period retains the covariance within each parity
scale as well as cancellation between different scales. The complete
formula is obtained by removing the common divisor and using the proved
Chinese-remainder phase identity.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A full natural-number period has the same sum at every starting
point, retaining the signed values before any norm estimate. -/
theorem sum_range_nat_periodic_shift {α : Type*} [AddCommGroup α] {f : ℕ → α} {P : ℕ}
    (hf : Function.Periodic f P) (A : ℕ) :
    (∑ r ∈ Finset.range P, f (A + r)) = ∑ r ∈ Finset.range P, f r := by
  induction A with
  | zero => simp
  | succ A ih =>
    have h := Finset.sum_range_sub (fun k ↦ f (A + k)) P
    rw [Finset.sum_sub_distrib, hf A, Nat.add_zero, sub_self] at h
    calc
      _ = ∑ r ∈ Finset.range P, f (A + (r + 1)) := by
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        omega
      _ = ∑ r ∈ Finset.range P, f (A + r) := sub_eq_zero.mp h
      _ = _ := ih

/-- Repeating complete periods multiplies their signed sum by the
exact number of periods. -/
theorem sum_range_nat_periodic_mul {α : Type*} [AddCommGroup α] {f : ℕ → α} {P : ℕ}
    (hf : Function.Periodic f P) (k : ℕ) :
    (∑ r ∈ Finset.range (P * k), f r) = k • (∑ r ∈ Finset.range P, f r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, sum_range_nat_periodic_shift hf]
    simp [add_nsmul]

/-- Grouping consecutive equal quotient blocks keeps every natural
floor exactly and supplies their common multiplicity. -/
theorem sum_range_div_blocks {α : Type*} [AddCommGroup α] (f : ℕ → α) {g : ℕ}
    (hg : 0 < g) (n : ℕ) :
    (∑ r ∈ Finset.range (g * n), f (r / g)) = g • (∑ k ∈ Finset.range n, f k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, smul_add]
    congr 1
    calc
      _ = ∑ _r ∈ Finset.range g, f n := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [Nat.add_comm (g * n), Nat.add_mul_div_left r n hg, Nat.div_eq_of_lt (Finset.mem_range.mp hr), zero_add]
      _ = _ := by simp

/-- Addition of parity arguments retains the literal eta sign convention. -/
theorem pairedEtaDirichletSign_add_eq_neg_mul (m n : ℕ) :
    pairedEtaDirichletSign (m + n) = -(pairedEtaDirichletSign m * pairedEtaDirichletSign n) := by
  simpa only [neg_neg] using
    (congrArg (fun z : ℤ ↦ -z) (pairedEtaDirichletSign_mul_eq_neg_add m n)).symm

/-- The raw correlation keeps both literal quotient phases. -/
def pairedEtaDivisorParityProduct (d e M : ℕ) : ℤ :=
  pairedEtaDirichletSign (M / d) * pairedEtaDirichletSign (M / e)

/-- One common half-period multiplies the full raw correlation by
the two divisor parity signs. -/
theorem pairedEtaDivisorParityProduct_halfPeriod {d e : ℕ} (hd : 0 < d) (he : 0 < e) (M : ℕ) :
    pairedEtaDivisorParityProduct d e (M + d * e) =
      pairedEtaDivisorParityProduct d e M * (pairedEtaDirichletSign d * pairedEtaDirichletSign e) := by
  unfold pairedEtaDivisorParityProduct
  rw [Nat.add_mul_div_left M e hd, show d * e = e * d by ring, Nat.add_mul_div_left M d he,
    pairedEtaDirichletSign_add_eq_neg_mul, pairedEtaDirichletSign_add_eq_neg_mul]
  ring

/-- The full raw correlation has an unconditional common arithmetic
period, before the gcd reduction or the parity case split. -/
theorem pairedEtaDivisorParityProduct_periodic {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Function.Periodic (pairedEtaDivisorParityProduct d e) (2 * d * e) := by
  intro M
  unfold pairedEtaDivisorParityProduct
  rw [show 2 * d * e = d * (2 * e) by ring, Nat.add_mul_div_left M (2 * e) hd,
    show d * (2 * e) = e * (2 * d) by ring, Nat.add_mul_div_left M (2 * d) he,
    pairedEtaDirichletSign_add_even _ _ (even_two_mul e),
    pairedEtaDirichletSign_add_even _ _ (even_two_mul d)]

/-- When the reduced divisor signs are opposite, the raw complete
period cancels with its half-period translate. -/
theorem sum_range_pairedEtaDivisorParity_of_opposite_sign {d e : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hsign : pairedEtaDirichletSign d * pairedEtaDirichletSign e = -1) :
    (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) = 0 := by
  rw [show 2 * d * e = d * e + d * e by ring, Finset.sum_range_add]
  have htail : (∑ M ∈ Finset.range (d * e), pairedEtaDivisorParityProduct d e (d * e + M)) =
      -(∑ M ∈ Finset.range (d * e), pairedEtaDivisorParityProduct d e M) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro M hM
    rw [Nat.add_comm, pairedEtaDivisorParityProduct_halfPeriod hd he, hsign]
    ring
  rw [htail, add_neg_cancel]

/-- For coprime odd divisors the complete raw period keeps the exact
positive numerator two. -/
theorem sum_range_pairedEtaDivisorParity_coprime_odd_full {d e : ℕ}
    (hd : Odd d) (he : Odd e) (hde : d.Coprime e) :
    (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) = 2 := by
  have hdp : 0 < d := by obtain ⟨k, rfl⟩ := hd; omega
  have hep : 0 < e := by obtain ⟨k, rfl⟩ := he; omega
  have hsign : pairedEtaDirichletSign d * pairedEtaDirichletSign e = 1 := by
    simp [pairedEtaDirichletSign, Nat.not_even_iff_odd.mpr hd, Nat.not_even_iff_odd.mpr he]
  have hper : Function.Periodic (pairedEtaDivisorParityProduct d e) (d * e) := by
    intro M
    rw [pairedEtaDivisorParityProduct_halfPeriod hdp hep, hsign, mul_one]
  rw [show 2 * d * e = (d * e) * 2 by ring, sum_range_nat_periodic_mul hper]
  have hsum : (∑ M ∈ Finset.range (d * e), pairedEtaDivisorParityProduct d e M) = 1 :=
    sum_range_pairedEtaDivisorParity_coprime_odd hd he hde
  rw [hsum]
  norm_num

/-- The complete coprime period keeps its odd/odd covariance and
cancels precisely when the reduced divisors have opposite parity. -/
theorem sum_range_pairedEtaDivisorParity_coprime {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hde : d.Coprime e) :
    (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) =
      if Odd d ∧ Odd e then 2 else 0 := by
  by_cases hodd : Odd d ∧ Odd e
  · rw [if_pos hodd]
    exact sum_range_pairedEtaDivisorParity_coprime_odd_full hodd.1 hodd.2 hde
  · rw [if_neg hodd]
    apply sum_range_pairedEtaDivisorParity_of_opposite_sign hd he
    by_cases hdo : Odd d
    · have hee : Even e := Nat.not_odd_iff_even.mp (fun heo ↦ hodd ⟨hdo, heo⟩)
      simp [pairedEtaDirichletSign, Nat.not_even_iff_odd.mpr hdo, hee]
    · have hdee : Even d := Nat.not_odd_iff_even.mp hdo
      have heo : Odd e := by
        by_contra h
        have hee : Even e := Nat.not_odd_iff_even.mp h
        have h2 : 2 ∣ Nat.gcd d e := Nat.dvd_gcd
          (Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hdee))
          (Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hee))
        have hgcd : Nat.gcd d e = 1 := hde
        rw [hgcd] at h2
        norm_num at h2
      simp [pairedEtaDirichletSign, hdee, Nat.not_even_iff_odd.mpr heo]

/-- Scaling both divisors repeats each quotient block and repeats
the reduced arithmetic period, preserving the exact square scale factor. -/
theorem sum_range_pairedEtaDivisorParity_common_multiple {g d e : ℕ}
    (hg : 0 < g) (hd : 0 < d) (he : 0 < e) :
    (∑ M ∈ Finset.range (2 * (g * d) * (g * e)), pairedEtaDivisorParityProduct (g * d) (g * e) M) =
      (g : ℤ) ^ 2 * (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) := by
  have hf (M : ℕ) : pairedEtaDivisorParityProduct (g * d) (g * e) M =
      pairedEtaDivisorParityProduct d e (M / g) := by
    simp only [pairedEtaDivisorParityProduct, Nat.div_div_eq_div_mul]
  simp_rw [hf]
  rw [show 2 * (g * d) * (g * e) = g * ((2 * d * e) * g) by ring,
    sum_range_div_blocks _ hg, sum_range_nat_periodic_mul (pairedEtaDivisorParityProduct_periodic hd he)]
  simp only [nsmul_eq_mul]
  ring

/-- The exact full arithmetic covariance of the original eta quotient
phases is a gcd square, with the two reduced parity colours retained. -/
theorem sum_range_pairedEtaDivisorParity_eq_gcd (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) =
      if Odd (d / Nat.gcd d e) ∧ Odd (e / Nat.gcd d e) then 2 * (Nat.gcd d e : ℤ) ^ 2 else 0 := by
  let g := Nat.gcd d e
  let a := d / g
  let b := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have ha : 0 < a := Nat.div_gcd_pos_of_pos_left e hd
  have hb : 0 < b := by
    simpa only [b, g, Nat.gcd_comm] using Nat.div_gcd_pos_of_pos_left d he
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  have hda : g * a = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have heb : g * b = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have hs : (∑ M ∈ Finset.range (2 * d * e), pairedEtaDivisorParityProduct d e M) =
      (g : ℤ) ^ 2 * (if Odd a ∧ Odd b then 2 else 0) := by
    calc
      _ = ∑ M ∈ Finset.range (2 * (g * a) * (g * b)), pairedEtaDivisorParityProduct (g * a) (g * b) M := by
        rw [hda, heb]
      _ = _ := by
        rw [sum_range_pairedEtaDivisorParity_common_multiple hg ha hb,
          sum_range_pairedEtaDivisorParity_coprime ha hb hab]
  change _ = if Odd a ∧ Odd b then 2 * (g : ℤ) ^ 2 else 0
  rw [hs]
  split_ifs <;> ring

end

end RiemannGaussian
