/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszTriplePrime

/-!
# The geometry of the complete three-prime coefficient

Keep every pair-product cutoff before compressing the signed Riesz profile.
-/
namespace RiemannGaussian.TripleRieszProfile
noncomputable section
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- With every individual prime below the cutoff and the whole product
above it, the exact signed response is determined by all three pair-product
hinges. All endpoint equalities are included. -/
theorem tripleDifference_eq_pair_hinges {a b c L : ℝ}
    (ha : 0 ≤ a) (haL : a ≤ L) (hbL : b ≤ L) (hcL : c ≤ L)
    (hLs : L ≤ a + b + c) :
    tripleDifference a b c L = a + b + c - 2 * L +
      max 0 (L - a - b) + max 0 (L - a - c) + max 0 (L - b - c) := by
  unfold tripleDifference primePairTent
  rw [max_eq_right (by linarith : 0 ≤ L), max_eq_right (sub_nonneg.mpr haL),
    max_eq_right (sub_nonneg.mpr hbL), max_eq_right (sub_nonneg.mpr hcL),
    max_eq_left (by linarith : L - c - a - b ≤ 0)]
  rw [show L - c - a = L - a - c by ring, show L - c - b = L - b - c by ring]
  ring

/-- The entire ordered three-prime response is the minimum of four
geometric margins: smallest prime,
largest-prime endpoint gap, total lower gap and total midpoint gap.
Its full prime imbalance is retained, rather than replaced by prime count. -/
theorem neg_tripleDifference_eq_min_margins {a b c L : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hcL : c ≤ L) (hLs : L ≤ a + b + c) :
    -tripleDifference a b c L =
      min a (min (L - c) (min (a + b + c - L) (2 * L - (a + b + c)))) := by
  rw [tripleDifference_eq_pair_hinges ha (by linarith) (by linarith) hcL hLs]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The four-margin profile is the exact arithmetic divisor sum of an
actual product of three ordered distinct primes. Its smallest and largest
prime logarithms and both product-cutoff gaps remain explicit. -/
theorem neg_riesz_ordered_three_primes_eq_min_margins {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) {L : ℝ}
    (hrL : Real.log r ≤ L) (hLs : L ≤ Real.log (p * (q * r) : ℕ)) :
    -VaughanLogAverage.riesz L (p * (q * r)) =
      min (Real.log p) (min (L - Real.log r)
        (min (Real.log (p * (q * r) : ℕ) - L) (2 * L - Real.log (p * (q * r) : ℕ)))) := by
  have hlog : Real.log (p * (q * r) : ℕ) = Real.log p + Real.log q + Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hr.ne_zero)]
    ring
  rw [hlog] at hLs ⊢
  rw [riesz_three_primes_eq_difference L hp hq hr hpq.ne (hpq.trans hqr).ne hqr.ne]
  exact neg_tripleDifference_eq_min_margins (Real.log_natCast_nonneg p)
    (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpq.le))
    (Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqr.le)) hrL hLs

end
end RiemannGaussian.TripleRieszProfile
