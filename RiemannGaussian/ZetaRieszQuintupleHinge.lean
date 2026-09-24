/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangle
import RiemannGaussian.ZetaRieszFixedCofactor

/-!
# Exact signs of the proposed five-prime packet

These are identities for actual distinct primes and the literal moving
cutoff. No prime leg or cofactor is completed. The three hinge regions
are evaluated before any phase or absolute value is introduced.
-/

namespace RiemannGaussian.ZetaRieszParityPacket
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszFixedCofactor

/-- The eight subsets of the three remaining small primes. -/
def threeHinge (b c r d : ℝ) : ℝ :=
  max 0 d - max 0 (d-b) - max 0 (d-c) - max 0 (d-r) +
    max 0 (d-b-c) + max 0 (d-b-r) + max 0 (d-c-r) - max 0 (d-b-c-r)

/-- Exact divisor enumeration, including every sign and endpoint. -/
theorem riesz_three (d : ℝ) {b c r : ℕ} (hb : b.Prime) (hc : c.Prime)
    (hr : r.Prime) (hbc : b ≠ c) (hbr : b ≠ r) (hcr : c ≠ r) :
    VaughanLogAverage.riesz d (b*(c*r)) = threeHinge (Real.log b) (Real.log c)
      (Real.log r) d := by
  rw [riesz_two_primes_eq_tent d hb hc hbc
    (fun h => hbr ((Nat.prime_dvd_prime_iff_eq hb hr).mp h))
    (fun h => hcr ((Nat.prime_dvd_prime_iff_eq hc hr).mp h)), hr.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hr,
    Int.cast_one, Int.cast_neg, Nat.cast_one, Real.log_one, sub_zero, one_mul, neg_mul]
  unfold primePairTent threeHinge
  have h₁ : d - Real.log r - Real.log b = d - Real.log b - Real.log r := by ring
  have h₂ : d - Real.log r - Real.log c = d - Real.log c - Real.log r := by ring
  have h₃ : d - Real.log r - Real.log b - Real.log c =
      d - Real.log b - Real.log c - Real.log r := by ring
  rw [h₃, h₁, h₂]
  ring

/-- The first proposed region has the strict negative response b-d. -/
theorem threeHinge_first {b c r d : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) (hcr : c+r ≤ d) (hbr : d ≤ b+r) :
    threeHinge b c r d = b-d := by
  unfold threeHinge
  rw [max_eq_right (by linarith : 0 ≤ d), max_eq_right (by linarith : 0 ≤ d-b),
    max_eq_right (by linarith : 0 ≤ d-c), max_eq_right (by linarith : 0 ≤ d-r),
    max_eq_left (by linarith : d-b-c ≤ 0), max_eq_left (by linarith : d-b-r ≤ 0),
    max_eq_right (by linarith : 0 ≤ d-c-r), max_eq_left (by linarith : d-b-c-r ≤ 0)]
  ring

/-- The middle region has the constant response -r. -/
theorem threeHinge_second {b c r d : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) (hcb : c ≤ b)
    (hbr : b+r ≤ d) (hbc : d ≤ b+c) : threeHinge b c r d = -r := by
  unfold threeHinge
  rw [max_eq_right (by linarith : 0 ≤ d), max_eq_right (by linarith : 0 ≤ d-b),
    max_eq_right (by linarith : 0 ≤ d-c), max_eq_right (by linarith : 0 ≤ d-r),
    max_eq_left (by linarith : d-b-c ≤ 0), max_eq_right (by linarith : 0 ≤ d-b-r),
    max_eq_right (by linarith : 0 ≤ d-c-r), max_eq_left (by linarith : d-b-c-r ≤ 0)]
  ring

/-- The last region is nonpositive, with zero at its closed upper boundary. -/
theorem threeHinge_third {b c r d : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) (hcb : c ≤ b)
    (hbc : b+c ≤ d) (hbcr : d ≤ b+c+r) : threeHinge b c r d = d-b-c-r := by
  unfold threeHinge
  rw [max_eq_right (by linarith : 0 ≤ d), max_eq_right (by linarith : 0 ≤ d-b),
    max_eq_right (by linarith : 0 ≤ d-c), max_eq_right (by linarith : 0 ≤ d-r),
    max_eq_right (by linarith : 0 ≤ d-b-c), max_eq_right (by linarith : 0 ≤ d-b-r),
    max_eq_right (by linarith : 0 ≤ d-c-r), max_eq_left (by linarith : d-b-c-r ≤ 0)]
  ring

/-- The union of the three adjacent hinge regions, using actual logarithms. -/
def HingeRegion (b c r d : ℝ) : Prop :=
  b < d ∧ c+r < d ∧ d ≤ b+c+r

/-- The proposed union really has the required sign. -/
theorem threeHinge_nonpos {b c r d : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) (hcb : c ≤ b)
    (h : HingeRegion b c r d) : threeHinge b c r d ≤ 0 := by
  rcases le_total d (b+r) with h₁ | h₁
  · rw [threeHinge_first hr hrc hcb h.1.le h.2.1.le h₁]
    linarith [h.1]
  · rcases le_total d (b+c) with h₂ | h₂
    · rw [threeHinge_second hr hrc hcb h₁ h₂]; linarith
    · rw [threeHinge_third hr hrc hcb h₂ h.2.2]; linarith [h.2.2]

/-- Literal ordered five-prime geometry. The cutoff is L-log(p), not a
constant multiple of log(n). Saturation is explicit and is not discarded. -/
structure QuintupleGeometry (L : ℝ) (n p a b c r : ℕ) : Prop where
  hp : p.Prime
  ha : a.Prime
  hb : b.Prime
  hc : c.Prime
  hr : r.Prime
  hpa : a < p
  hab : b < a
  hbc : c < b
  hcr : r < c
  factorization : n = p*(a*(b*(c*r)))
  squarefree : Squarefree n
  saturated : Real.log (a*(b*(c*r)) : ℕ) ≤ L
  inactive : L-Real.log p ≤ Real.log a
  region : HingeRegion (Real.log b) (Real.log c) (Real.log r) (L-Real.log p)

private theorem prime_not_dvd_smaller {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q < p) : ¬p ∣ q := fun hd => (ne_of_gt h)
      ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)

/-- All thirty-two original subsets reduce exactly to the eight displayed
ones. The saturation term vanishes by a proved arithmetic hypothesis. -/
theorem quintuple_riesz {L : ℝ} {n p a b c r : ℕ}
    (h : QuintupleGeometry L n p a b c r) :
    VaughanLogAverage.riesz L n =
      -threeHinge (Real.log b) (Real.log c) (Real.log r) (L-Real.log p) := by
  have hpn : ¬p ∣ a*(b*(c*r)) := by
    simp only [h.hp.dvd_mul]
    exact not_or.mpr ⟨prime_not_dvd_smaller h.hp h.ha h.hpa,
      not_or.mpr ⟨prime_not_dvd_smaller h.hp h.hb (h.hab.trans h.hpa),
        not_or.mpr ⟨prime_not_dvd_smaller h.hp h.hc (h.hbc.trans (h.hab.trans h.hpa)),
          prime_not_dvd_smaller h.hp h.hr (h.hcr.trans (h.hbc.trans (h.hab.trans h.hpa)))⟩⟩⟩
  have han : ¬a ∣ b*(c*r) := by
    simp only [h.ha.dvd_mul]
    exact not_or.mpr ⟨prime_not_dvd_smaller h.ha h.hb h.hab,
      not_or.mpr ⟨prime_not_dvd_smaller h.ha h.hc (h.hbc.trans h.hab),
        prime_not_dvd_smaller h.ha h.hr (h.hcr.trans (h.hbc.trans h.hab))⟩⟩
  have hdiv : a*(b*(c*r)) ∣ n := by rw [h.factorization]; exact dvd_mul_left _ _
  have htail : 1 < b*(c*r) := h.hb.one_lt.trans_le
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos h.hc.pos h.hr.pos))
  have hcof : 1 < a*(b*(c*r)) := by nlinarith [h.ha.two_le]
  rw [h.factorization, riesz_prime_mul L h.hp hpn,
    riesz_eq_zero_of_saturated (h.squarefree.squarefree_of_dvd hdiv)
      (by omega) (Nat.not_prime_mul h.ha.ne_one (by omega)) h.saturated,
    riesz_prime_mul (L-Real.log p) h.ha han,
    riesz_eq_zero_of_nonpos (sub_nonpos.mpr h.inactive), sub_zero,
    riesz_three _ h.hb h.hc h.hr (ne_of_gt h.hbc)
      (ne_of_gt (h.hcr.trans h.hbc)) (ne_of_gt h.hcr), zero_sub]

/-- The full original coefficient has the opposite arithmetic sign to
the surviving triple. This is independent of every zero hypothesis. -/
theorem quintuple_coefficient {L : ℝ} {n p a b c r : ℕ}
    (h : QuintupleGeometry L n p a b c r) :
    SquarefreeVaughanLogSource.coefficient L n =
      ((Real.log n / L * threeHinge (Real.log b) (Real.log c)
        (Real.log r) (L-Real.log p) : ℝ) : ℂ) := by
  have hnp : ¬n.Prime := by
    rw [h.factorization]
    apply Nat.not_prime_mul h.hp.ne_one
    have : 1 < a*(b*(c*r)) := h.ha.one_lt.trans_le
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos h.hb.pos (Nat.mul_pos h.hc.pos h.hr.pos)))
    omega
  rw [SquarefreeVaughanLogSource.coefficient, if_pos ⟨h.squarefree, hnp⟩, quintuple_riesz h]
  congr 1
  ring

/-- The sign is nonpositive including the zero-response boundary. -/
theorem quintuple_coefficient_nonpos {L : ℝ} (hL : 0 < L) {n p a b c r : ℕ}
    (h : QuintupleGeometry L n p a b c r) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 := by
  rw [quintuple_coefficient h, Complex.ofReal_re]
  apply mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  apply threeHinge_nonpos (Real.log_natCast_nonneg r)
    (Real.log_le_log (by exact_mod_cast h.hr.pos) (by exact_mod_cast h.hcr.le))
    (Real.log_le_log (by exact_mod_cast h.hc.pos) (by exact_mod_cast h.hbc.le)) h.region

end
end RiemannGaussian.ZetaRieszParityPacket
