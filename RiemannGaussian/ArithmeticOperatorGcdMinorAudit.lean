/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorLcmCutoffAudit
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Stronger GCD total-positivity gate fails beyond every fixed head

The literal logarithmic GCD matrix is PSD, but not totally nonnegative.
The ordered rows `p,q` and columns `q,p*q`, for distinct primes `p<q`,
have determinant `-log(p)*log(q)<0`. Such examples exist with every row
and column beyond any given fixed cutoff. This rejects a total-positivity
upgrade of the complete GCD matrix; it says nothing about a specially
restricted packet or a new signed estimate for its remaining geometry.
-/

namespace RiemannGaussian.ArithmeticOperatorGcdMinorAudit
noncomputable section
open ArithmeticOperatorGcdAudit

/-- The genuine actual-Mangoldt GCD matrix, in real coordinates. -/
def actualEntry (m n : ℕ) : ℝ := Real.log (Nat.gcd m n : ℝ)

/-- Ordered two-by-two minor retaining two distinct prime columns. -/
def orderedMinor (p q : ℕ) : ℝ :=
  actualEntry p q*actualEntry q (p*q)-actualEntry p (p*q)*actualEntry q q

theorem actualEntry_eq_mangoldt (m n : ℕ) :
    (actualEntry m n : ℂ) =
      gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) m n :=
  (gcdKernel_mangoldt m n).symm

/-- Incomparable prime columns yield an exact negative minor. No
approximation, twist, or arbitrary-weight substitution is involved. -/
theorem orderedMinor_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    orderedMinor p q = -Real.log p*Real.log q := by
  have hg : Nat.gcd p q = 1 := (hp.coprime_iff_not_dvd.mpr (by
    intro h
    have he := (Nat.dvd_prime hq).mp h
    rcases he with he | he
    · exact hp.ne_one he
    · exact hpq he)).gcd_eq_one
  unfold orderedMinor actualEntry
  simp only [hg, Nat.cast_one, Real.log_one, zero_mul, Nat.gcd_self,
    Nat.gcd_eq_left (dvd_mul_right p q),
    Nat.gcd_eq_left (dvd_mul_left q p), zero_sub, neg_mul]

theorem orderedMinor_negative {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    orderedMinor p q < 0 := by
  rw [orderedMinor_eq hp hq hpq]
  have ha : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hb

/-- No fixed head deletion makes the complete integer GCD matrix
totally nonnegative: all four labels in this negative ordered minor
can be chosen beyond that head. -/
theorem exists_negative_minor_beyond (H : ℕ) :
    ∃ p q : ℕ, H < p ∧ p < q ∧ q < p*q ∧ p.Prime ∧ q.Prime ∧
      orderedMinor p q < 0 := by
  obtain ⟨p, hpH, hp⟩ := Nat.exists_infinite_primes (H+2)
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p+1)
  have hpq : p < q := by omega
  refine ⟨p,q,by omega,hpq,?_,hp,hq,orderedMinor_negative hp hq hpq.ne⟩
  simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos

end
end RiemannGaussian.ArithmeticOperatorGcdMinorAudit
