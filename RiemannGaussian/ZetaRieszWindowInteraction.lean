/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowGcd
import RiemannGaussian.ZetaRieszWindowOverlap

/-!
# Prime support of negative window interactions

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszWindowInteraction
noncomputable section
open scoped Classical
open ZetaRieszWindowGram ZetaRieszWindowGcd ZetaRieszWindowOverlap

/-- A surviving negative Mobius interaction has two coprime nonunit
reduced divisors, at least three distinct non-shared primes, and a close
logarithmic ratio. This identifies the remaining arithmetic patterns
without assuming cancellation of their complex amplitudes. -/
theorem negative_overlap_reduced_structure (a L : ℝ) {q d e : ℕ} (hq : 0 < q)
    (hroughd : ∀ p ∈ d.primeFactors, q ≤ p)
    (hroughe : ∀ p ∈ e.primeFactors, q ≤ p)
    (hneg : (ArithmeticFunction.moebius d : ℤ) * ArithmeticFunction.moebius e < 0)
    (hK : clippedOverlap a (Real.log q) (L - Real.log d - Real.log q)
      (L - Real.log e - Real.log q) ≠ 0) :
    let r := d / Nat.gcd d e
    let s := e / Nat.gcd d e
    1 < r ∧ 1 < s ∧ r.Coprime s ∧ Squarefree (r * s) ∧
      3 ≤ ArithmeticFunction.cardDistinctFactors (r * s) ∧
      (ArithmeticFunction.moebius r : ℤ) * ArithmeticFunction.moebius s < 0 ∧
      |Real.log (r : ℝ) - Real.log (s : ℝ)| < Real.log q := by
  dsimp only
  have hd : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    (left_ne_zero_of_mul hneg.ne)
  have he : Squarefree e := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    (right_ne_zero_of_mul hneg.ne)
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have he0 : 0 < e := Nat.pos_of_ne_zero he.ne_zero
  have hne : d ≠ e := by
    intro h
    subst e
    have hh := sq_nonneg (ArithmeticFunction.moebius d : ℤ)
    rw [pow_two] at hh
    linarith
  obtain ⟨hnd, hne'⟩ := nonzero_clippedOverlap_incomparable a L hq hd0 he0 hne hroughd hroughe hK
  have hr := one_lt_reduced_of_not_dvd hd0 hnd
  have hs : 1 < e / Nat.gcd d e := by
    simpa only [Nat.gcd_comm e d] using one_lt_reduced_of_not_dvd he0 hne'
  have hcop := (reduced_divisors_coprime hd he).2.2
  have hrs : Squarefree ((d / Nat.gcd d e) * (e / Nat.gcd d e)) :=
    (Nat.squarefree_mul hcop).mpr
      ⟨hd.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d e)),
        he.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right d e))⟩
  have hneg' : (ArithmeticFunction.moebius (d / Nat.gcd d e) : ℤ) *
      ArithmeticFunction.moebius (e / Nat.gcd d e) < 0 := by
    rw [← moebius_pair_reduce_gcd hd he]
    exact hneg
  have hcount : 3 ≤ ArithmeticFunction.cardDistinctFactors
      ((d / Nat.gcd d e) * (e / Nat.gcd d e)) := by
    rw [(ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hrs.ne_zero).mpr hrs]
    exact negative_moebius_pair_needs_three_factors hr hs hneg'
  refine ⟨hr, hs, hcop, hrs, hcount, hneg', ?_⟩
  have hb := clippedOverlap_le_triangular a (Real.log q)
    (L - Real.log d - Real.log q) (L - Real.log e - Real.log q)
  have hdist : |(L - Real.log d - Real.log q) - (L - Real.log e - Real.log q)| =
      |Real.log d - Real.log e| := by
    rw [show (L - Real.log d - Real.log q) - (L - Real.log e - Real.log q) =
      -(Real.log d - Real.log e) by ring, abs_neg]
  rw [hdist] at hb
  have hpos : 0 < max (Real.log q - |Real.log d - Real.log e|) 0 :=
    (lt_of_le_of_ne (le_max_right _ _) hK.symm).trans_le hb
  have hsep := (lt_max_iff.mp hpos).resolve_right (lt_irrefl 0)
  rw [← log_ratio_reduce_gcd hd0 he0]
  linarith

end
end RiemannGaussian.ZetaRieszWindowInteraction
