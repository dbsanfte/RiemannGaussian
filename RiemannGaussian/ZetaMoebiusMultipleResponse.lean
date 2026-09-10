/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusFactorDecay

/-!
# Least-common-multiple response of complete mixed-prime sectors

All multiples of a positive mixed-prime factor have zero complete
von Mangoldt coefficient. Their actual Möbius tail is therefore the
negative finite head. Intersecting each head divisor with the factor
uses its least common multiple, retaining arbitrary prime valuations
without an infinite sum over coprime sectors.
-/

open Complex Filter Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem log_nat_quotient {n d : ℕ} (hd : d ∣ n) (hn : n ≠ 0) :
    Real.log (n / d : ℕ) = Real.log n - Real.log d := by
  have hd0 : d ≠ 0 := fun he ↦ hn (by simpa [he] using hd)
  rw [Nat.cast_div hd (by exact_mod_cast hd0),
    Real.log_div (by exact_mod_cast hn) (by exact_mod_cast hd0)]

/-- A complete non-prime-power coefficient is exactly the negative
finite divisor head. The logarithm at index zero is handled explicitly. -/
theorem zetaMoebiusLogTailCoefficient_eq_neg_prefix (D : ℕ) {n : ℕ}
    (hn1 : n ≠ 1) (hmix : ¬IsPrimePow n) :
    zetaMoebiusLogTailCoefficient D n =
      -(∑ d ∈ Finset.Icc 1 D, if d ∣ n then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) := by
  by_cases hn : n = 0
  · simp [hn, zetaMoebiusLogTailCoefficient]
  have he : n.divisors.filter (fun d ↦ d ≤ D) = (Finset.Icc 1 D).filter (fun d ↦ d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hD⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn), hD⟩, hd⟩
    · tauto
  have hz : (∑ d ∈ n.divisors, (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ)) = 0 := by
    calc
      _ = ∑ d ∈ n.divisors, (μ d : ℂ) * ((Real.log n : ℂ) - (Real.log d : ℂ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [log_nat_quotient (Nat.dvd_of_mem_divisors hd) hn, Complex.ofReal_sub]
      _ = 0 := by
        rw [sum_moebius_log_affine, if_neg hn1, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hmix]
        simp
  have hsplit : zetaMoebiusLogTailCoefficient D n +
      (∑ d ∈ n.divisors, if d ≤ D then (μ d : ℂ) * (Real.log (n / d : ℕ) : ℂ) else 0) = 0 := by
    rw [zetaMoebiusLogTailCoefficient_divisors, ← Finset.sum_add_distrib]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ≤ D <;> simp [hd]
  rw [← Finset.sum_filter, he, Finset.sum_filter] at hsplit
  exact eq_neg_of_add_eq_zero_left hsplit

/-- The original tail on every multiple of `P`, with no restriction on
the coprimality or prime valuations of the quotient. -/
def zetaMoebiusMultipleCoefficient (D P n : ℕ) : ℂ :=
  if P ∣ n then zetaMoebiusLogTailCoefficient D n else 0

/-- One head divisor restricted to all multiples of `P`. -/
def zetaMultipleLogCoefficient (d P n : ℕ) : ℂ :=
  if d ∣ n ∧ P ∣ n then (Real.log (n / d : ℕ) : ℂ) else 0

/-- The complete arithmetic sector is a finite signed sum of exact
divisibility intersections. This keeps every prime valuation. -/
theorem zetaMoebiusMultipleCoefficient_eq_prefix (D : ℕ) {P : ℕ}
    (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) :
    zetaMoebiusMultipleCoefficient D P =
      -(∑ d ∈ Finset.Icc 1 D, (μ d : ℂ) • zetaMultipleLogCoefficient d P) := by
  funext n
  by_cases hPn : P ∣ n
  · have hn1 : n ≠ 1 := fun hn ↦ hP1 (Nat.eq_one_of_dvd_one (hn ▸ hPn))
    have hnprime : ¬IsPrimePow n := fun h ↦ hmix (h.dvd hPn hP1)
    simp only [zetaMoebiusMultipleCoefficient, Pi.neg_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, zetaMultipleLogCoefficient, hPn, and_true, if_true]
    rw [zetaMoebiusLogTailCoefficient_eq_neg_prefix D hn1 hnprime]
    simp only [mul_ite, mul_zero]
  · simp [zetaMoebiusMultipleCoefficient, zetaMultipleLogCoefficient, hPn]

/-- The full real logarithmic offset of the least common multiple. -/
def zetaMultipleLogOffset (d P : ℕ) : ℝ := Real.log (Nat.lcm d P) - Real.log d

/-- Intersecting divisibility conditions is one exact dilation, with
its constant and logarithmic channels retained separately. -/
theorem zetaMultipleLogCoefficient_eq_dilation {d P : ℕ} (hd : 0 < d) (hP : 0 < P) :
    zetaMultipleLogCoefficient d P = zetaDilationCoefficient (Nat.lcm d P)
      (fun n ↦ (Real.log n : ℂ) + (zetaMultipleLogOffset d P : ℂ) * zetaCoprimeCoefficient 1 n) := by
  funext n
  have hL := Nat.lcm_pos hd hP
  by_cases hn : n = 0
  · simp [hn, zetaMultipleLogCoefficient, zetaDilationCoefficient, zetaCoprimeCoefficient]
  by_cases hdiv : Nat.lcm d P ∣ n
  · have hds := Nat.lcm_dvd_iff.mp hdiv
    have hr : n / Nat.lcm d P ≠ 0 := (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) hL).ne'
    rw [zetaMultipleLogCoefficient, if_pos hds, zetaDilationCoefficient, if_pos hdiv]
    have hOne : zetaCoprimeCoefficient 1 (n / Nat.lcm d P) = 1 := by
      simp [zetaCoprimeCoefficient, hr]
    rw [hOne, mul_one, zetaMultipleLogOffset]
    rw [log_nat_quotient hds.1 hn, log_nat_quotient hdiv hn]
    simp only [Complex.ofReal_sub]
    ring
  · have hds : ¬(d ∣ n ∧ P ∣ n) := fun h ↦ hdiv (Nat.lcm_dvd_iff.mpr h)
    simp [zetaMultipleLogCoefficient, zetaDilationCoefficient, hdiv, hds]

/-- Genuine convergence and the exact two-channel value of one
least-common-multiple atom throughout the Euler half-plane. -/
theorem LSeriesHasSum_zetaMultipleLogCoefficient {d P : ℕ} (hd : 0 < d) (hP : 0 < P)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMultipleLogCoefficient d P) s
      (zetaPrimeFeature s (Nat.lcm d P) *
        (-deriv riemannZeta s + (zetaMultipleLogOffset d P : ℂ) * riemannZeta s)) := by
  rw [zetaMultipleLogCoefficient_eq_dilation hd hP]
  have hOne : LSeriesHasSum (zetaCoprimeCoefficient 1) s (riemannZeta s) := by
    simpa [zetaCoprimeEulerFactor, zetaFiniteDirichletSeries, zetaPrimeFeature] using
      LSeriesHasSum_zetaCoprimeCoefficient (P := 1) (by norm_num) hs
  apply LSeriesHasSum_zetaDilationCoefficient (Nat.lcm_pos hd hP) (by simp [zetaCoprimeCoefficient])
  exact (LSeriesHasSum_natLog hs).add (hOne.smul (zetaMultipleLogOffset d P : ℂ))

/-- The signed entire multiplier of `-zeta'` for all multiples. -/
def zetaMoebiusMultipleDerivativeMultiplier (D P : ℕ) (s : ℂ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 D, (μ d : ℂ) * zetaPrimeFeature s (Nat.lcm d P))

/-- The signed entire multiplier of zeta, including the complete
logarithmic displacement of each divisibility intersection. -/
def zetaMoebiusMultipleValueMultiplier (D P : ℕ) (s : ℂ) : ℂ :=
  -(∑ d ∈ Finset.Icc 1 D,
    (μ d : ℂ) * zetaPrimeFeature s (Nat.lcm d P) * (zetaMultipleLogOffset d P : ℂ))

/-- The actual response of the whole multiple sector. -/
def zetaMoebiusMultipleResponse (D P : ℕ) (s : ℂ) : ℂ :=
  zetaMoebiusMultipleDerivativeMultiplier D P s * (-deriv riemannZeta s) +
    zetaMoebiusMultipleValueMultiplier D P s * riemannZeta s

/-- All multiples of a mixed-prime factor have this genuine L-series
response. Both entire multipliers come from actual finite arithmetic sums. -/
theorem LSeriesHasSum_zetaMoebiusMultipleResponse (D : ℕ) {P : ℕ}
    (hP : 0 < P) (hP1 : P ≠ 1) (hmix : ¬IsPrimePow P) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (zetaMoebiusMultipleCoefficient D P) s (zetaMoebiusMultipleResponse D P s) := by
  rw [zetaMoebiusMultipleCoefficient_eq_prefix D hP1 hmix]
  have h := (LSeriesHasSum.sum (S := Finset.Icc 1 D) (fun d hd ↦
    (LSeriesHasSum_zetaMultipleLogCoefficient (Finset.mem_Icc.mp hd).1 hP hs).smul (μ d : ℂ))).neg
  convert h using 1
  unfold zetaMoebiusMultipleResponse zetaMoebiusMultipleDerivativeMultiplier
    zetaMoebiusMultipleValueMultiplier
  simp only [neg_mul, ← neg_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

end
end RiemannGaussian
