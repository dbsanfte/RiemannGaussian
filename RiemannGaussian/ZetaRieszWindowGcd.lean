/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowUnitDeletion

/-!
# Shared primes in signed window correlations

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszWindowGcd
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open ZetaRieszWholeWindow

/-- Removing the shared prime factors leaves a coprime numerator and
denominator; each is also coprime to the full opposite divisor. -/
theorem reduced_divisors_coprime {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    (d / Nat.gcd d e).Coprime e ∧ (e / Nat.gcd d e).Coprime d ∧
      (d / Nat.gcd d e).Coprime (e / Nat.gcd d e) := by
  have hde := Nat.coprime_div_gcd_of_squarefree hd he.ne_zero
  have hed := Nat.coprime_div_gcd_of_squarefree he hd.ne_zero
  rw [Nat.gcd_comm e d] at hed
  exact ⟨hde, hed, hde.of_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right d e))⟩

/-- Common prime factors contribute a Mobius square equal to one.
The surviving sign is exactly the parity of the reduced coprime ratio. -/
theorem moebius_pair_reduce_gcd {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    (ArithmeticFunction.moebius d : ℤ) * ArithmeticFunction.moebius e =
      ArithmeticFunction.moebius (d / Nat.gcd d e) *
        ArithmeticFunction.moebius (e / Nat.gcd d e) := by
  let g := Nat.gcd d e
  have hgd : g * (d / g) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have hge : g * (e / g) = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have hcopd : g.Coprime (d / g) := Nat.coprime_of_squarefree_mul (by rw [hgd]; exact hd)
  have hcope : g.Coprime (e / g) := Nat.coprime_of_squarefree_mul (by rw [hge]; exact he)
  have hmd : ArithmeticFunction.moebius d =
      ArithmeticFunction.moebius g * ArithmeticFunction.moebius (d / g) := by
    calc
      _ = ArithmeticFunction.moebius (g * (d / g)) := congrArg _ hgd.symm
      _ = _ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopd
  have hme : ArithmeticFunction.moebius e =
      ArithmeticFunction.moebius g * ArithmeticFunction.moebius (e / g) := by
    calc
      _ = ArithmeticFunction.moebius (g * (e / g)) := congrArg _ hge.symm
      _ = _ := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcope
  have hgs : (ArithmeticFunction.moebius g : ℤ) ^ 2 = 1 :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hd.squarefree_of_dvd (Nat.gcd_dvd_left d e))
  calc
    _ = (ArithmeticFunction.moebius g : ℤ) ^ 2 *
        (ArithmeticFunction.moebius (d / g) * ArithmeticFunction.moebius (e / g)) := by
      rw [hmd, hme]
      ring
    _ = _ := by rw [hgs, one_mul]

/-- Each divisor retains its exact common-factor logarithm and
its positive reduced quotient. -/
theorem log_gcd_quotients {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Real.log d = Real.log (Nat.gcd d e) + Real.log ((d / Nat.gcd d e : ℕ) : ℝ) ∧
      Real.log e = Real.log (Nat.gcd d e) + Real.log ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
  have hqd : 0 < d / Nat.gcd d e := Nat.div_pos
    (Nat.le_of_dvd hd (Nat.gcd_dvd_left d e)) hg
  have hqe : 0 < e / Nat.gcd d e := Nat.div_pos
    (Nat.le_of_dvd he (Nat.gcd_dvd_right d e)) hg
  have hg0 : (Nat.gcd d e : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqd0 : ((d / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqd.ne'
  have hqe0 : ((e / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hqe.ne'
  constructor
  · calc
      _ = Real.log ((Nat.gcd d e : ℝ) * (d / Nat.gcd d e : ℕ)) := by
        congr 1
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)).symm
      _ = _ := Real.log_mul hg0 hqd0
  · calc
      _ = Real.log ((Nat.gcd d e : ℝ) * (e / Nat.gcd d e : ℕ)) := by
        congr 1
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
      _ = _ := Real.log_mul hg0 hqe0

/-- Logarithmic separation depends only on the reduced coprime ratio,
although the physical cutoff still remembers the shared prime factor. -/
theorem log_ratio_reduce_gcd {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    Real.log d - Real.log e =
      Real.log ((d / Nat.gcd d e : ℕ) : ℝ) - Real.log ((e / Nat.gcd d e : ℕ) : ℝ) := by
  obtain ⟨h1, h2⟩ := log_gcd_quotients hd he
  linarith

/-- Factoring a divisor shifts the lower window cutoff by exactly
the common-factor logarithm. The original prime labels do not change. -/
theorem primeWindowLower_factor (L : ℝ) (p q : ℕ → ℕ) (n : ℕ) {g d : ℕ}
    (hg : 0 < g) (hd : 0 < d) :
    primeWindowLower L p q ⟨n, g * d⟩ =
      primeWindowLower (L - Real.log g) p q ⟨n, d⟩ := by
  unfold primeWindowLower
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hd.ne')]
  ring

/-- The upper edge has the same displacement. Dropping the common
factor would move the physical cutoff and lose exactness. -/
theorem primeWindowUpper_factor (L : ℝ) (p : ℕ → ℕ) (n : ℕ) {g d : ℕ}
    (hg : 0 < g) (hd : 0 < d) :
    primeWindowUpper L p ⟨n, g * d⟩ =
      primeWindowUpper (L - Real.log g) p ⟨n, d⟩ := by
  unfold primeWindowUpper
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hd.ne')]
  ring

/-- The full complex coefficient pair loses exactly the common
Mobius square. Original integer amplitudes, filter phases and their
normalization length remain unchanged. -/
theorem primeWindowCoefficient_pair_reduce_gcd (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) (p : ℕ → ℕ) (n m : ℕ) {d e : ℕ}
    (hd : Squarefree d) (he : Squarefree e) :
    primeWindowCoefficient L P N t p ⟨n, d⟩ *
        conj (primeWindowCoefficient L P N t p ⟨m, e⟩) =
      primeWindowCoefficient L P N t p ⟨n, d / Nat.gcd d e⟩ *
        conj (primeWindowCoefficient L P N t p ⟨m, e / Nat.gcd d e⟩) := by
  have hc : ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      ((ArithmeticFunction.moebius e : ℤ) : ℂ) =
      ((ArithmeticFunction.moebius (d / Nat.gcd d e) : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius (e / Nat.gcd d e) : ℤ) : ℂ) := by
    exact_mod_cast moebius_pair_reduce_gcd hd he
  let A := (Real.log (p n) : ℂ) * ZetaArithmeticBandCorrelation.bandAmplitude L P N t n
  let B := (Real.log (p m) : ℂ) * ZetaArithmeticBandCorrelation.bandAmplitude L P N t m
  change (A * ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
      conj (B * ((ArithmeticFunction.moebius e : ℤ) : ℂ)) =
    (A * ((ArithmeticFunction.moebius (d / Nat.gcd d e) : ℤ) : ℂ)) *
      conj (B * ((ArithmeticFunction.moebius (e / Nat.gcd d e) : ℤ) : ℂ))
  simp only [map_mul, map_intCast]
  calc
    _ = (A * conj B) * (((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius e : ℤ) : ℂ)) := by ring
    _ = _ := by rw [hc]; ring

/-- The exact complete Gram entry depends on the reduced coprime
Mobius pair and a displaced physical cutoff. The original amplitude still
uses L, not L-log(gcd): shifting that amplitude would change the carrier. -/
theorem primeWindowGram_entry_reduce_gcd (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) (p q : ℕ → ℕ) (n m : ℕ) {d e : ℕ}
    (hd : Squarefree d) (he : Squarefree e) :
    (primeWindowCoefficient L P N t p ⟨n, d⟩ *
        conj (primeWindowCoefficient L P N t p ⟨m, e⟩)) *
      (unitOverlap (primeWindowLower L p q ⟨n, d⟩) (primeWindowUpper L p ⟨n, d⟩)
        (primeWindowLower L p q ⟨m, e⟩) (primeWindowUpper L p ⟨m, e⟩) : ℂ) =
    (primeWindowCoefficient L P N t p ⟨n, d / Nat.gcd d e⟩ *
        conj (primeWindowCoefficient L P N t p ⟨m, e / Nat.gcd d e⟩)) *
      (unitOverlap
        (primeWindowLower (L - Real.log (Nat.gcd d e)) p q ⟨n, d / Nat.gcd d e⟩)
        (primeWindowUpper (L - Real.log (Nat.gcd d e)) p ⟨n, d / Nat.gcd d e⟩)
        (primeWindowLower (L - Real.log (Nat.gcd d e)) p q ⟨m, e / Nat.gcd d e⟩)
        (primeWindowUpper (L - Real.log (Nat.gcd d e)) p ⟨m, e / Nat.gcd d e⟩) : ℂ) := by
  have hg : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd.ne_zero)
  have hqd : 0 < d / Nat.gcd d e := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) (Nat.gcd_dvd_left d e)) hg
  have hqe : 0 < e / Nat.gcd d e := Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero he.ne_zero) (Nat.gcd_dvd_right d e)) hg
  have hld := primeWindowLower_factor L p q n hg hqd
  have hrd := primeWindowUpper_factor L p n hg hqd
  have hle := primeWindowLower_factor L p q m hg hqe
  have hre := primeWindowUpper_factor L p m hg hqe
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)] at hld hrd
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)] at hle hre
  rw [primeWindowCoefficient_pair_reduce_gcd L P N t p n m hd he, hld, hrd, hle, hre]

end
end RiemannGaussian.ZetaRieszWindowGcd
