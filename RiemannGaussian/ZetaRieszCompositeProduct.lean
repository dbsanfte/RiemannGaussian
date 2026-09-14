/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFourier
import RiemannGaussian.ZetaPrimeNonlinearFactor
import Mathlib.NumberTheory.Primorial

/-!
# Complete composite products preserve unit, prime and band subtractions

The Fourier prime product of each squarefree integer generates an exact
finite Euler product. Removing the unit and ordinary primes leaves the
compensated exponential, with the nonlinear correction still multiplied
by the first-order core. Completing the actual finite band preserves its
entire omitted boundary as a signed subtraction. No boundary saving or
source-scale floor is inferred from these identities.
-/

namespace RiemannGaussian.ZetaRieszCompositeProduct
noncomputable section
open scoped BigOperators
open ZetaRieszPrimeFourier ZetaPrimeCharacterRemainder

/-- Multiplicative deformation retaining every logarithmic prime phase. -/
def deformedCoefficient (s : ℂ) (xi : ℝ) : ArithmeticFunction ℂ :=
  ArithmeticFunction.prodPrimeFactors
    (fun p => zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))

/-- The deformation at a squarefree integer is the original feature times
its full prime-factor Fourier product. -/
theorem deformedCoefficient_apply {n : ℕ} (hn : Squarefree n) (s : ℂ) (xi : ℝ) :
    deformedCoefficient s xi n = zetaPrimeFeature s n * primeProduct n xi := by
  rw [deformedCoefficient, ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero,
    Finset.prod_mul_distrib]
  congr 1
  unfold zetaPrimeFeature
  rw [← Complex.exp_sum, CoprimeEulerPhase.squarefree_log_eq_prime_sum hn]
  simp only [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_neg_distrib]

/-- Completing a squarefree divisor set preserves its exact deformed Euler
product, with no norm relaxation. -/
theorem sum_divisors_eq_product {m : ℕ} (hm : Squarefree m) (s : ℂ) (xi : ℝ) :
    (∑ n ∈ m.divisors, zetaPrimeFeature s n * primeProduct n xi) =
      ∏ p ∈ m.primeFactors, (1 + zetaPrimeFeature s p *
        (1 - zetaPrimeFeature (Complex.I * xi) p)) := by
  have h := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
    (fun p => zetaPrimeFeature s p * (1 - zetaPrimeFeature (Complex.I * xi) p))).prodPrimeFactors_one_add_of_squarefree hm
  calc
    _ = ∑ n ∈ m.divisors, deformedCoefficient s xi n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (deformedCoefficient_apply (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hn)) s xi).symm
    _ = _ := by
      rw [deformedCoefficient, ← h]
      apply Finset.prod_congr rfl
      intro p hp
      simp only [ArithmeticFunction.prodPrimeFactors_apply
        (Nat.prime_of_mem_primeFactors hp).ne_zero,
        (Nat.prime_of_mem_primeFactors hp).primeFactors, Finset.prod_singleton]

/-- The unit-free prime part of a divisor set is exactly its prime factors. -/
theorem prime_divisors_eq_primeFactors (m : ℕ) :
    (m.divisors.erase 1).filter Nat.Prime = m.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨h.2, h.1.2.1, h.1.2.2⟩,
    fun h => ⟨⟨h.1.ne_one, h.2⟩, h.1⟩⟩

/-- The complete composite divisor sum deletes the unit and the entire
first-order prime sum exactly, rather than silently absorbing them. -/
theorem sum_composites_eq_product_sub {m : ℕ} (hm : Squarefree m) (s : ℂ) (xi : ℝ) :
    (∑ n ∈ (m.divisors.erase 1).filter (fun n => ¬ n.Prime),
      zetaPrimeFeature s n * primeProduct n xi) =
      (∏ p ∈ m.primeFactors, (1 + zetaPrimeFeature s p *
        (1 - zetaPrimeFeature (Complex.I * xi) p))) - 1 -
        ∑ p ∈ m.primeFactors, zetaPrimeFeature s p *
          (1 - zetaPrimeFeature (Complex.I * xi) p) := by
  have hs := Finset.sum_filter_add_sum_filter_not (m.divisors.erase 1) Nat.Prime
    (fun n => zetaPrimeFeature s n * primeProduct n xi)
  rw [prime_divisors_eq_primeFactors] at hs
  have he := Finset.sum_erase_add m.divisors
    (fun n => zetaPrimeFeature s n * primeProduct n xi) (Nat.one_mem_divisors.mpr hm.ne_zero)
  rw [sum_divisors_eq_product hm s xi] at he
  have h1 : zetaPrimeFeature s 1 * primeProduct 1 xi = 1 := by
    simp [zetaPrimeFeature, primeProduct]
  rw [h1] at he
  have hp : (∑ p ∈ m.primeFactors, zetaPrimeFeature s p * primeProduct p xi) =
      ∑ p ∈ m.primeFactors, zetaPrimeFeature s p *
        (1 - zetaPrimeFeature (Complex.I * xi) p) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [primeProduct, (Nat.prime_of_mem_primeFactors hp).primeFactors,
      Finset.prod_singleton]
  rw [hp] at hs
  linear_combination hs + he

/-- The imaginary-power feature uses the negative frequency in the
existing first-order and local-log character definitions. -/
theorem imaginary_feature_eq_character (p : ℕ) (xi : ℝ) :
    zetaPrimeFeature (Complex.I * xi) p =
      Complex.exp (((Real.log p * (-xi) : ℝ) : ℂ) * Complex.I) := by
  unfold zetaPrimeFeature
  congr 1
  push_cast
  ring

/-- Completing the actual composite prime response gives a compensated
exponential, with its whole singleton subtraction retained. -/
theorem sum_composites_eq_compensated_exp {m : ℕ} (hm : Squarefree m)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hm16 : ∀ p ∈ m.primeFactors, 16 ≤ p) (xi : ℝ) :
    (∑ n ∈ (m.divisors.erase 1).filter (fun n => ¬ n.Prime),
      zetaPrimeFeature s n * primeProduct n xi) =
      Complex.exp (firstOrder m.primeFactors (zetaPrimeFeature s) (fun p => Real.log p) (-xi) +
        logRemainder m.primeFactors (zetaPrimeFeature s) (fun p => Real.log p) (-xi)) - 1 -
        firstOrder m.primeFactors (zetaPrimeFeature s) (fun p => Real.log p) (-xi) := by
  rw [sum_composites_eq_product_sub hm s xi]
  simp_rw [imaginary_feature_eq_character]
  rw [normalized_character_eq_exp _ _ _
    (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (hm16 p hp))]
  rfl

/-- The bounded nonlinear correction remains multiplied by the original
first-order exponential. This identity does not discard that coupling. -/
theorem compensated_exp_split (A E : ℂ) :
    Complex.exp (A + E) - 1 - A =
      (Complex.exp A - 1 - A) + Complex.exp A * (Complex.exp E - 1) := by
  rw [Complex.exp_add]
  ring

/-- The complete composite generating function retains the exact unit
and singleton deletions, including any small primes. -/
def compositeResponse (m : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  (∏ p ∈ m.primeFactors, (1 + zetaPrimeFeature s p *
    (1 - zetaPrimeFeature (Complex.I * xi) p))) - 1 -
      ∑ p ∈ m.primeFactors, zetaPrimeFeature s p *
        (1 - zetaPrimeFeature (Complex.I * xi) p)

/-- Every original squarefree composite band label occurs in the complete
divisor universe of its actual upper endpoint, with exactly the same support. -/
theorem actual_band_support_eq (N : ℕ) :
    (((primorial (2 ^ (32 * N))).divisors.erase 1).filter (fun n => ¬ n.Prime)).filter
        (fun n => n ∈ zetaPrimeLogBand N) =
      (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨h1, hd, _h0⟩, hp⟩, hband⟩
    exact ⟨hband, (squarefree_primorial _).squarefree_of_dvd hd, h1, hp⟩
  · rintro ⟨hband, hsf, h1, hp⟩
    have hb : n ≤ 2 ^ (32 * N) := (Finset.mem_Icc.mp (Finset.mem_filter.mp hband).1).2
    exact ⟨⟨⟨h1, hsf.dvd_primorial.trans (primorial_dvd_primorial hb),
      primorial_ne_zero _⟩, hp⟩, hband⟩

/-- Completing the actual finite band exposes the entire omitted boundary
as a signed subtraction. No bound or smallness of that boundary is asserted. -/
theorem actual_band_symbol_eq_completed_sub_boundary (N : ℕ) (s : ℂ) (xi : ℝ) :
    (∑ n ∈ (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
      zetaPrimeFeature s n * primeProduct n xi) =
      compositeResponse (primorial (2 ^ (32 * N))) s xi -
        ∑ n ∈ (((primorial (2 ^ (32 * N))).divisors.erase 1).filter
          (fun n => ¬ n.Prime)).filter (fun n => n ∉ zetaPrimeLogBand N),
          zetaPrimeFeature s n * primeProduct n xi := by
  have h := Finset.sum_filter_add_sum_filter_not
    (((primorial (2 ^ (32 * N))).divisors.erase 1).filter (fun n => ¬ n.Prime))
    (fun n => n ∈ zetaPrimeLogBand N) (fun n => zetaPrimeFeature s n * primeProduct n xi)
  rw [actual_band_support_eq, sum_composites_eq_product_sub (squarefree_primorial _)] at h
  exact eq_sub_iff_add_eq.mpr h


end
end RiemannGaussian.ZetaRieszCompositeProduct
