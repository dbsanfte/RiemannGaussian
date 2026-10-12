/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGramAudit

/-!
# Cutoff GCD matrices: exact incidence and density/source audit

All integer rows and all complex prime-power phases are retained. The
ordinary PSD mechanism is valid for every nonnegative denominator weight.
Twisting the literal prime powers does not preserve this PSD conclusion.
These results do not exclude nonlinear cross-column arithmetic constraints.
-/

namespace RiemannGaussian.ArithmeticOperatorGcdAudit
noncomputable section
open scoped BigOperators ComplexConjugate
open ArithmeticOperatorGramAudit
open SuzukiCarryCorrelation

/-- GCD incidence with an arbitrary complex divisor weight. -/
def gcdKernel (w : ℕ → ℂ) (m n : ℕ) : ℂ :=
  ∑ d ∈ (Nat.gcd m n).divisors, w d

/-- The full finite cutoff quadratic before the rows are joined. -/
def gcdQuadratic (X : ℕ) (alpha w : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    alpha m*conj (alpha n)*gcdKernel w m n

/-- Divisibility feature of the literal finite integer lattice. -/
def divisorFeature (m d : ℕ) : ℂ := if d ∣ m then 1 else 0

/-- The GCD factorization is an exact identity for every complex weight,
including a von Mangoldt weight with its full height phase. -/
theorem gcdKernel_eq_incidence {X m n : ℕ} (hm : 0 < m) (hmX : m ≤ X)
    (w : ℕ → ℂ) :
    gcdKernel w m n = ∑ d ∈ Finset.Icc 1 X,
      w d*divisorFeature m d*conj (divisorFeature n d) := by
  classical
  have hg : Nat.gcd m n ≠ 0 := (Nat.gcd_pos_of_pos_left n hm).ne'
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ m ∧ d ∣ n) =
      (Nat.gcd m n).divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hg⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hm,(Nat.le_of_dvd hm hd.1).trans hmX⟩,hd⟩
  have ht (d : ℕ) : w d*divisorFeature m d*conj (divisorFeature n d) =
      if d ∣ m ∧ d ∣ n then w d else 0 := by
    by_cases ha : d ∣ m <;> by_cases hb : d ∣ n <;> simp [divisorFeature,ha,hb]
  simp_rw [ht]
  rw [← Finset.sum_filter,he]
  rfl

/-- Every row correlation collapses to the same arithmetic columns. -/
theorem gcdQuadratic_eq_joined (X : ℕ) (alpha w : ℕ → ℂ) :
    gcdQuadratic X alpha w =
      joinedGram (Finset.Icc 1 X) (Finset.Icc 1 X) alpha divisorFeature w := by
  unfold gcdQuadratic joinedGram
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n _
  rw [gcdKernel_eq_incidence (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2]

/-- Untwisted actual-prime factorization evaluates the entire GCD entry,
whereas the twisted entry remains its signed divisor polynomial. -/
theorem gcdKernel_mangoldt (m n : ℕ) :
    gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) m n =
      (Real.log (Nat.gcd m n) : ℂ) := by
  simp only [gcdKernel,← Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum]

/-- Positive GCD quadratic forms impose no extra constraint on the
prime weights: every nonnegative sequence satisfies the same result. -/
theorem gcdQuadratic_nonnegative (X : ℕ) (alpha : ℕ → ℂ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ Finset.Icc 1 X, 0 ≤ w d) :
    0 ≤ (gcdQuadratic X alpha (fun d => (w d : ℂ))).re := by
  rw [gcdQuadratic_eq_joined]
  exact joinedGram_nonnegative_for_arbitrary_weights _ _ _ _ w hw

/-- Within the positive-density PSD mechanism, exact pole cancellation
deletes every signed source. A signed difference of such forms requires
an independent prime estimate instead. -/
theorem gcdQuadratic_density_cancellation_kills_source (X : ℕ) (alpha : ℕ → ℂ)
    (density : ℕ → ℝ) (hdensity : ∀ d ∈ Finset.Icc 1 X, 0 < density d)
    (hpole : (gcdQuadratic X alpha (fun d => (density d : ℂ))).re = 0)
    (source : ℕ → ℂ) : gcdQuadratic X alpha source = 0 := by
  rw [gcdQuadratic_eq_joined] at hpole ⊢
  exact positive_density_cancellation_kills_source _ _ _ _ density hdensity hpole source

/-- Prime two alone gives the same exact diagonal as the Gamma/Kummer
mixed Hessian at the origin. No prime powers are dropped. -/
theorem gcdKernel_two_twisted (y : ℝ) :
    gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) 2 2 =
      ArithmeticOperatorKummerCutoff.twistedHessian 0 0 y := by
  rw [gcdKernel,Nat.gcd_self,Nat.prime_two.divisors]
  simp [primePhase,ArithmeticOperatorKummerCutoff.twistedHessian,
    ArithmeticOperatorKummerCutoff.weightedHessian_origin]

/-- A real-part PSD theorem for the twisted actual-prime GCD matrix
cannot hold at all campaign heights. This unrestricted matrix audit is
not a cofinal bulk bound at a hypothetical zero ordinate. -/
theorem exists_campaign_negative_gcd_diagonal :
    ∃ y : ℝ, 54 ≤ y ∧
      (gcdKernel (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) 2 2).re < 0 := by
  obtain ⟨y,hy,hn⟩ := ArithmeticOperatorKummerCutoff.exists_campaign_negative_twisted_diagonal
  exact ⟨y,hy,by simpa only [gcdKernel_two_twisted] using hn⟩

end
end RiemannGaussian.ArithmeticOperatorGcdAudit
