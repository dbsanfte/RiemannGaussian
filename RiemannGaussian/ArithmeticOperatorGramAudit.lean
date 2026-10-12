/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorRamanujanAudit

/-!
# Joined Gram and scalar-bound collapse audit

This applies to deterministic divisor, quotient, modular and finite
Gaussian-feature matrices. Positivity from nonnegative column weights
survives arbitrary weights of that sign; it is not a source-sensitive
constraint special to the actual primes. No bound for the twisted prime
measure is claimed.
-/

namespace RiemannGaussian.ArithmeticOperatorGramAudit
noncomputable section
open scoped BigOperators ComplexConjugate

/-- Joined quadratic with its arithmetic column weight still signed. -/
def joinedGram {ι κ : Type*} (S : Finset ι) (D : Finset κ)
    (alpha : ι → ℂ) (feature : ι → κ → ℂ) (w : κ → ℂ) : ℂ :=
  ∑ i ∈ S, ∑ j ∈ S, alpha i*conj (alpha j)*
    ∑ d ∈ D, w d*feature i d*conj (feature j d)

/-- Exact denominator kernel after all incidences have been joined. -/
def gramKernel {ι κ : Type*} (S : Finset ι) (alpha : ι → ℂ)
    (feature : ι → κ → ℂ) (d : κ) : ℝ :=
  ‖∑ i ∈ S, alpha i*feature i d‖^2

/-- Arbitrary-weight collapse with phase and correlations retained. -/
theorem joinedGram_eq {ι κ : Type*} (S : Finset ι) (D : Finset κ)
    (alpha : ι → ℂ) (feature : ι → κ → ℂ) (w : κ → ℂ) :
    joinedGram S D alpha feature w = ∑ d ∈ D, w d*(gramKernel S alpha feature d : ℂ) := by
  classical
  unfold joinedGram gramKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Complex.sq_norm,← Complex.mul_conj]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The PSD conclusion holds for every nonnegative arithmetic measure;
it imposes no additional literal-prime constraint. -/
theorem joinedGram_nonnegative_for_arbitrary_weights {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (alpha : ι → ℂ) (feature : ι → κ → ℂ)
    (w : κ → ℝ) (hw : ∀ d ∈ D, 0 ≤ w d) :
    0 ≤ (joinedGram S D alpha feature (fun d => (w d : ℂ))).re := by
  rw [joinedGram_eq, Complex.re_sum]
  apply Finset.sum_nonneg
  intro d hd
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hw d hd) (sq_nonneg _)

/-- A universal bound on an arbitrary-weight signed scalar test is
possible only when its complete joined kernel is zero. -/
theorem scalar_bound_forall_weights_iff {κ : Type*} (D : Finset κ) (K : κ → ℂ) (B : ℝ) :
    (∀ w : κ → ℂ, ‖∑ d ∈ D, w d*K d‖ ≤ B) ↔
      0 ≤ B ∧ ∀ d ∈ D, K d = 0 := by
  classical
  constructor
  · intro h
    have hB : 0 ≤ B := by simpa using h (fun _ => 0)
    refine ⟨hB,?_⟩
    intro d hd
    by_contra hk
    have hh := h (fun n => if n = d then ((B+1 : ℝ) : ℂ)/K d else 0)
    have he : (∑ n ∈ D, (if n = d then ((B+1 : ℝ) : ℂ)/K d else 0)*K n) =
        ((B+1 : ℝ) : ℂ) := by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq', ite_eq_left hd, div_mul_cancel₀ _ hk]
    rw [he] at hh
    have : B+1 ≤ B := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ B+1)] using hh
    linarith
  · rintro ⟨hB,hK⟩ w
    have he : (∑ d ∈ D, w d*K d) = 0 :=
      Finset.sum_eq_zero (fun d hd => by rw [hK d hd,mul_zero])
    simpa only [he,norm_zero] using hB

/-- Exact density-cancellation obstruction for a single PSD quadratic.
A strictly positive density cannot have zero response unless every
joined column amplitude vanishes. This also applies to finite Gaussian
feature lifts; no prime sequence or asymptotic estimate is used. -/
theorem positive_density_zero_iff {ι κ : Type*} (S : Finset ι) (D : Finset κ)
    (alpha : ι → ℂ) (feature : ι → κ → ℂ) (density : κ → ℝ)
    (hdensity : ∀ d ∈ D, 0 < density d) :
    (joinedGram S D alpha feature (fun d => (density d : ℂ))).re = 0 ↔
      ∀ d ∈ D, gramKernel S alpha feature d = 0 := by
  rw [joinedGram_eq, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  have hn (d : κ) (hd : d ∈ D) :
      0 ≤ density d*gramKernel S alpha feature d :=
    mul_nonneg (hdensity d hd).le (sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg hn]
  constructor
  · intro h d hd
    exact (mul_eq_zero.mp (h d hd)).resolve_left (hdensity d hd).ne'
  · intro h d hd
    rw [h d hd,mul_zero]

/-- Pole cancellation by a positive-density PSD statistic annihilates
EVERY signed source, not only the continuous density. To retain a zero
source one must introduce signed combinations and then prove genuinely
new arithmetic cancellation for those combinations. -/
theorem positive_density_cancellation_kills_source {ι κ : Type*}
    (S : Finset ι) (D : Finset κ) (alpha : ι → ℂ) (feature : ι → κ → ℂ)
    (density : κ → ℝ) (hdensity : ∀ d ∈ D, 0 < density d)
    (hpole : (joinedGram S D alpha feature (fun d => (density d : ℂ))).re = 0)
    (source : κ → ℂ) : joinedGram S D alpha feature source = 0 := by
  have hk := (positive_density_zero_iff S D alpha feature density hdensity).mp hpole
  rw [joinedGram_eq]
  exact Finset.sum_eq_zero (fun d hd => by rw [hk d hd,Complex.ofReal_zero,mul_zero])

end
end RiemannGaussian.ArithmeticOperatorGramAudit
