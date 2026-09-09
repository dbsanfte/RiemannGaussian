/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteGaussianGram

/-!
# Bilinear curvature of arbitrary finite Laplace sums

The curvature `f'^2 - f*f''` is an exact signed sum of squared frequency
gaps. Its coefficients are bilinear, with no conjugation: the oscillation
uses the sum of the two frequencies. Self-pairs vanish, but this does not
assert a sign for the remaining complex sum.
-/

open Complex Filter MeasureTheory Set Topology
namespace RiemannGaussian
noncomputable section

variable {ι : Type*}

/-- The logarithmic moments of a finite Laplace sum with arbitrary complex
coefficients and real frequencies. -/
def finiteLaplaceMoment (S : Finset ι) (c : ι → ℂ) (l : ι → ℝ)
    (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ S, c j * (l j : ℂ) ^ k * exp (-s * (l j : ℂ))

/-- Differentiation advances the frequency moment, retaining its sign. -/
theorem hasDerivAt_finiteLaplaceMoment (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteLaplaceMoment S c l k)
      (-finiteLaplaceMoment S c l (k + 1) s) s := by
  have ht (j : ι) : HasDerivAt
      (fun w : ℂ => c j * (l j : ℂ) ^ k * exp (-w * (l j : ℂ)))
      (-(c j * (l j : ℂ) ^ (k + 1) * exp (-s * (l j : ℂ)))) s := by
    convert! ((((hasDerivAt_id s).fun_neg.mul_const (l j : ℂ)).cexp).const_mul
      (c j * (l j : ℂ) ^ k)) using 1
    simp only [id_eq]
    ring
  unfold finiteLaplaceMoment
  convert! HasDerivAt.fun_sum (u := S) (fun j _ => ht j) using 1
  exact (Finset.sum_neg_distrib _).symm

/-- The first derivative of a finite Laplace sum is its negative first
moment. -/
theorem deriv_finiteLaplaceMoment (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (k : ℕ) (s : ℂ) :
    deriv (finiteLaplaceMoment S c l k) s =
      -finiteLaplaceMoment S c l (k + 1) s :=
  (hasDerivAt_finiteLaplaceMoment S c l k s).deriv

/-- The second derivative has positive second-moment sign. -/
theorem deriv_deriv_finiteLaplaceMoment_zero (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (s : ℂ) :
    deriv (deriv (finiteLaplaceMoment S c l 0)) s =
      finiteLaplaceMoment S c l 2 s := by
  have he : deriv (finiteLaplaceMoment S c l 0) =
      fun w => -finiteLaplaceMoment S c l 1 w := by
    funext w
    exact deriv_finiteLaplaceMoment S c l 0 w
  rw [he]
  simpa only [neg_neg, Nat.reduceAdd] using
    (hasDerivAt_finiteLaplaceMoment S c l 1 s).fun_neg.deriv

/-- The full complex bilinear variance identity, with arbitrary weights.
It is not a Hermitian norm identity. -/
theorem sum_bilinear_frequency_gap_sq (S : Finset ι) (a l : ι → ℂ) :
    (∑ j ∈ S, ∑ k ∈ S, a j * a k * (l j - l k) ^ 2) =
      2 * ((∑ j ∈ S, a j) * (∑ j ∈ S, a j * l j ^ 2) -
        (∑ j ∈ S, a j * l j) ^ 2) := by
  have he (j k : ι) : a j * a k * (l j - l k) ^ 2 =
      (a j * l j ^ 2) * a k + a j * (a k * l k ^ 2) -
        2 * (a j * l j) * (a k * l k) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show (∑ j ∈ S, 2 * (a j * l j)) = 2 * ∑ j ∈ S, a j * l j from
    (Finset.mul_sum S (fun j => a j * l j) 2).symm]
  ring

/-- The complete pair kernel of finite Laplace curvature. Both phases and
both coefficient signs are retained. -/
def finiteLaplaceGapSum (S : Finset ι) (c : ι → ℂ) (l : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ S, ∑ k ∈ S, c j * c k *
    exp (-s * ((l j : ℂ) + (l k : ℂ))) * ((l j : ℂ) - (l k : ℂ)) ^ 2

/-- Exact curvature expansion for every finite coefficient family. The
frequency gap is squared before any sign or phase is discarded. -/
theorem finiteLaplace_curvature_eq_gapSum (S : Finset ι) (c : ι → ℂ)
    (l : ι → ℝ) (s : ℂ) :
    deriv (finiteLaplaceMoment S c l 0) s ^ 2 -
      finiteLaplaceMoment S c l 0 s * deriv (deriv (finiteLaplaceMoment S c l 0)) s =
        -(1 / 2 : ℂ) * finiteLaplaceGapSum S c l s := by
  rw [deriv_finiteLaplaceMoment, deriv_deriv_finiteLaplaceMoment_zero]
  have h := sum_bilinear_frequency_gap_sq S
    (fun j => c j * exp (-s * (l j : ℂ))) (fun j => (l j : ℂ))
  have hgap : finiteLaplaceGapSum S c l s =
      ∑ j ∈ S, ∑ k ∈ S,
        (c j * exp (-s * (l j : ℂ))) * (c k * exp (-s * (l k : ℂ))) *
          ((l j : ℂ) - (l k : ℂ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [show -s * ((l j : ℂ) + (l k : ℂ)) =
      -s * (l j : ℂ) + -s * (l k : ℂ) by ring, Complex.exp_add]
    ring
  rw [hgap, h]
  simp only [finiteLaplaceMoment, pow_zero, mul_one, pow_one, Nat.reduceAdd]
  simp_rw [show ∀ j : ι, c j * (l j : ℂ) * exp (-s * (l j : ℂ)) =
    c j * exp (-s * (l j : ℂ)) * (l j : ℂ) by intro j; ring,
    show ∀ j : ι, c j * (l j : ℂ) ^ 2 * exp (-s * (l j : ℂ)) =
    c j * exp (-s * (l j : ℂ)) * (l j : ℂ) ^ 2 by intro j; ring]
  ring

/-- The literal self-pair in the curvature expansion is identically zero,
independently of its coefficient or complex phase. -/
theorem finiteLaplaceGapSum_diagonal (c : ι → ℂ) (l : ι → ℝ) (s : ℂ) (j : ι) :
    c j * c j * exp (-s * ((l j : ℂ) + (l j : ℂ))) *
      ((l j : ℂ) - (l j : ℂ)) ^ 2 = 0 := by simp

end
end RiemannGaussian
