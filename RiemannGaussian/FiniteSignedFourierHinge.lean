/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CosineHinge

/-!
# Two-frequency Fourier representation of finite signed cutoff measures

The complete complex character retains both positive and negative
frequencies. Their centered pair vanishes at zero and yields a genuinely
integrable inverse-square kernel. The exact hinge formula keeps the first
moment and cutoff phase; no conjugation relation on the weights is imposed.
-/

namespace RiemannGaussian.FiniteSignedFourierHinge
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open CosineHinge

/-- The full complex character of a finite signed atomic measure. -/
def finiteCharacter {ι : Type*} (S : Finset ι) (w : ι → ℂ) (x : ι → ℝ) (xi : ℝ) : ℂ :=
  ∑ i ∈ S, w i * Complex.exp (((xi * x i : ℝ) : ℂ) * Complex.I)

/-- The centered pair retains both frequencies of the complex measure. -/
def pairedNumerator {ι : Type*} (S : Finset ι) (w : ι → ℂ) (x : ι → ℝ)
    (L xi : ℝ) : ℂ :=
  (∑ i ∈ S, w i) -
    (Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) * finiteCharacter S w x xi +
     Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) * finiteCharacter S w x (-xi)) / 2

/-- Centering and coupling the two frequencies gives the exact cosine loss
for every complex atom, with no conjugation assumption on its weight. -/
theorem pairedNumerator_eq_sum {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (x : ι → ℝ) (L xi : ℝ) :
    pairedNumerator S w x L xi =
      ∑ i ∈ S, w i * ((1 - Real.cos ((x i - L) * xi) : ℝ) : ℂ) := by
  unfold pairedNumerator finiteCharacter
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hp : Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((xi * x i : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((x i - L) * xi : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-xi * x i : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((((x i - L) * xi : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc := Complex.two_cos (((x i - L) * xi : ℝ) : ℂ)
  rw [← Complex.ofReal_cos] at hc
  calc
    _ = w i * (1 - (Complex.exp ((((x i - L) * xi : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-((((x i - L) * xi : ℝ) : ℂ)) * Complex.I)) / 2) := by
      rw [← hp, ← hm]
      ring
    _ = _ := by rw [← hc]; push_cast; ring

/-- The coupled numerator vanishes exactly at frequency zero. -/
theorem pairedNumerator_zero {ι : Type*} (S : Finset ι) (w : ι → ℂ) (x : ι → ℝ)
    (L : ℝ) : pairedNumerator S w x L 0 = 0 := by
  simp [pairedNumerator_eq_sum]

/-- All finite signed weights give a genuinely integrable coupled kernel.
The first moment is outside the integral, and both frequency signs remain. -/
theorem integrable_pairedNumerator_div_sq {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (x : ι → ℝ) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => pairedNumerator S w x L xi / (xi : ℂ) ^ 2) (Ioi 0) := by
  have h : IntegrableOn (fun xi : ℝ => ∑ i ∈ S,
      w i * (((1 - Real.cos ((x i - L) * xi)) / xi ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ =>
      (Complex.ofRealCLM.integrable_comp (integrable_one_sub_cos_div_sq (x i - L))).const_mul (w i))
  convert h using 1
  funext xi
  rw [pairedNumerator_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  push_cast
  ring

/-- Exact Fourier representation of every finite signed cutoff tail.
The signed first moment, cutoff phase and both frequencies are retained. -/
theorem finite_hinge_eq_paired_integral {ι : Type*} (S : Finset ι) (w : ι → ℂ)
    (x : ι → ℝ) (L : ℝ) :
    (∑ i ∈ S, ((max 0 (x i - L) : ℝ) : ℂ) * w i) =
      (∑ i ∈ S, ((x i - L : ℝ) : ℂ) * w i) / 2 +
      (1 / (Real.pi : ℂ)) * ∫ xi : ℝ in Ioi 0,
        pairedNumerator S w x L xi / (xi : ℂ) ^ 2 := by
  have hid (xi : ℝ) : pairedNumerator S w x L xi / (xi : ℂ) ^ 2 =
      ∑ i ∈ S, w i * (((1 - Real.cos ((x i - L) * xi)) / xi ^ 2 : ℝ) : ℂ) := by
    rw [pairedNumerator_eq_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    push_cast
    ring
  simp_rw [hid]
  have hi (i : ι) : IntegrableOn (fun xi : ℝ =>
      w i * (((1 - Real.cos ((x i - L) * xi)) / xi ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    (Complex.ofRealCLM.integrable_comp (integrable_one_sub_cos_div_sq (x i - L))).const_mul (w i)
  rw [integral_finsetSum S (fun i _ => hi i),
    Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [integral_const_mul,
    integral_complex_ofReal,
    integral_one_sub_cos_div_sq]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (positive_part_eq_cosine_integral (x i - L))
  rw [integral_one_sub_cos_div_sq] at h
  push_cast at h ⊢
  rw [h]
  ring

end
end RiemannGaussian.FiniteSignedFourierHinge
