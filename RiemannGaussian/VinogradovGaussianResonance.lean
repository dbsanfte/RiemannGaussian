/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianKernel

/-!
# Full Gaussian resonance fibres of the product moment

The signed Gaussian tuple Gram form is grouped by its exact integer
frequency differences. The complete weighted fibre identity precedes
the bound by the homogeneous moment. No coordinate projection, support
box or deletion of Gaussian translates is used in this reduction.
-/

namespace RiemannGaussian.VinogradovGaussianResonance
noncomputable section
open VinogradovMeanValue VinogradovShiftedMoment VinogradovMomentReduction
open VinogradovGaussianKernel
open scoped BigOperators ComplexConjugate

/-- The complete set of attainable integer frequency differences. -/
def differenceSupport {d ι : Type*} [Fintype ι] (v : ι → d → ℤ) : Finset (d → ℤ) := by
  classical
  exact Finset.univ.image (fun p : ι × ι => v p.1 - v p.2)

/-- Exact grouping of a weighted Gram sum by the full difference vector.
Every complex weighted fibre is retained before taking any majorant. -/
theorem sum_weightedShift {d ι : Type*} [Fintype d] [Fintype ι]
    (v : ι → d → ℤ) (w : ι → ℂ) (F : (d → ℤ) → ℂ) :
    (∑ h ∈ differenceSupport v, weightedShift v w h * F h) =
      ∑ b, ∑ c, (w b * conj (w c)) * F (v b - v c) := by
  classical
  let : DecidableEq (d → ℤ) := Classical.decEq _
  calc
    _ = ∑ h ∈ differenceSupport v,
        ∑ p ∈ Finset.univ.filter (fun p : ι × ι => v p.1 - v p.2 = h),
          (w p.1 * conj (w p.2)) * F (v p.1 - v p.2) := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [weightedShift, Finset.sum_mul, Finset.sum_filter,
        Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hbc : v b = v c + h
      · have hd : v b - v c = h := sub_eq_iff_eq_add'.mpr hbc
        rw [if_pos hbc, if_pos hd, hd]
      · have hd : v b - v c ≠ h := fun he => hbc (sub_eq_iff_eq_add'.mp he)
        rw [if_neg hbc, if_neg hd, zero_mul]
    _ = ∑ p : ι × ι, (w p.1 * conj (w p.2)) * F (v p.1 - v p.2) := by
      unfold differenceSupport
      exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
        (fun p hp => Finset.mem_image_of_mem (fun q : ι × ι => v q.1 - v q.2) hp)
        (fun p : ι × ι => (w p.1 * conj (w p.2)) * F (v p.1 - v p.2))
    _ = _ := Fintype.sum_prod_type _

/-- Coordinatewise multiplication by the exact real coefficient vector. -/
def linearSample {k : ℕ} (γ : Fin k → ℝ) (v : Fin k → ℤ) : Fin k → ℝ :=
  fun j => γ j * (v j : ℝ)

/-- The coefficient map preserves the full signed difference vector. -/
theorem linearSample_sub {k : ℕ} (γ : Fin k → ℝ) (v u : Fin k → ℤ) :
    linearSample γ (v - u) = linearSample γ v - linearSample γ u := by
  ext j
  simp only [linearSample, Pi.sub_apply, Int.cast_sub, mul_sub]

/-- Coefficient sampling commutes with every finite tuple sum. -/
theorem linearSample_sum {k : ℕ} {ι : Type*} (γ : Fin k → ℝ)
    (S : Finset ι) (v : ι → Fin k → ℤ) :
    linearSample γ (∑ b ∈ S, v b) = ∑ b ∈ S, linearSample γ (v b) := by
  ext j
  simp only [linearSample, Finset.sum_apply, Int.cast_sum, Finset.mul_sum]

/-- The actual tuple Gram form is exactly its full weighted frequency
fibres, with all real coefficient correlations and complex signs retained. -/
theorem momentGram_eq_fibres {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a γ : Fin k → ℝ) (v : ι → Fin k → ℤ) (w : ι → ℂ) :
    momentGram s a (fun b => linearSample γ (v b)) w =
      ∑ h ∈ differenceSupport (tupleFrequency s v),
        weightedShift (tupleFrequency s v) (tupleWeight s w) h *
          (latticeKernel a (linearSample γ h) : ℂ) := by
  rw [sum_weightedShift]
  unfold momentGram
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  simp only [linearSample_sub, tupleFrequency, linearSample_sum]

/-- The complete positive Gaussian resonance sum on attainable integer
differences, retaining the entire coordinate vector and all translates. -/
def resonanceSum {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) (a γ : Fin k → ℝ) (v : ι → Fin k → ℤ) : ℝ :=
  ∑ h ∈ differenceSupport (tupleFrequency s v), latticeKernel a (linearSample γ h)

/-- The homogeneous moment controls every weighted difference fibre.
The remaining cost is the full joint Gaussian resonance sum. This bound
is downstream from the exact signed fibre identity. -/
theorem momentGram_re_le {k : ℕ} {ι : Type*} [Fintype ι]
    (s : ℕ) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (γ : Fin k → ℝ) (v : ι → Fin k → ℤ) (w : ι → ℂ)
    (hw : ∀ b, ‖w b‖ ≤ 1) :
    (momentGram s a (fun b => linearSample γ (v b)) w).re ≤
      moment s v * resonanceSum s a γ v := by
  rw [momentGram_eq_fibres, resonanceSum, Finset.mul_sum]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply Finset.sum_le_sum
  intro h hh
  have hf : (weightedShift (tupleFrequency s v) (tupleWeight s w) h).re ≤ moment s v :=
    (Complex.re_le_norm _).trans ((weightedShift_norm_le_count _ _
      (tupleWeight_norm_le_one s w hw) h).trans (tuple_differenceCount_le_moment s v h))
  exact mul_le_mul_of_nonneg_right hf
    (Finset.prod_nonneg (fun j _ => kernel_nonneg (ha j) _))

/-- The actual dual moment is reduced to the homogeneous moment of the
second frequency family and a complete joint resonance sum. All weights
with norm at most one are covered uniformly. -/
theorem dualMoment_le_moment_resonance {k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℕ) (v : ι → Fin k → ℤ) (u : κ → Fin k → ℤ) (γ : Fin k → ℝ)
    (w : κ → ℂ) (hw : ∀ b, ‖w b‖ ≤ 1)
    {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) :
    dualMoment r s v (fun b j => (linearSample γ (u b) j : UnitAddCircle)) w ≤
      Real.exp (supportCost a (frequencySupport (tupleFrequency r v))) *
        moment s u * resonanceSum s a γ u := by
  apply (dualMoment_le_gaussian_gram r s v (fun b => linearSample γ (u b)) w ha).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (momentGram_re_le s ha γ u w hw) (Real.exp_pos _).le

end
end RiemannGaussian.VinogradovGaussianResonance
