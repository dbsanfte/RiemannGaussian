/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHeadOrders
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Differentiating absolutely convergent labelled Dirichlet families

This permits increasing prime tuples as indices without dropping their
ordering or identifying a divergent series with a totalized sum.
-/

namespace RiemannGaussian.DirichletFamilyMoments
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical

/-- One negative derivative raises the exact factorial moment. -/
theorem kernel_hasDerivAt (N n : ℕ) (s : ℂ) :
    HasDerivAt (fun z => zetaPrimeLogKernel N z n)
      (-((N+1 : ℕ) : ℂ)*zetaPrimeLogKernel (N+1) s n) s := by
  have h := (((hasDerivAt_id s).mul_const (Real.log n : ℂ)).neg).cexp
  simp only [Pi.neg_apply, id_eq, one_mul] at h
  have hh := h.const_mul ((Real.log n : ℂ)^N / (N.factorial : ℂ))
  convert! hh using 1
  · rw [neg_mul, ← ZetaRieszHeadOrders.log_mul_kernel]
    simp only [zetaPrimeLogKernel, zetaPrimeFeature]
    ring

/-- The complete labelled factorial moment. -/
def moment {ι : Type*} (a : ι → ℂ) (n : ι → ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑' i, a i * zetaPrimeLogKernel N s (n i)

/-- A single absolutely convergent lower real edge controls all moments
uniformly throughout a strictly smaller right half-plane. -/
theorem term_bound {ι : Type*} (a : ι → ℂ) (n : ι → ℕ) (N : ℕ)
    {σ q : ℝ} (hq : 0 < q) {s : ℂ} (hs : σ+q ≤ s.re) (i : ι) :
    ‖a i * zetaPrimeLogKernel N s (n i)‖ ≤
      q⁻¹^N * ‖a i * zetaPrimeFeature (σ : ℂ) (n i)‖ := by
  rw [norm_mul, norm_mul, norm_zetaPrimeFeature, Complex.ofReal_re]
  have he : zetaPrimeExpWeight (s.re-q) (n i) ≤ zetaPrimeExpWeight σ (n i) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_natCast_nonneg (n i)]
  calc
    _ ≤ ‖a i‖ * (q⁻¹^N * zetaPrimeExpWeight (s.re-q) (n i)) :=
      mul_le_mul_of_nonneg_left (norm_zetaPrimeLogKernel_le N s (n i) hq) (norm_nonneg _)
    _ ≤ ‖a i‖ * (q⁻¹^N * zetaPrimeExpWeight σ (n i)) := by gcongr
    _ = _ := by ring

/-- Absolute convergence at every real edge greater than one justifies
each actual logarithmic moment throughout the Euler half-plane. -/
theorem summable_moment {ι : Type*} (a : ι → ℂ) (n : ι → ℕ)
    (h : ∀ σ : ℝ, 1 < σ → Summable (fun i => a i*zetaPrimeFeature (σ : ℂ) (n i)))
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun i => a i*zetaPrimeLogKernel N s (n i)) := by
  let σ := (1+s.re)/2
  let q := (s.re-1)/2
  have hq : 0 < q := by dsimp [q]; linarith
  apply ((h σ (by dsimp [σ]; linarith)).norm.mul_left (q⁻¹^N)).of_norm_bounded
  exact term_bound a n N hq (by dsimp [σ,q]; linarith)

/-- Differentiation under the complete sum preserves all complex signs. -/
theorem moment_hasDerivAt {ι : Type*} (a : ι → ℂ) (n : ι → ℕ)
    (h : ∀ σ : ℝ, 1 < σ → Summable (fun i => a i*zetaPrimeFeature (σ : ℂ) (n i)))
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (moment a n N) (-((N+1 : ℕ) : ℂ)*moment a n (N+1) s) s := by
  let σ := (1+s.re)/2
  let q := (s.re-1)/4
  let U : Set ℂ := {z | σ+q < z.re}
  have hq : 0 < q := by dsimp [q]; linarith
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by dsimp [U,σ,q]; linarith
  have hg := (h σ (by dsimp [σ]; linarith)).norm.mul_left (q⁻¹^N)
  have hd (i : ι) : DifferentiableOn ℂ (fun z => a i*zetaPrimeLogKernel N z (n i)) U :=
    fun z _ => ((kernel_hasDerivAt N (n i) z).const_mul (a i)).differentiableAt.differentiableWithinAt
  have hb (i : ι) (z : ℂ) (hz : z ∈ U) := term_bound a n N hq (le_of_lt hz) i
  have ht := Complex.hasSum_deriv_of_summable_norm hg hd hU hb hsU
  have he : deriv (moment a n N) s = -((N+1 : ℕ) : ℂ)*moment a n (N+1) s := by
    change deriv (fun w => ∑' i, a i*zetaPrimeLogKernel N w (n i)) s = _
    rw [← ht.tsum_eq]
    rw [moment, ← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [((kernel_hasDerivAt N (n i) s).const_mul (a i)).deriv]
    ring
  rw [← he]
  exact (Complex.differentiableOn_tsum_of_summable_norm hg hd hU hb).differentiableAt
    (hU.mem_nhds hsU) |>.hasDerivAt

/-- Every iterated negative derivative is the genuine log-power series,
with the factorial normalization and all original labels unchanged. -/
theorem iteratedDeriv_moment_zero {ι : Type*} (a : ι → ℂ) (n : ι → ℕ)
    (h : ∀ σ : ℝ, 1 < σ → Summable (fun i => a i*zetaPrimeFeature (σ : ℂ) (n i)))
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv N (moment a n 0) s = (-1 : ℂ)^N * (N.factorial : ℂ) * moment a n N s := by
  induction N generalizing s with
  | zero => simp
  | succ N ih =>
    have he : iteratedDeriv N (moment a n 0) =ᶠ[𝓝 s]
        (fun z => (-1 : ℂ)^N * (N.factorial : ℂ) * moment a n N z) := by
      filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
      exact ih hz
    rw [iteratedDeriv_succ, he.deriv_eq,
      ((moment_hasDerivAt a n h N hs).const_mul ((-1 : ℂ)^N * (N.factorial : ℂ))).deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

theorem signedTaylorMoment_eq {ι : Type*} (a : ι → ℂ) (n : ι → ℕ)
    (h : ∀ σ : ℝ, 1 < σ → Summable (fun i => a i*zetaPrimeFeature (σ : ℂ) (n i)))
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    signedTaylorMoment N (moment a n 0) s = moment a n N s := by
  rw [signedTaylorMoment, iteratedDeriv_moment_zero a n h N hs]
  have hf : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hh : (-1 : ℂ)^N * (-1 : ℂ)^N = 1 := by rw [← mul_pow]; simp
  field_simp
  linear_combination (moment a n N s) * hh

end
end RiemannGaussian.DirichletFamilyMoments
