/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMomentPoleJet
import RiemannGaussian.MoebiusFiniteMellin
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A uniform regular part for finite Möbius convolution heads

The finite Dirichlet polynomial is the actual signed Möbius prefix.
Multiplying it by `-zeta'` produces a double pole and a simple pole whose
coefficients are retained exactly. Removing both gives an entire function.
A circle chosen uniformly in the divisor cutoff bounds the regular part
by a quadratic cutoff budget, independently of the moment order.
-/

open Complex Filter Metric Set Topology
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual finite Möbius Dirichlet polynomial, with exponential
weights exposing its entire dependence on the Mellin parameter. -/
def zetaMoebiusDirichletHead (D : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range D, ((μ (n + 1) : ℤ) : ℂ) *
    Complex.exp (-s * (Real.log (n + 1 : ℕ) : ℂ))

/-- The exponential presentation is exactly the repository's original
finite complex Möbius prefix, with the same coefficients and cutoff. -/
theorem zetaMoebiusDirichletHead_eq_prefix (D : ℕ) (s : ℂ) :
    zetaMoebiusDirichletHead D s = complexMoebiusFinitePrefix s D := by
  rw [zetaMoebiusDirichletHead, complexMoebiusFinitePrefix]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hn0 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  rw [Complex.cpow_def_of_ne_zero hn0]
  have he : Complex.log (n + 1 : ℂ) = (Real.log (n + 1 : ℕ) : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Complex.natCast_log (n := n + 1)).symm
  rw [he]
  congr 1
  ring

/-- Every finite signed Möbius head is entire. -/
theorem differentiable_zetaMoebiusDirichletHead (D : ℕ) : Differentiable ℂ (zetaMoebiusDirichletHead D) := by
  unfold zetaMoebiusDirichletHead
  fun_prop

/-- A cutoff-uniform elementary bound on the whole half-plane needed
by the chosen Cauchy circles. It does not assume Möbius cancellation. -/
theorem norm_zetaMoebiusDirichletHead_le (D : ℕ) {s : ℂ} (hs : -1 ≤ s.re) :
    ‖zetaMoebiusDirichletHead D s‖ ≤ (D + 1 : ℝ) ^ 2 := by
  rw [zetaMoebiusDirichletHead]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range D, (D + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnD : n < D := Finset.mem_range.mp hn
      have hp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hl : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_natCast_nonneg _
      have he : Real.exp (-s.re * Real.log (n + 1 : ℕ)) ≤ (n + 1 : ℕ) := by
        calc
          _ ≤ Real.exp (Real.log (n + 1 : ℕ)) := Real.exp_le_exp.mpr (by nlinarith)
          _ = _ := Real.exp_log hp
      have hm : ‖((μ (n + 1) : ℤ) : ℂ)‖ ≤ 1 := by
        simpa only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] using abs_real_moebius_le_one (n + 1)
      rw [norm_mul, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, neg_mul]
      have h := mul_le_mul hm he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
      simp only [one_mul] at h
      simpa only [neg_mul] using h.trans
        (show ((n + 1 : ℕ) : ℝ) ≤ D + 1 by exact_mod_cast (show n + 1 ≤ D + 1 by omega))
    _ ≤ _ := by simp; nlinarith [sq_nonneg (D : ℝ)]

/-- The first pole coefficient of the actual finite head has the same
quadratic cutoff budget, including cutoff zero. -/
theorem norm_deriv_zetaMoebiusDirichletHead_one_le (D : ℕ) :
    ‖deriv (zetaMoebiusDirichletHead D) 1‖ ≤ (D + 1 : ℝ) ^ 2 := by
  have hb (s : ℂ) (hs : s ∈ sphere (1 : ℂ) 1) : ‖zetaMoebiusDirichletHead D s‖ ≤ (D + 1 : ℝ) ^ 2 := by
    have hn : ‖s - 1‖ = 1 := mem_sphere_iff_norm.mp hs
    have hr := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re, hn] at hr
    exact norm_zetaMoebiusDirichletHead_le D (by linarith [(abs_le.mp hr).1])
  have h := norm_signedTaylorMoment_le (by norm_num : (0 : ℝ) < 1)
    (differentiable_zetaMoebiusDirichletHead D).diffContOnCl hb 1
  simpa [signedTaylorMoment] using h

/-- The exact entire remainder after removing both pole coefficients
from the finite Möbius head times `-zeta'`. -/
def zetaMoebiusHeadRegular (D : ℕ) (s : ℂ) : ℂ :=
  -zetaMoebiusDirichletHead D s * deriv riemannZeta₀ s +
    dslope (dslope (zetaMoebiusDirichletHead D) 1) 1 s

private theorem differentiable_dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 1) := by
  rw [← differentiableOn_univ, Complex.differentiableOn_dslope (s := Set.univ) Filter.univ_mem]
  exact hf.differentiableOn

/-- Both apparent singularities in the regular remainder are genuinely
removed; its analyticity holds also at the pole point itself. -/
theorem differentiable_zetaMoebiusHeadRegular (D : ℕ) : Differentiable ℂ (zetaMoebiusHeadRegular D) := by
  exact ((differentiable_zetaMoebiusDirichletHead D).neg.mul differentiable_riemannZeta₀.deriv).add
    (differentiable_dslope_entire (differentiable_dslope_entire (differentiable_zetaMoebiusDirichletHead D)))

/-- Exact pole decomposition for the actual signed convolution head.
The simple pole coefficient is the derivative of the same finite prefix,
so it cannot be dropped while retaining only its value at one. -/
theorem zetaMoebiusHead_mul_neg_deriv_eq (D : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaMoebiusDirichletHead D s * (-deriv riemannZeta s) =
      zetaMoebiusHeadRegular D s + zetaMoebiusDirichletHead D 1 * ((s - 1)⁻¹) ^ 2 +
        deriv (zetaMoebiusDirichletHead D) 1 * (s - 1)⁻¹ := by
  rw [zetaMoebiusHeadRegular, deriv_riemannZeta_eq_neg_inv_sub_sq_add hs]
  simp only [dslope_of_ne _ hs, dslope_same, slope_def_field]
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

private theorem regular_norm_le (D : ℕ) {s : ℂ} (hs : -1 ≤ s.re)
    (hgap : (1 / 2 : ℝ) ≤ ‖s - 1‖) {C : ℝ} (hC : ‖deriv riemannZeta₀ s‖ ≤ C) :
    ‖zetaMoebiusHeadRegular D s‖ ≤ (C + 10) * (D + 1 : ℝ) ^ 2 := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hgap
  have hi : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by simpa using hgap)
  have hi2 : ‖((s - 1)⁻¹) ^ 2‖ ≤ 4 := by rw [norm_pow]; nlinarith [norm_nonneg ((s - 1)⁻¹)]
  have hhead := norm_zetaMoebiusDirichletHead_le D hs
  have hpole := norm_zetaMoebiusDirichletHead_le D (s := 1) (by norm_num)
  have hder := norm_deriv_zetaMoebiusDirichletHead_one_le D
  have hz : ‖deriv riemannZeta s‖ ≤ 4 + C := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs1]
    exact (norm_add_le _ _).trans (by simpa only [norm_neg] using add_le_add hi2 hC)
  have hc0 : 0 ≤ C := (norm_nonneg _).trans hC
  have he := zetaMoebiusHead_mul_neg_deriv_eq D hs1
  have hre : zetaMoebiusHeadRegular D s =
      zetaMoebiusDirichletHead D s * (-deriv riemannZeta s) -
        zetaMoebiusDirichletHead D 1 * ((s - 1)⁻¹) ^ 2 -
          deriv (zetaMoebiusDirichletHead D) 1 * (s - 1)⁻¹ := by linear_combination -he
  rw [hre]
  have h1 : ‖zetaMoebiusDirichletHead D s * (-deriv riemannZeta s)‖ ≤ (D + 1 : ℝ) ^ 2 * (4 + C) := by
    rw [norm_mul, norm_neg]
    exact mul_le_mul hhead hz (norm_nonneg _) (by positivity)
  have h2 : ‖zetaMoebiusDirichletHead D 1 * ((s - 1)⁻¹) ^ 2‖ ≤ (D + 1 : ℝ) ^ 2 * 4 := by
    rw [norm_mul]
    exact mul_le_mul hpole hi2 (norm_nonneg _) (by positivity)
  have h3 : ‖deriv (zetaMoebiusDirichletHead D) 1 * (s - 1)⁻¹‖ ≤ (D + 1 : ℝ) ^ 2 * 2 := by
    rw [norm_mul]
    exact mul_le_mul hder hi (norm_nonneg _) (by positivity)
  have h := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) h3)
  exact h.trans_eq (by ring)

private theorem exists_head_circle (y : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ R ≤ 2 ∧ ∀ s ∈ sphere (3 / 2 + I * (y : ℂ)) R,
      -1 ≤ s.re ∧ (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  let c : ℂ := 3 / 2 + I * y
  have hre : c.re = (3 / 2 : ℝ) := by dsimp [c]; norm_num
  have hreal {R : ℝ} (hR : R ≤ 2) {s : ℂ} (hs : s ∈ sphere c R) : -1 ≤ s.re := by
    have hn := mem_sphere_iff_norm.mp hs
    have hr := Complex.abs_re_le_norm (s - c)
    rw [Complex.sub_re, hre, hn] at hr
    linarith [(abs_le.mp hr).1]
  by_cases hc : (3 / 2 : ℝ) ≤ ‖c - 1‖
  · refine ⟨1, le_rfl, by norm_num, ?_⟩
    intro s hs
    refine ⟨hreal (by norm_num) hs, ?_⟩
    have hn : ‖c - s‖ = 1 := by rw [norm_sub_rev]; exact mem_sphere_iff_norm.mp hs
    have ht := norm_add_le (c - s) (s - 1)
    rw [show c - s + (s - 1) = c - 1 by ring, hn] at ht
    linarith
  · refine ⟨2, by norm_num, le_rfl, ?_⟩
    intro s hs
    refine ⟨hreal le_rfl hs, ?_⟩
    have hn := mem_sphere_iff_norm.mp hs
    have ht := norm_sub_le (s - 1) (c - 1)
    rw [show s - 1 - (c - 1) = s - c by ring, hn] at ht
    linarith

/-- One actual Cauchy circle and one constant control every finite
Möbius head and every moment order. Both pole coefficients have been
removed before this estimate; no cancellation assumption is used. -/
theorem exists_zetaMoebiusHeadRegular_moment_bound (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D n : ℕ,
      ‖signedTaylorMoment n (zetaMoebiusHeadRegular D) (3 / 2 + I * y)‖ ≤ C * (D + 1 : ℝ) ^ 2 := by
  let c : ℂ := 3 / 2 + I * y
  obtain ⟨C, hC⟩ := ((isCompact_closedBall c 2).image
    differentiable_riemannZeta₀.deriv.continuous).isBounded.exists_norm_le
  have hc : ‖deriv riemannZeta₀ c‖ ≤ C := hC _ ⟨c, mem_closedBall_self (by norm_num), rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hc
  obtain ⟨R, hR1, hR2, hcircle⟩ := exists_head_circle y
  refine ⟨C + 10, by linarith, ?_⟩
  intro D n
  have hb (s : ℂ) (hs : s ∈ sphere c R) : ‖zetaMoebiusHeadRegular D s‖ ≤ (C + 10) * (D + 1 : ℝ) ^ 2 := by
    obtain ⟨hre, hgap⟩ := hcircle s hs
    apply regular_norm_le D hre hgap
    apply hC
    refine ⟨s, ?_, rfl⟩
    exact (closedBall_subset_closedBall hR2) (sphere_subset_closedBall hs)
  have h := norm_signedTaylorMoment_le (zero_lt_one.trans_le hR1)
    (differentiable_zetaMoebiusHeadRegular D).diffContOnCl hb n
  apply h.trans
  exact div_le_self (by positivity) (one_le_pow₀ hR1)

/-- The actual finite Möbius head of the integer logarithmic series,
before any of its pole or regular contributions are estimated. -/
def zetaMoebiusHeadMoment (D n : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment n (fun z ↦ zetaMoebiusDirichletHead D z * (-deriv riemannZeta z)) s

/-- All signed moment contributions of the finite convolution head,
including the value and derivative of its prefix at the pole. -/
theorem zetaMoebiusHeadMoment_eq (D n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaMoebiusHeadMoment D n s =
      signedTaylorMoment n (zetaMoebiusHeadRegular D) s +
        zetaMoebiusDirichletHead D 1 * (((n + 1 : ℕ) : ℂ) * ((s - 1)⁻¹) ^ (n + 2)) +
          deriv (zetaMoebiusDirichletHead D) 1 * ((s - 1)⁻¹) ^ (n + 1) := by
  have he : (fun z ↦ zetaMoebiusDirichletHead D z * (-deriv riemannZeta z)) =ᶠ[𝓝 s]
      (fun z ↦ zetaMoebiusHeadRegular D z + zetaMoebiusDirichletHead D 1 * ((z - 1)⁻¹) ^ 2 +
        deriv (zetaMoebiusDirichletHead D) 1 * (z - 1)⁻¹) := by
    filter_upwards [compl_singleton_mem_nhds hs] with z hz
    exact zetaMoebiusHead_mul_neg_deriv_eq D hz
  have hreg := (differentiable_zetaMoebiusHeadRegular D).analyticAt (z := s)
  have hinv : AnalyticAt ℂ (fun z : ℂ ↦ (z - 1)⁻¹) s :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs)
  have hp2 : AnalyticAt ℂ (fun z ↦ zetaMoebiusDirichletHead D 1 * ((z - 1)⁻¹) ^ 2) s :=
    analyticAt_const.mul (hinv.pow 2)
  have hp1 : AnalyticAt ℂ (fun z ↦ deriv (zetaMoebiusDirichletHead D) 1 * (z - 1)⁻¹) s :=
    analyticAt_const.mul hinv
  have hboth : AnalyticAt ℂ (fun z ↦ zetaMoebiusHeadRegular D z +
      zetaMoebiusDirichletHead D 1 * ((z - 1)⁻¹) ^ 2) s := hreg.add hp2
  rw [zetaMoebiusHeadMoment, signedTaylorMoment_congr n he,
    signedTaylorMoment_add n hboth hp1, signedTaylorMoment_add n hreg hp2,
    signedTaylorMoment_const_mul, signedTaylorMoment_const_mul,
    signedTaylorMoment_inv_sub_one_sq n hs, signedTaylorMoment_inv_sub_one]

/-- Cancelling both entries of the pole jet leaves exactly the regular
part of each literal finite Möbius convolution head. -/
theorem zetaMoebiusHeadFilter_eq_regular (p : Polynomial ℂ) (D N : ℕ) {s : ℂ} (hs : s ≠ 1)
    (hp : p.eval (s - 1)⁻¹ = 0) (hp' : p.derivative.eval (s - 1)⁻¹ = 0) :
    zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusHeadMoment D n s) N =
      zetaMomentSequenceFilter p (fun n ↦ signedTaylorMoment n (zetaMoebiusHeadRegular D) s) N := by
  have he : zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusHeadMoment D n s) N =
      zetaMomentSequenceFilter p (fun n ↦ signedTaylorMoment n (zetaMoebiusHeadRegular D) s) N +
        zetaMoebiusDirichletHead D 1 * zetaMomentSequenceFilter p
          (fun n ↦ ((n + 1 : ℕ) : ℂ) * ((s - 1)⁻¹) ^ (n + 2)) N +
        deriv (zetaMoebiusDirichletHead D) 1 * zetaMomentSequenceFilter p
          (fun n ↦ ((s - 1)⁻¹) ^ (n + 1)) N := by
    simp only [zetaMomentSequenceFilter, Polynomial.sum, zetaMoebiusHeadMoment_eq D _ hs,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, zetaMomentSequenceFilter_doublePole, zetaMomentSequenceFilter_geometric, hp, hp']
  simp

/-- An independent quadratic divisor-cutoff budget for every moment
order of every filter that kills the double pole. This is a bound on the
actual finite Möbius convolution head, not an assumed arithmetic premise. -/
theorem exists_zetaMoebiusHeadFilter_bound (y : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N : ℕ),
      p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0 →
      p.derivative.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0 →
      ‖zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusHeadMoment D n (3 / 2 + I * y)) N‖ ≤
        C * (D + 1 : ℝ) ^ 2 * ∑ k ∈ p.support, ‖p.coeff k‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaMoebiusHeadRegular_moment_bound y
  refine ⟨C, hC, ?_⟩
  intro p D N hp hp'
  have hs : (3 / 2 + I * (y : ℂ)) ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  rw [zetaMoebiusHeadFilter_eq_regular p D N hs hp hp', zetaMomentSequenceFilter, Polynomial.sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (C * (D + 1 : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound D (N + k)) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring

end

end RiemannGaussian
