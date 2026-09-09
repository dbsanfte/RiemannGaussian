/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusTailConvolution

/-!
# Zero multiplicity transported to a moving composite Möbius tail

All factorial moments and polynomial filters of the large-divisor
convolution are genuine convergent arithmetic sums. The full pole-jet
filter makes its exponentially growing complementary head negligible.
Consequently the composite tail carries the selected zero's full complex
source. An independent signed lower estimate on this tail remains open.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

private theorem logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Real.log n : ℂ) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, ← Complex.natCast_log]
    ring

/-- Every absolutely convergent Dirichlet series has the literal
factorial logarithmic moments, with no loss of coefficient phase.
The zero-index hypothesis aligns the exponential kernel with `LSeries.term`. -/
theorem hasSum_signedTaylorMoment_LSeries (f : ℕ → ℂ) (hf0 : f 0 = 0) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv f < s.re) (k : ℕ) :
    HasSum (fun n : ℕ ↦ f n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (signedTaylorMoment k (LSeries f) s) := by
  have hval : signedTaylorMoment k (LSeries f) s =
      LSeries (LSeries.logMul^[k] f) s / (k.factorial : ℂ) := by
    rw [signedTaylorMoment, LSeries_iteratedDeriv k hs]
    have hsign : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    calc
      _ = ((-1 : ℂ) ^ k * (-1) ^ k) * LSeries (LSeries.logMul^[k] f) s / (k.factorial : ℂ) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [hval]
  have h := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (f := LSeries.logMul^[k] f) (s := s) (by simpa using hs)
  apply (h.hasSum.div_const (k.factorial : ℂ)).congr_fun
  intro n
  by_cases hn : n = 0
  · subst n
    simp [hf0]
  · rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
      ← Complex.natCast_log]
    simp only [div_eq_mul_inv, ← Complex.exp_neg]
    unfold zetaPrimeFeature
    rw [mul_comm (Real.log n : ℂ) s]
    ring

/-- Absolute convergence of the genuine large-divisor logarithmic
convolution throughout the Euler half-plane, for every finite cutoff. -/
theorem abscissaOfAbsConv_zetaMoebiusLogTail_le_one (D : ℕ) :
    LSeries.abscissaOfAbsConv (zetaMoebiusLogTailCoefficient D) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact (LSeriesHasSum_zetaMoebiusLogTail D (by simpa using hy)).LSeriesSummable

/-- The full signed Taylor moment of the literal large-divisor convolution. -/
def zetaMoebiusLogTailMoment (D n : ℕ) (s : ℂ) : ℂ :=
  signedTaylorMoment n (zetaMoebiusLogTail D) s

/-- Each tail moment is an actual convergent sum over the signed
divisor-product coefficients, rather than a totalized infinite sum. -/
theorem hasSum_zetaMoebiusLogTailMoment (D k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ zetaMoebiusLogTailCoefficient D n *
      ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * zetaPrimeFeature s n)
      (zetaMoebiusLogTailMoment D k s) := by
  have he : zetaMoebiusLogTail D =ᶠ[𝓝 s] LSeries (zetaMoebiusLogTailCoefficient D) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs] with z hz
    exact (LSeriesHasSum_zetaMoebiusLogTail D hz).LSeries_eq.symm
  rw [zetaMoebiusLogTailMoment, signedTaylorMoment_congr k he]
  exact hasSum_signedTaylorMoment_LSeries _ (by simp [zetaMoebiusLogTailCoefficient])
    (lt_of_le_of_lt (abscissaOfAbsConv_zetaMoebiusLogTail_le_one D) (by exact_mod_cast hs)) k

/-- The exact polynomial filter of the moving arithmetic tail. -/
def zetaMoebiusLogTailFilter (p : Polynomial ℂ) (D N : ℕ) (s : ℂ) : ℂ :=
  zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusLogTailMoment D n s) N

/-- The complete filter is a single convergent complex arithmetic sum.
Divisor signs and all logarithmic phase cross terms stay coupled. -/
theorem hasSum_zetaMoebiusLogTailFilter (p : Polynomial ℂ) (D N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ zetaMoebiusLogTailCoefficient D n * zetaPrimeFeature s n *
      ∑ k ∈ p.support, p.coeff k * ((Real.log n : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)))
      (zetaMoebiusLogTailFilter p D N s) := by
  have h := hasSum_sum (s := p.support) (fun k _ ↦
    (hasSum_zetaMoebiusLogTailMoment D (N + k) hs).mul_left (p.coeff k))
  apply h.congr_fun
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The identical convergent filter can be restricted to composite
indices at least twice the first retained divisor; nothing is estimated
or discarded in this support restriction. -/
theorem hasSum_zetaMoebiusLogTailFilter_composite (p : Polynomial ℂ) (D N : ℕ)
    (hD : 1 ≤ D) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ if 2 * (D + 1) ≤ n ∧ ¬n.Prime then
      zetaMoebiusLogTailCoefficient D n * zetaPrimeFeature s n *
        ∑ k ∈ p.support, p.coeff k * ((Real.log n : ℂ) ^ (N + k) / ((N + k).factorial : ℂ))
      else 0) (zetaMoebiusLogTailFilter p D N s) := by
  apply (hasSum_zetaMoebiusLogTailFilter p D N hs).congr_fun
  intro n
  by_cases hn : 2 * (D + 1) ≤ n
  · by_cases hp : n.Prime
    · simp [hp, zetaMoebiusLogTailCoefficient_prime D hD hp]
    · simp [hn, hp]
  · simp [hn, zetaMoebiusLogTailCoefficient_eq_zero_of_lt D n (lt_of_not_ge hn)]

/-- The negative logarithmic derivative splits exactly into the finite
head and the literal logarithmic Möbius tail. -/
theorem neg_logDeriv_riemannZeta_eq_moebiusHead_add_tail (D : ℕ) (s : ℂ) :
    -logDeriv riemannZeta s = zetaMoebiusDirichletHead D s * (-deriv riemannZeta s) +
      zetaMoebiusLogTail D s := by
  simp only [logDeriv, Pi.div_apply, zetaMoebiusLogTail, div_eq_mul_inv]
  ring

/-- Every higher moment keeps the exact head-tail decomposition, with
analyticity and zeta zero avoidance discharged in the Euler half-plane. -/
theorem zetaPrimeLogMoment_eq_moebiusHead_add_tail (D n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeLogMoment n s = zetaMoebiusHeadMoment D n s + zetaMoebiusLogTailMoment D n s := by
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    simp [h] at hs)
  have hh := (differentiable_zetaMoebiusDirichletHead D).analyticAt (z := s)
  have hhead : AnalyticAt ℂ (fun z ↦ zetaMoebiusDirichletHead D z * (-deriv riemannZeta z)) s :=
    hh.mul hz.deriv.neg
  have htail : AnalyticAt ℂ (zetaMoebiusLogTail D) s :=
    ((hz.inv (riemannZeta_ne_zero_of_one_lt_re hs)).sub hh).mul hz.deriv.neg
  have he : (fun z ↦ -logDeriv riemannZeta z) = (fun z ↦
      zetaMoebiusDirichletHead D z * (-deriv riemannZeta z) + zetaMoebiusLogTail D z) :=
    funext (neg_logDeriv_riemannZeta_eq_moebiusHead_add_tail D)
  rw [zetaPrimeLogMoment, he, signedTaylorMoment_add n hhead htail]
  rfl

/-- Arbitrary polynomial filters preserve the complete arithmetic split. -/
theorem zetaPrimeLogFilter_eq_moebiusHead_add_tail (p : Polynomial ℂ) (D N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaPrimeLogFilter p N s =
      zetaMomentSequenceFilter p (fun n ↦ zetaMoebiusHeadMoment D n s) N +
        zetaMoebiusLogTailFilter p D N s := by
  simp only [zetaPrimeLogFilter, zetaMoebiusLogTailFilter, zetaMomentSequenceFilter,
    Polynomial.sum, zetaPrimeLogMoment_eq_moebiusHead_add_tail D _ hs, mul_add,
    Finset.sum_add_distrib]

/-- A quantitative independent bound on replacing the complete prime
filter by its actual large-divisor tail. The source-normalized error is
geometric even though the removed divisor head grows exponentially. -/
theorem exists_zetaRightHalfPoleJetTail_error_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        (zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) -
          zetaMoebiusLogTailFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
            (3 / 2 + I * rho.1.im))‖ ≤ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_zetaRightHalfPoleJetHead_bound rho hrho
  refine ⟨C, hC, fun N ↦ ?_⟩
  rw [zetaPrimeLogFilter_eq_moebiusHead_add_tail _ _ _ (by norm_num), add_sub_cancel_right]
  exact hb N

/-- For every hypothetical right-half zero, the literal tail beyond an
exponentially growing divisor cutoff retains its full negative multiplicity.
The head's decay is independently proved, not assumed in this theorem. -/
theorem tendsto_zetaRightHalfPoleJetTail (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMoebiusLogTailFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_zetaRightHalfPoleJetFilter rho hrho).sub (tendsto_zetaRightHalfPoleJetHead rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [zetaPrimeLogFilter_eq_moebiusHead_add_tail _ _ _ (by norm_num), mul_add, add_sub_cancel_left]

/-- The signed real tail source has the same full multiplicity limit. -/
theorem tendsto_zetaRightHalfPoleJetTail_re (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (zetaMoebiusLogTailFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)).re) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] using
    (Complex.continuous_re.tendsto _).comp (tendsto_zetaRightHalfPoleJetTail rho hrho)

/-- The selected divisor cutoff is genuinely cofinal for every
hypothetical zero right of the critical line. -/
theorem tendsto_zetaRightHalfPoleJetCutoff (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re))) atTop atTop := by
  apply tendsto_zetaMoebiusGeometricCutoff
  exact one_lt_zetaMoebiusHeadGrowth (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)

/-- The full selected-zero limit is an explicit sum over composite
products beyond the growing divisor head. All convergence, cutoff, and
source-preservation hypotheses are discharged for this literal carrier. -/
theorem tendsto_zetaRightHalfPoleJetTail_compositeSum (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let u : ℝ := 3 / 2 - rho.1.re
    let p := zetaRightHalfPoleJetFilter rho hrho
    let D := zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth u)
    Tendsto (fun N : ℕ ↦ (u : ℂ) ^ (N + 1) * ∑' n : ℕ,
      if 2 * (D N + 1) ≤ n ∧ ¬n.Prime then
        zetaMoebiusLogTailCoefficient (D N) n * zetaPrimeFeature (3 / 2 + I * rho.1.im) n *
          ∑ k ∈ p.support, p.coeff k * ((Real.log n : ℂ) ^ (N + k) / ((N + k).factorial : ℂ))
      else 0) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  dsimp only
  apply (tendsto_zetaRightHalfPoleJetTail rho hrho).congr'
  filter_upwards [(tendsto_zetaRightHalfPoleJetCutoff rho hrho).eventually_ge_atTop 1] with N hN
  rw [(hasSum_zetaMoebiusLogTailFilter_composite _ _ N hN (by norm_num)).tsum_eq]

/-- Eventually the actual tail has a negative real source at least
half the selected zero's full multiplicity scale. An independent opposite
arithmetic estimate is the remaining obligation. -/
theorem zetaRightHalfPoleJetTail_eventually_negative (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      (zetaMoebiusLogTailFilter (zetaRightHalfPoleJetFilter rho hrho)
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) N
        (3 / 2 + I * rho.1.im)).re <
          -(analyticZetaZeroMultiplicity rho : ℝ) / (2 * (3 / 2 - rho.1.re) ^ (N + 1)) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_zetaRightHalfPoleJetTail_re rho hrho).eventually
    (gt_mem_nhds (by linarith : -(analyticZetaZeroMultiplicity rho : ℝ) <
      -(analyticZetaZeroMultiplicity rho : ℝ) / 2))
  filter_upwards [h] with N hN
  rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hu _))]
  nlinarith

end

end RiemannGaussian
