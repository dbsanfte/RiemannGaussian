/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The nonzero alternating bulk channel of the lag spectrum

Use the entire cosine-zeta continuation, rather than a divergent ordinary
eta sum on Re(z)=0. The boundary channel is nonzero at every nonzero height.
This lemma alone does not identify the literal carry phase response.
-/

namespace RiemannGaussian.SuzukiCarryPhaseEta
noncomputable section
open Complex Filter Set
open scoped BigOperators Topology

/-- Entire continuation of the alternating Dirichlet eta function. -/
def eta (z : ℂ) : ℂ := -HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) z

private theorem half_ne_zero : ((1/2 : ℝ) : UnitAddCircle) ≠ 0 := by
  intro hz
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  have he : (n : ℝ) = 1/2 := by simpa using hn
  have h01 : (0 : ℤ) < n ∧ n < 1 := by
    constructor
    · exact_mod_cast (show (0 : ℝ) < (n : ℝ) by linarith)
    · exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

theorem analytic_eta : AnalyticOnNhd ℂ eta univ := by
  exact (HurwitzZeta.differentiable_cosZeta_of_ne_zero half_ne_zero).neg.differentiableOn.analyticOnNhd isOpen_univ

set_option maxHeartbeats 1000000 in
private theorem cosZeta_eq_neg_paired {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) s = -pairedEtaCore s := by
  let f : ℕ → ℂ := fun n => (-1 : ℂ)^n/(n : ℂ)^s
  have hf : HasSum f (HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) s) := by
    convert HurwitzZeta.hasSum_nat_cosZeta (1/2 : ℝ) hs using 1
    funext n
    rw [show 2*Real.pi*(1/2 : ℝ)*(n : ℝ) = (n : ℝ)*Real.pi by ring,
      Real.cos_nat_mul_pi]
    simp only [f, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  have hf0 : f 0 = 0 := by simp [f, Complex.zero_cpow (ne_zero_of_one_lt_re hs)]
  have hshift : HasSum (fun n : ℕ => f (n+1))
      (HurwitzZeta.cosZeta ((1/2 : ℝ) : UnitAddCircle) s) := by
    simpa [hf0] using (hasSum_nat_add_iff' 1).mpr hf
  have he := hshift.summable.comp_injective (show Function.Injective (fun n : ℕ => 2*n) by
    intro n m he; dsimp at he; omega)
  have ho := hshift.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2*n+1) by intro n m he; dsimp at he; omega)
  have hp : (∑' n : ℕ, (f (2*n+1)+f (2*n+1+1))) = -pairedEtaCore s := by
    rw [pairedEtaCore, ← tsum_neg]
    apply tsum_congr
    intro n
    simp only [f, pairedEtaCoreSummand]
    rw [show 2*n+1+1 = 2*n+2 by omega]
    simp only [pow_add, pow_mul, pow_one,
      pow_two, mul_one, mul_neg, Complex.cpow_neg,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    push_cast
    ring
  exact ((HasSum.even_add_odd he.hasSum ho.hasSum).unique hshift).symm.trans
    ((he.tsum_add ho).symm.trans hp)

theorem eta_eq_factor {s : ℂ} (hs : s ≠ 1) :
    eta s = (1-2*(2 : ℂ)^(-s))*riemannZeta s := by
  have ha : AnalyticOnNhd ℂ eta {1}ᶜ := analytic_eta.mono (subset_univ _)
  have hb : AnalyticOnNhd ℂ (fun s : ℂ =>
      (1-2*(2 : ℂ)^(-s))*riemannZeta s) {1}ᶜ := by
    apply AnalyticOnNhd.mul _ analyticOn_riemannZeta
    intro z _
    exact analyticAt_const.sub (analyticAt_const.mul
      ((analyticAt_const.cpow analyticAt_id.neg (Or.inl (by norm_num)))))
  have hconn := (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have he := ha.eqOn_of_preconnected_of_eventuallyEq hb hconn
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    (eventuallyEq_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num : 1 < (2 : ℂ).re))
      (fun z hz => by
        rw [eta, cosZeta_eq_neg_paired hz, neg_neg,
          pairedEtaCore_eq_factor_riemannZeta_of_one_lt_re hz]))
  exact he hs

theorem zeta_ne_zero_on_zero_line {z : ℂ} (hz : z.re = 0) (hi : z.im ≠ 0) :
    riemannZeta z ≠ 0 := by
  have hn (n : ℕ) : z ≠ -(n : ℂ) := by
    intro he
    exact hi (by simpa using congrArg Complex.im he)
  have hn1 : z ≠ 1 := by intro he; exact hi (by simpa using congrArg Complex.im he)
  intro hzero
  have h := riemannZeta_one_sub hn hn1
  rw [hzero, mul_zero] at h
  exact riemannZeta_ne_zero_of_one_le_re
    (by simp only [Complex.sub_re, Complex.one_re, hz]; norm_num) h

/-- There is no exceptional nonzero height for the leading alternating
channel. In particular, no short-height numerical certificate is needed. -/
theorem eta_ne_zero_on_zero_line {z : ℂ} (hz : z.re = 0) (hi : z.im ≠ 0) :
    eta z ≠ 0 := by
  have hn1 : z ≠ 1 := by intro he; exact hi (by simpa using congrArg Complex.im he)
  rw [eta_eq_factor hn1]
  apply mul_ne_zero _ (zeta_ne_zero_on_zero_line hz hi)
  intro he
  have heq : 2*(2 : ℂ)^(-z) = 1 := by linear_combination -he
  have hn := congrArg norm heq
  have hp : ‖(2 : ℂ)^(-z)‖ = 1 := by
    simpa [hz] using (Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ))
      (y := -z) (by norm_num))
  norm_num [norm_mul, hp] at hn

end
end RiemannGaussian.SuzukiCarryPhaseEta
