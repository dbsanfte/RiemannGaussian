/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinRate

/-!
# The asymmetric cofinal determinant gate

The finite/continuum passage is unconditional. The fourth-order expansion
and its nonzero wedge remain explicit analytic premises; they are not
arithmetic estimates or conclusions of numerical quadrature.
-/

namespace RiemannGaussian.SuzukiCarryDeterminantGate
noncomputable section
open Complex Filter Set
open SuzukiCarryPhaseCode SuzukiCarryMellinRate
open scoped Topology

/-- The two contrasts used by the 0,tau,2tau code. -/
def contrastDet (f g : ℝ → ℂ) (tau : ℝ) : ℂ :=
  (f tau-f 0)*(g (2*tau)-g 0)-(f (2*tau)-f 0)*(g tau-g 0)

/-- The proposed even fourth-order jet. -/
def evenJet (A B C : ℂ) (tau : ℝ) : ℂ := A+B*(tau : ℂ)^2+C*(tau : ℂ)^4

/-- Exact leading coefficient, including the factor twelve and its sign. -/
theorem contrastDet_evenJet (A B C a b c : ℂ) (tau : ℝ) :
    contrastDet (evenJet A B C) (evenJet a b c) tau =
      12*(B*c-C*b)*(tau : ℂ)^6 := by
  simp only [contrastDet, evenJet, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, add_zero,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The actual remainder, with no fitted coefficients or discarded terms. -/
def jetRemainder (f : ℝ → ℂ) (B C : ℂ) (tau : ℝ) : ℂ :=
  (f tau-f 0-B*(tau : ℂ)^2-C*(tau : ℂ)^4)/(tau : ℂ)^4

/-- An even fourth-order expansion from the positive side. This is a
separate analytic proposition about the literal continuum response. -/
def FourthOrderExpansion (f : ℝ → ℂ) (B C : ℂ) : Prop :=
  Tendsto (jetRemainder f B C) (𝓝[>] (0 : ℝ)) (𝓝 0)

private theorem reconstruct {f : ℝ → ℂ} (B C : ℂ) {tau : ℝ} (ht : tau ≠ 0) :
    f tau-f 0 = B*(tau : ℂ)^2+C*(tau : ℂ)^4+
      jetRemainder f B C tau*(tau : ℂ)^4 := by
  unfold jetRemainder
  have hc : (tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  field_simp
  ring

/-- The full remainder identity. No asymptotic cancellation is silently
substituted into the source determinant. -/
theorem normalized_contrastDet_eq {f g : ℝ → ℂ} (B C b c : ℂ)
    {tau : ℝ} (ht : tau ≠ 0) :
    contrastDet f g tau/(tau : ℂ)^6 = 12*(B*c-C*b)+
      B*(16*jetRemainder g b c (2*tau)-4*jetRemainder g b c tau)+
      b*(4*jetRemainder f B C tau-16*jetRemainder f B C (2*tau))+
      16*(tau : ℂ)^2*((C+jetRemainder f B C tau)*(c+jetRemainder g b c (2*tau))-
        (C+jetRemainder f B C (2*tau))*(c+jetRemainder g b c tau)) := by
  have h2 : 2*tau ≠ 0 := mul_ne_zero (by norm_num) ht
  unfold contrastDet
  rw [reconstruct (f := f) B C ht, reconstruct (f := f) B C h2,
    reconstruct (f := g) b c ht, reconstruct (f := g) b c h2]
  have hc : (tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  push_cast
  field_simp
  ring

private theorem tendsto_twice :
    Tendsto (fun tau : ℝ => 2*tau) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous (fun tau : ℝ => 2*tau) := by fun_prop
    simpa using hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with tau ht
    change 0 < 2*tau
    exact mul_pos (by norm_num) ht

/-- The requested leading term follows from the two expansions. The
expansion premises must be proved for F itself before this gate is passed. -/
theorem tendsto_normalized_contrastDet {f g : ℝ → ℂ} {B C b c : ℂ}
    (hf : FourthOrderExpansion f B C) (hg : FourthOrderExpansion g b c) :
    Tendsto (fun tau : ℝ => contrastDet f g tau/(tau : ℂ)^6)
      (𝓝[>] (0 : ℝ)) (𝓝 (12*(B*c-C*b))) := by
  have hf2 := hf.comp tendsto_twice
  have hg2 := hg.comp tendsto_twice
  have ht : Tendsto (fun tau : ℝ => (tau : ℂ)^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun tau : ℝ => (tau : ℂ)^2) := by fun_prop
    simpa using (hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)))
  have hlim := ((((tendsto_const_nhds (x := 12*(B*c-C*b))).add
    (((hg2.const_mul 16).sub (hg.const_mul 4)).const_mul B)).add
      (((hf.const_mul 4).sub (hf2.const_mul 16)).const_mul b)).add
        ((ht.mul ((((hf.const_add C).mul (hg2.const_add c)).sub
          ((hf2.const_add C).mul (hg.const_add c))))).const_mul 16))
  simp only [mul_zero, sub_self, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with tau htau
  simpa only [Function.comp_apply, mul_assoc] using
    (normalized_contrastDet_eq (f := f) (g := g) B C b c (ne_of_gt htau)).symm

/-- Any nonzero wedge supplies some fixed positive modulation. A universal
choice is unnecessary and no finite probe is used by this theorem. -/
theorem exists_positive_contrastDet_ne_zero {f g : ℝ → ℂ} {B C b c : ℂ}
    (hf : FourthOrderExpansion f B C) (hg : FourthOrderExpansion g b c)
    (hw : B*c-C*b ≠ 0) : ∃ tau : ℝ, 0 < tau ∧ contrastDet f g tau ≠ 0 := by
  have hn : 0 < ‖12*(B*c-C*b)‖ := norm_pos_iff.mpr (mul_ne_zero (by norm_num) hw)
  have he := (tendsto_normalized_contrastDet hf hg).norm.eventually
    (lt_mem_nhds (by linarith : ‖12*(B*c-C*b)‖/2 < ‖12*(B*c-C*b)‖))
  have hall : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), 0 < tau ∧ contrastDet f g tau ≠ 0 := by
    filter_upwards [he, self_mem_nhdsWithin] with tau hnorm hpos
    refine ⟨hpos, ?_⟩
    intro hz
    rw [hz, zero_div, norm_zero] at hnorm
    linarith
  exact hall.exists

theorem continuumDet_eq_contrast (p s : ℂ) (tau : ℝ) :
    continuumDet p s tau = contrastDet (continuumResponse p) (continuumResponse s) tau := by
  simp [continuumDet, sourceDet_eq_contrasts, contrastDet]

/-- A precise sufficient gate for the literal cofinal source bound. This
does not assert that every campaign height satisfies the wedge premise. -/
theorem exists_fixed_code_source_lower {p s B C b c : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re)
    (hf : FourthOrderExpansion (continuumResponse p) B C)
    (hg : FourthOrderExpansion (continuumResponse s) b c)
    (hw : B*c-C*b ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ continuumDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeDet H p s tau‖ := by
  obtain ⟨tau, ht, hd⟩ := exists_positive_contrastDet_ne_zero hf hg hw
  rw [← continuumDet_eq_contrast] at hd
  exact ⟨tau, ht, hd, eventually_nativeDet_source_lower hp hs hd⟩

end
end RiemannGaussian.SuzukiCarryDeterminantGate
