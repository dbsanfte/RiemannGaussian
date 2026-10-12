/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryExceptionalPhase

/-!
# A diagonal-free two-scale escape from quartic phase degeneracy

Each scale first uses a same-amplitude phase contrast. Only then are the
two scales pole-centered. The limiting determinant has the factor
`exp(p*log 2)-exp(s*log 2)`, which cannot vanish when the real parts differ.
This is a source gate, not an arithmetic smallness estimate.
-/

namespace RiemannGaussian.SuzukiCarryPhaseScaleGate
noncomputable section
open Complex Filter Set
open SuzukiCarryPhaseCode SuzukiCarryMellinRate SuzukiCarryMellinJet
open SuzukiCarryDeterminantGate
open scoped BigOperators Topology

/-- A phase contrast retains the same amplitude and physical support. -/
def nativeContrast (H : ℕ) (s : ℂ) (tau : ℝ) : ℂ :=
  Cmod H (tau/(H : ℝ)) s-Cmod H 0 s

/-- Its actual continuum limit. -/
def contrast (s : ℂ) (tau : ℝ) : ℂ :=
  continuumResponse s tau-continuumResponse s 0

/-- The four responses use phases 0,tau/H at H and 0,tau/(2H) at 2H. -/
def nativeScaleDet (H : ℕ) (p s : ℂ) (tau : ℝ) : ℂ :=
  nativeContrast (2*H) p tau*nativeContrast H s tau-
    nativeContrast H p tau*nativeContrast (2*H) s tau

/-- No fourth-order wedge occurs in this limiting source factor. -/
def scaleDet (p s : ℂ) (tau : ℝ) : ℂ :=
  (Complex.exp (p*(Real.log 2 : ℂ))-Complex.exp (s*(Real.log 2 : ℂ)))*
    contrast p tau*contrast s tau

/-- The two phase coefficients at each scale sum to zero separately. -/
def scaleCode (H : ℕ) (p : ℂ) (tau : ℝ) : Fin 4 → ℂ :=
  ![-nativeContrast (2*H) p tau, nativeContrast (2*H) p tau,
    nativeContrast H p tau, -nativeContrast H p tau]

/-- The literal four complete power responses use the two native lengths;
no continuum coefficient is substituted into this code. -/
def fourResponses (H : ℕ) (s : ℂ) (tau : ℝ) : Fin 4 → ℂ :=
  ![Cmod H 0 s, Cmod H (tau/(H : ℝ)) s,
    Cmod (2*H) 0 s, Cmod (2*H) (tau/(2*H : ℕ)) s]

theorem scaleCode_cancel_diagonal (H : ℕ) (p : ℂ) (tau : ℝ) (A B : ℂ) :
    ∑ j : Fin 4, scaleCode H p tau j*(if j.val < 2 then A else B) = 0 := by
  simp [Fin.sum_univ_four, scaleCode]

/-- The two independent diagonal constraints and the pole constraint hold
exactly at finite H, including proper prime-power contributions. -/
theorem scaleCode_response (H : ℕ) (p s : ℂ) (tau : ℝ) :
    (∑ j : Fin 4, scaleCode H p tau j*fourResponses H s tau j) =
      nativeScaleDet H p s tau := by
  simp [Fin.sum_univ_four, scaleCode, fourResponses, nativeScaleDet, nativeContrast]
  ring

theorem scaleCode_cancel_pole (H : ℕ) (p : ℂ) (tau : ℝ) :
    (∑ j : Fin 4, scaleCode H p tau j*fourResponses H p tau j) = 0 := by
  rw [scaleCode_response]
  unfold nativeScaleDet
  ring

/-- Exact multiplicity and residue sign of a specified matched power
component. This is not an asymptotic of the literal prime measure. -/
theorem scaleCode_matched_response (H : ℕ) (p s : ℂ) (tau : ℝ) (m : ℕ) :
    (∑ j : Fin 4, scaleCode H p tau j*(-(m : ℂ)*fourResponses H s tau j)) =
      -(m : ℂ)*nativeScaleDet H p s tau := by
  rw [show (∑ j : Fin 4, scaleCode H p tau j*(-(m : ℂ)*fourResponses H s tau j)) =
      -(m : ℂ)*(∑ j : Fin 4, scaleCode H p tau j*fourResponses H s tau j) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring,
    scaleCode_response]

theorem scale_factor_ne_zero {p s : ℂ} (h : p.re ≠ s.re) :
    Complex.exp (p*(Real.log 2 : ℂ))-Complex.exp (s*(Real.log 2 : ℂ)) ≠ 0 := by
  intro hz
  have hn := congrArg norm (sub_eq_zero.mp hz)
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hn
  have he := Real.exp_injective hn
  exact h (mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne' he)

private theorem tendsto_contrast_div_square (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun tau : ℝ => contrast s tau/(tau : ℂ)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (B s)) := by
  have hr := fourthOrderExpansion hs
  have ht : Tendsto (fun tau : ℝ => (tau : ℂ)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun tau : ℝ => (tau : ℂ)^2) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have he := (tendsto_const_nhds (x := B s)).add (ht.mul (hr.const_add (C s)))
  simp only [zero_mul, add_zero] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with tau htau
  have hn : (tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htau)
  change B s+(tau : ℂ)^2*(C s+jetRemainder (continuumResponse s) (B s) (C s) tau) =
    contrast s tau/(tau : ℂ)^2
  unfold contrast jetRemainder
  field_simp
  ring

private theorem tendsto_contrast_div_fourth (s : ℂ) (hs : 0 < s.re) (hb : B s = 0) :
    Tendsto (fun tau : ℝ => contrast s tau/(tau : ℂ)^4)
      (𝓝[>] (0 : ℝ)) (𝓝 (C s)) := by
  have hr := (fourthOrderExpansion hs).const_add (C s)
  simp only [add_zero] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with tau htau
  have hn : (tau : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htau)
  unfold contrast jetRemainder
  rw [hb]
  field_simp
  ring

private theorem eventually_contrast_ne_zero {s : ℂ} {d : ℕ} {c : ℂ}
    (hc : c ≠ 0)
    (ht : Tendsto (fun tau : ℝ => contrast s tau/(tau : ℂ)^d)
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), contrast s tau ≠ 0 := by
  have hp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  filter_upwards [ht.norm.eventually (lt_mem_nhds (by linarith : ‖c‖/2 < ‖c‖))]
    with tau hnorm
  intro hz
  rw [hz, zero_div, norm_zero] at hnorm
  linarith

theorem eventually_contrast_ne_zero_of_B {s : ℂ} (hs : 0 < s.re) (hb : B s ≠ 0) :
    ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), contrast s tau ≠ 0 :=
  eventually_contrast_ne_zero hb (tendsto_contrast_div_square s hs)

/-- A nonzero quadratic coefficient at both exponents gives a common fixed
phase even if their quadratic/quartic determinant is exactly zero. -/
theorem exists_scale_code_of_B {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re)
    (hps : p.re ≠ s.re) (hbp : B p ≠ 0) (hbs : B s ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 := by
  have ep := eventually_contrast_ne_zero hbp (tendsto_contrast_div_square p hp)
  have es := eventually_contrast_ne_zero hbs (tendsto_contrast_div_square s hs)
  have hall : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), 0 < tau ∧
      contrast p tau ≠ 0 ∧ contrast s tau ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, ep, es] with tau ht hp' hs'
    exact ⟨ht, hp', hs'⟩
  obtain ⟨tau, ht, hp', hs'⟩ := hall.exists
  exact ⟨tau, ht, mul_ne_zero (mul_ne_zero (scale_factor_ne_zero hps) hp') hs'⟩

theorem exists_scale_code_of_C {p s : ℂ} (hp : 0 < p.re) (hs : 0 < s.re)
    (hps : p.re ≠ s.re) (hbp : B p = 0) (hbs : B s = 0)
    (hcp : C p ≠ 0) (hcs : C s ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 := by
  have ep := eventually_contrast_ne_zero hcp (tendsto_contrast_div_fourth p hp hbp)
  have es := eventually_contrast_ne_zero hcs (tendsto_contrast_div_fourth s hs hbs)
  have hall : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), 0 < tau ∧
      contrast p tau ≠ 0 ∧ contrast s tau ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, ep, es] with tau ht hp' hs'
    exact ⟨ht, hp', hs'⟩
  obtain ⟨tau, ht, hp', hs'⟩ := hall.exists
  exact ⟨tau, ht, mul_ne_zero (mul_ne_zero (scale_factor_ne_zero hps) hp') hs'⟩

private theorem eventually_contrast_of_nonzero_jet {s : ℂ} (hs : 0 < s.re)
    (hj : B s ≠ 0 ∨ C s ≠ 0) :
    ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), contrast s tau ≠ 0 := by
  by_cases hb : B s = 0
  · exact eventually_contrast_ne_zero (hj.resolve_left (not_not.mpr hb))
      (tendsto_contrast_div_fourth s hs hb)
  · exact eventually_contrast_ne_zero hb (tendsto_contrast_div_square s hs)

/-- A common small modulation exists even when the first nonzero jet
orders at the two exponents differ. No wedge premise is required. -/
theorem exists_scale_code_of_nonzero_jets {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (hps : p.re ≠ s.re)
    (hjp : B p ≠ 0 ∨ C p ≠ 0) (hjs : B s ≠ 0 ∨ C s ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 := by
  have hall : ∀ᶠ tau : ℝ in 𝓝[>] (0 : ℝ), 0 < tau ∧
      contrast p tau ≠ 0 ∧ contrast s tau ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, eventually_contrast_of_nonzero_jet hp hjp,
      eventually_contrast_of_nonzero_jet hs hjs] with tau ht hp' hs'
    exact ⟨ht,hp',hs'⟩
  obtain ⟨tau,ht,hp',hs'⟩ := hall.exists
  exact ⟨tau,ht,mul_ne_zero (mul_ne_zero (scale_factor_ne_zero hps) hp') hs'⟩

/-- Every quartic-degenerate pair of nonzero jet vectors is separated by
the four-response code. The remaining jet degeneracy is stated explicitly. -/
theorem exists_scale_code_of_degenerate_wedge {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (hps : p.re ≠ s.re)
    (hvp : B p ≠ 0 ∨ C p ≠ 0) (hvs : B s ≠ 0 ∨ C s ≠ 0)
    (hw : B p*C s-C p*B s = 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 := by
  by_cases hb : B p = 0
  · have hcp : C p ≠ 0 := hvp.resolve_left (not_not.mpr hb)
    have hbs : B s = 0 := by
      rw [hb, zero_mul, zero_sub, neg_eq_zero] at hw
      exact (mul_eq_zero.mp hw).resolve_left hcp
    exact exists_scale_code_of_C hp hs hps hb hbs hcp
      (hvs.resolve_left (not_not.mpr hbs))
  · have hbs : B s ≠ 0 := by
      intro hz
      have hcs : C s ≠ 0 := hvs.resolve_left (not_not.mpr hz)
      rw [hz, mul_zero, sub_zero] at hw
      exact mul_ne_zero hb hcs hw
    exact exists_scale_code_of_B hp hs hps hb hbs

theorem nativeContrast_eq_scaled (H : ℕ) (s : ℂ) (tau : ℝ) :
    nativeContrast H s tau = Complex.exp (s*(Real.log H : ℂ))*
      (scaledResponse H s tau-scaledResponse H s 0) := by
  unfold nativeContrast scaledResponse
  simp only [zero_div]
  rw [← mul_sub, ← mul_assoc, ← Complex.exp_add]
  simp

private theorem log_double {H : ℕ} (hH : 0 < H) :
    Real.log (2*H : ℕ) = Real.log 2+Real.log H := by
  rw [Nat.cast_mul, Nat.cast_ofNat]
  exact Real.log_mul (by norm_num) (by exact_mod_cast hH.ne')

theorem normalized_nativeScaleDet_eq {H : ℕ} (hH : 0 < H) (p s : ℂ) (tau : ℝ) :
    Complex.exp (-(p+s)*(Real.log H : ℂ))*nativeScaleDet H p s tau =
      Complex.exp (p*(Real.log 2 : ℂ))*
        (scaledResponse (2*H) p tau-scaledResponse (2*H) p 0)*
        (scaledResponse H s tau-scaledResponse H s 0)-
      Complex.exp (s*(Real.log 2 : ℂ))*
        (scaledResponse H p tau-scaledResponse H p 0)*
        (scaledResponse (2*H) s tau-scaledResponse (2*H) s 0) := by
  have ed (q : ℂ) : Complex.exp (q*(Real.log (2*H : ℕ) : ℂ)) =
      Complex.exp (q*(Real.log 2 : ℂ))*Complex.exp (q*(Real.log H : ℂ)) := by
    rw [log_double hH, Complex.ofReal_add, mul_add, Complex.exp_add]
  unfold nativeScaleDet
  simp_rw [nativeContrast_eq_scaled]
  rw [ed p, ed s]
  rw [mul_sub]
  have hc : Complex.exp (-(p+s)*(Real.log H : ℂ))*
      (Complex.exp (p*(Real.log H : ℂ))*Complex.exp (s*(Real.log H : ℂ))) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  calc
    _ = (Complex.exp (-(p+s)*(Real.log H : ℂ))*
      (Complex.exp (p*(Real.log H : ℂ))*Complex.exp (s*(Real.log H : ℂ))))*
      (Complex.exp (p*(Real.log 2 : ℂ))*
        (scaledResponse (2*H) p tau-scaledResponse (2*H) p 0)*
        (scaledResponse H s tau-scaledResponse H s 0)-
      Complex.exp (s*(Real.log 2 : ℂ))*
        (scaledResponse H p tau-scaledResponse H p 0)*
        (scaledResponse (2*H) s tau-scaledResponse (2*H) s 0)) := by
          ring
    _ = _ := by rw [hc, one_mul]

private theorem tendsto_double : Tendsto (fun H : ℕ => 2*H) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with H hH
  omega

theorem tendsto_normalized_nativeScaleDet {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (tau : ℝ) :
    Tendsto (fun H : ℕ => Complex.exp (-(p+s)*(Real.log H : ℂ))*
      nativeScaleDet H p s tau) atTop (𝓝 (scaleDet p s tau)) := by
  have hp0 := (tendsto_scaledResponse hp tau).sub (tendsto_scaledResponse hp 0)
  have hs0 := (tendsto_scaledResponse hs tau).sub (tendsto_scaledResponse hs 0)
  have ht := ((hp0.comp tendsto_double).const_mul
    (Complex.exp (p*(Real.log 2 : ℂ)))).mul hs0 |>.sub
      ((hp0.const_mul (Complex.exp (s*(Real.log 2 : ℂ)))).mul
        (hs0.comp tendsto_double))
  have he : Complex.exp (p*(Real.log 2 : ℂ))*contrast p tau*contrast s tau-
      Complex.exp (s*(Real.log 2 : ℂ))*contrast p tau*contrast s tau =
        scaleDet p s tau := by unfold scaleDet; ring
  change Tendsto _ atTop (𝓝 (Complex.exp (p*(Real.log 2 : ℂ))*contrast p tau*contrast s tau-
    Complex.exp (s*(Real.log 2 : ℂ))*contrast p tau*contrast s tau)) at ht
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  exact (normalized_nativeScaleDet_eq hH p s tau).symm

/-- The finite source determinant itself, not only its limit, is eventually
bounded below at its native H^(Re(p)+Re(s)) scale. -/
theorem eventually_nativeScaleDet_source_lower {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) {tau : ℝ} (hd : scaleDet p s tau ≠ 0) :
    ∀ᶠ H : ℕ in atTop,
      (‖scaleDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
        ‖nativeScaleDet H p s tau‖ := by
  have he := (tendsto_normalized_nativeScaleDet hp hs tau).norm
  have hn : 0 < ‖scaleDet p s tau‖ := norm_pos_iff.mpr hd
  filter_upwards [he.eventually (lt_mem_nhds (by linarith :
    ‖scaleDet p s tau‖/2 < ‖scaleDet p s tau‖))] with H hH
  rw [norm_mul, Complex.norm_exp] at hH
  have hre : (-(p+s)*(Real.log H : ℂ)).re = -(p.re+s.re)*Real.log H := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  rw [hre] at hH
  have hc : Real.exp ((p.re+s.re)*Real.log H)*
      Real.exp (-(p.re+s.re)*Real.log H) = 1 := by
    rw [← Real.exp_add, show (p.re+s.re)*Real.log H+
      -(p.re+s.re)*Real.log H = 0 by ring, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_left hH.le
    (Real.exp_pos ((p.re+s.re)*Real.log H)).le
  calc
    _ = Real.exp ((p.re+s.re)*Real.log H)*(‖scaleDet p s tau‖/2) := by ring
    _ ≤ _ := hm
    _ = _ := by rw [← mul_assoc, hc, one_mul]

theorem exists_fixed_scale_code_of_nonzero_jets {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (hps : p.re ≠ s.re)
    (hjp : B p ≠ 0 ∨ C p ≠ 0) (hjs : B s ≠ 0 ∨ C s ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeScaleDet H p s tau‖ := by
  obtain ⟨tau,ht,hd⟩ := exists_scale_code_of_nonzero_jets hp hs hps hjp hjs
  exact ⟨tau,ht,hd,eventually_nativeScaleDet_source_lower hp hs hd⟩

/-- An exact escape theorem for a quartic exception, provided neither
exponent has an entirely zero quadratic/quartic jet vector. -/
theorem exists_fixed_scale_code_source_lower {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (hps : p.re ≠ s.re)
    (hvp : B p ≠ 0 ∨ C p ≠ 0) (hvs : B s ≠ 0 ∨ C s ≠ 0)
    (hw : B p*C s-C p*B s = 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeScaleDet H p s tau‖ := by
  obtain ⟨tau, ht, hd⟩ := exists_scale_code_of_degenerate_wedge hp hs hps hvp hvs hw
  exact ⟨tau, ht, hd, eventually_nativeScaleDet_source_lower hp hs hd⟩

/-- Either the original three-phase code or the two-phase/two-scale code
works whenever the two actual jet vectors are nonzero. This leaves precisely
the common-zero jet gate, not the old proportionality equation. -/
theorem exists_source_code_of_nonzero_jets {p s : ℂ}
    (hp : 0 < p.re) (hs : 0 < s.re) (hps : p.re ≠ s.re)
    (hvp : B p ≠ 0 ∨ C p ≠ 0) (hvs : B s ≠ 0 ∨ C s ≠ 0) :
    (∃ tau : ℝ, 0 < tau ∧ continuumDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeDet H p s tau‖) ∨
    (∃ tau : ℝ, 0 < tau ∧ scaleDet p s tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet p s tau‖/2)*Real.exp ((p.re+s.re)*Real.log H) ≤
          ‖nativeScaleDet H p s tau‖) := by
  by_cases hw : B p*C s-C p*B s = 0
  · exact Or.inr (exists_fixed_scale_code_source_lower hp hs hps hvp hvs hw)
  · exact Or.inl (exists_fixed_code_of_wedge hp hs hw)

/-- Campaign specialization. No nonzero jet premise is silently inferred
from the ordinate condition or from numerical probes. -/
theorem exists_campaign_source_code {beta : ℝ} (hb : 0 < beta) (hb1 : beta < 1)
    (y : ℝ)
    (hpj : B (SuzukiCarryPoleCenter.poleExponent y) ≠ 0 ∨
      C (SuzukiCarryPoleCenter.poleExponent y) ≠ 0)
    (hbj : B (beta : ℂ) ≠ 0 ∨ C (beta : ℂ) ≠ 0) :
    (∃ tau : ℝ, 0 < tau ∧
      continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖) ∨
    (∃ tau : ℝ, 0 < tau ∧
      scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeScaleDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖) := by
  have hre : (SuzukiCarryPoleCenter.poleExponent y).re ≠ (beta : ℂ).re := by
    rw [SuzukiCarryPoleCenter.poleExponent_re, Complex.ofReal_re]
    exact ne_of_gt hb1
  simpa only [SuzukiCarryPoleCenter.poleExponent_re, Complex.ofReal_re] using
    exists_source_code_of_nonzero_jets
      (by rw [SuzukiCarryPoleCenter.poleExponent_re]; norm_num) (by simpa using hb)
      hre hpj hbj

theorem campaign_scale_gap (y beta : ℝ) :
    2-Real.exp (beta*Real.log 2) ≤
      ‖Complex.exp (SuzukiCarryPoleCenter.poleExponent y*(Real.log 2 : ℂ))-
        Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))‖ := by
  have h := (le_abs_self _).trans (abs_norm_sub_norm_le
    (Complex.exp (SuzukiCarryPoleCenter.poleExponent y*(Real.log 2 : ℂ)))
    (Complex.exp ((beta : ℂ)*(Real.log 2 : ℂ))))
  simpa only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, SuzukiCarryPoleCenter.poleExponent_re,
    one_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h

end
end RiemannGaussian.SuzukiCarryPhaseScaleGate
