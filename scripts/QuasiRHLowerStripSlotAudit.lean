/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual principal-slot lower-strip preflight

This audits the native all-power slot at its actual double-pole coordinates.
The leading correction has modulus `Q^(3-5*re(s))`, after the compensating
`Q^s` has been included. No global correction, residue, contour, or low-row
estimate is inferred from the finite local formulas.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2048
noncomputable section
open scoped BigOperators Classical Topology
namespace OpenAIReview.LowerStripSlot
open OAI OAI.SevenEighths
open ProbeEuler ProbeLocal PrincipalSlotEstimate ProbeFiniteProductBounds HeckeFamily
open OAI.CompletedGauss OAI.ActualEisensteinCubic

/-- The exact remaining denominator after the local raw factor cancels. -/
def slotDenominator (t R D : ℂ) : ℂ := 1 - t * R - (1-t)*D

theorem principal_K_exact {Q : ℝ} (hQ : 0<Q) (η s : ℂ) :
    coordK Q η s 1 = (1-(Q:ℂ)⁻¹)*coordD Q η 1 s := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordK coordD
  simp only [star_one, mul_one]
  rw [show -s-1 = -s+(-1:ℂ) by ring, Complex.cpow_add _ _ hQc,
    Complex.cpow_neg_one]
  field_simp

theorem marked_principal_algebra (t R D : ℂ) (ht : 1-t≠0) :
    markedFactor R t t ((1-t)*D) (-D+t*R) 1 =
      (1+t)*(R-D)/(1-R) := by
  unfold markedFactor
  field_simp
  ring

theorem principal_marked_exact {Q : ℝ} (hQ : 0<Q) (A η s : ℂ)
    (ht : 1-(Q:ℂ)⁻¹≠0) :
    principalMarked Q A η s =
      (1+(Q:ℂ)⁻¹)*(coordR Q A s (1/6)-coordD Q η 1 s)/
        (1-coordR Q A s (1/6)) := by
  unfold principalMarked
  rw [principal_V, principal_W, principal_K_exact hQ]
  exact marked_principal_algebra _ _ _ ht

/-- Pure field algebra for the EXISTING compensated slot, not a free row. -/
theorem continued_principal_algebra (t R D : ℂ) (hR : 1-R≠0) :
    continuedCorrection t t D ((1+t)*(R-D)/(1-R)) =
      (1-t)*(1+t)*slotDenominator t R D/((1-R)*(1-D)) := by
  unfold continuedCorrection slotDenominator
  field_simp
  ring

theorem compensated_principal_ratio (t R D B : ℂ)
    (ht : 1-t≠0) (hpt : 1+t≠0) (hR : 1-R≠0) (hD : 1-D≠0)
    (hden : slotDenominator t R D≠0) :
    compensatedReplacement t t D ((1+t)*(R-D)/(1-R)) B t /
      continuedCorrection t t D ((1+t)*(R-D)/(1-R)) =
      ((B-t)*(1-t)*(R-D)-t*(1-R))/slotDenominator t R D := by
  rw [continued_principal_algebra t R D hR]
  unfold compensatedReplacement
  field_simp
  ring

theorem compensated_principal_algebra (t R D B : ℂ)
    (ht : 1-t≠0) (hpt : 1+t≠0) (hR : 1-R≠0) (hD : 1-D≠0)
    (hden : slotDenominator t R D≠0) (hBD : B*D=1) :
    compensatedReplacement t t D ((1+t)*(R-D)/(1-R)) B t /
      continuedCorrection t t D ((1+t)*(R-D)/(1-R)) + 1 =
      (1-t)*(R*(B-t)-(1-t)*D)/slotDenominator t R D := by
  rw [compensated_principal_ratio t R D B ht hpt hR hD hden]
  field_simp
  unfold slotDenominator
  linear_combination -(1-t)*hBD

theorem principal_slot_exact {Q : ℝ} (hQ : 0<Q) (A η s : ℂ) (hη : ‖η‖=1)
    (ht : 1-(Q:ℂ)⁻¹≠0) (hpt : 1+(Q:ℂ)⁻¹≠0)
    (hR : 1-coordR Q A s (1/6)≠0) (hD : 1-coordD Q η 1 s≠0)
    (hden : slotDenominator (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q η 1 s)≠0) :
    principalSlot Q A η s + 1 =
      (1-(Q:ℂ)⁻¹)*
        (coordR Q A s (1/6)*(star η*(Q:ℂ)^s-(Q:ℂ)⁻¹) -
          (1-(Q:ℂ)⁻¹)*coordD Q η 1 s)/
        slotDenominator (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q η 1 s) := by
  unfold principalSlot principalReplacement
  rw [principal_marked_exact hQ A η s ht]
  unfold unramifiedClosed
  dsimp only
  rw [principal_V, principal_W, principal_K_exact hQ,
    marked_principal_algebra _ _ _ ht, Complex.cpow_neg_one]
  exact compensated_principal_algebra _ _ _ _ ht hpt hR hD hden
    (principal_coord_cancellation hQ η s hη)

theorem leading_norm {Q : ℝ} (hQ : 0<Q) (A η s : ℂ) (hA : ‖A‖=1) (hη : ‖η‖=1) :
    ‖coordR Q A s (1/6)*(star η*(Q:ℂ)^s)‖ = Q^(3-5*s.re) := by
  rw [norm_mul, principal_B_norm hQ η s hη]
  unfold coordR
  rw [norm_mul, hA, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  norm_num
  rw [←Real.rpow_add hQ]
  congr 1
  ring

theorem leading_norm_le {Q : ℝ} (hQ : 0<Q) (A η s : ℂ)
    (hA : ‖A‖≤1) (hη : ‖η‖=1) :
    ‖coordR Q A s (1/6)*(star η*(Q:ℂ)^s)‖ ≤ Q^(3-5*s.re) := by
  rw [norm_mul, principal_B_norm hQ η s hη]
  have hR := coordR_norm_le Q hQ A s (1/6) hA
  norm_num at hR
  rw [show 4-6*s.re-1=3-6*s.re by ring] at hR
  calc
    _ ≤ Q^(3-6*s.re)*Q^s.re := mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hQ.le _)
    _ = _ := by rw [←Real.rpow_add hQ]; congr 1; ring

theorem native_D_norm {Q : ℝ} (hQ : 0<Q) (η s : ℂ) (hη : ‖η‖=1) :
    ‖coordD Q η 1 s‖ = Q^(-s.re) := by
  simp only [coordD, star_one, mul_one, norm_mul, hη, one_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]

theorem small_denominator_bounds {t : ℝ} {R D : ℂ}
    (ht0 : 0≤t) (ht : t≤1/4) (hR : ‖R‖≤1/2) (hD : ‖D‖≤1/4) :
    1/2 ≤ ‖slotDenominator t R D‖ ∧ ‖slotDenominator t R D‖ ≤ 2 := by
  have ht1 : t≤1 := by linarith
  have htn : ‖(t:ℂ)‖=t := by simp [Complex.norm_real, abs_of_nonneg ht0]
  have hon : ‖(1-(t:ℂ))‖=1-t := by
    rw [←Complex.ofReal_one, ←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  have he : ‖(t:ℂ)*R+(1-(t:ℂ))*D‖≤1/2 := by
    calc
      _ ≤ ‖(t:ℂ)*R‖+‖(1-(t:ℂ))*D‖ := norm_add_le _ _
      _ = t*‖R‖+(1-t)*‖D‖ := by rw [norm_mul,norm_mul,htn,hon]
      _ ≤ t*(1/2)+(1-t)*(1/4) := by gcongr
      _ ≤ _ := by linarith
  have hd : slotDenominator t R D = 1-((t:ℂ)*R+(1-(t:ℂ))*D) := by
    unfold slotDenominator
    ring
  rw [hd]
  constructor
  · have hl := norm_sub_norm_le (1:ℂ) ((t:ℂ)*R+(1-(t:ℂ))*D)
    rw [norm_one] at hl
    linarith
  · have hu := norm_sub_le (1:ℂ) ((t:ℂ)*R+(1-(t:ℂ))*D)
    rw [norm_one] at hu
    linarith

theorem algebraic_slot_upper {t : ℝ} {R D B : ℂ}
    (ht0 : 0≤t) (ht : t≤1/4) (hR : ‖R‖≤1/2) (hD : ‖D‖≤1/4) :
    ‖(1-(t:ℂ))*(R*(B-t)-(1-(t:ℂ))*D)/slotDenominator t R D‖ ≤
      2*(‖R*B‖+t*‖R‖+‖D‖) := by
  have hdb := (small_denominator_bounds ht0 ht hR hD).1
  have ht1 : t≤1 := by linarith
  have htn : ‖(t:ℂ)‖=t := by simp [Complex.norm_real, abs_of_nonneg ht0]
  have hon : ‖(1-(t:ℂ))‖=1-t := by
    rw [←Complex.ofReal_one, ←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖slotDenominator t R D‖)).mpr
  have hn : ‖(1-(t:ℂ))*(R*(B-t)-(1-(t:ℂ))*D)‖≤‖R*B‖+t*‖R‖+‖D‖ := by
    rw [norm_mul,hon]
    calc
      _ ≤ 1*‖R*(B-t)-(1-(t:ℂ))*D‖ := by gcongr; linarith
      _ ≤ ‖R*B‖+t*‖R‖+‖D‖ := by
        rw [one_mul, mul_sub]
        calc
          _ ≤ ‖R*B-R*t‖+‖(1-(t:ℂ))*D‖ := norm_sub_le _ _
          _ ≤ ‖R*B‖+‖R*t‖+‖(1-(t:ℂ))*D‖ := by gcongr; exact norm_sub_le _ _
          _ ≤ _ := by simp only [norm_mul,htn,hon]; nlinarith [norm_nonneg D]
  have he0 : 0≤‖R*B‖+t*‖R‖+‖D‖ := by positivity
  have hp := mul_le_mul_of_nonneg_left hdb he0
  nlinarith [hp]

theorem algebraic_slot_lower {t : ℝ} {R D B : ℂ}
    (ht0 : 0≤t) (ht : t≤1/4) (hR : ‖R‖≤1/2) (hD : ‖D‖≤1/4) :
    ‖R*B‖/4-1 ≤
      ‖(1-(t:ℂ))*(R*(B-t)-(1-(t:ℂ))*D)/slotDenominator t R D‖ := by
  let X : ℂ := R*(B-t)-(1-(t:ℂ))*D
  let G : ℂ := (1-(t:ℂ))*X/slotDenominator t R D
  have hdb := small_denominator_bounds ht0 ht hR hD
  have hd0 : ‖slotDenominator t R D‖≠0 := by linarith [hdb.1]
  have ht1 : t≤1 := by linarith
  have htn : ‖(t:ℂ)‖=t := by simp [Complex.norm_real, abs_of_nonneg ht0]
  have hon : ‖(1-(t:ℂ))‖=1-t := by
    rw [←Complex.ofReal_one, ←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  have he : ‖G‖*‖slotDenominator t R D‖ = (1-t)*‖X‖ := by
    dsimp only [G]
    rw [norm_div,norm_mul,hon]
    field_simp
  have hu := mul_le_mul_of_nonneg_left hdb.2 (norm_nonneg G)
  have hx : ‖X‖≤4*‖G‖ := by nlinarith [norm_nonneg X, norm_nonneg G]
  have hi : R*B = X+R*t+(1-(t:ℂ))*D := by dsimp only [X]; ring
  have hn : ‖R*B‖≤‖X‖+1/2 := by
    rw [hi]
    calc
      _ ≤ ‖X+R*t‖+‖(1-(t:ℂ))*D‖ := norm_add_le _ _
      _ ≤ ‖X‖+‖R*t‖+‖(1-(t:ℂ))*D‖ := by gcongr; exact norm_add_le _ _
      _ = ‖X‖+‖R‖*t+(1-t)*‖D‖ := by simp only [norm_mul,htn,hon]
      _ ≤ ‖X‖+(1/2)*t+(1-t)*(1/4) := by gcongr
      _ ≤ _ := by linarith
  change ‖R*B‖/4-1≤‖G‖
  linarith

theorem actual_phase_norm_one (η : HeckeFamily.Character) (p : ActualEisensteinCubic.O)
    (hp : p≠0) (hu : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖actualAPhase η p‖=1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star,
    FiniteGaussPhase.norm_angularFactor p hp, actual_target_norm η p hu, one_pow, one_mul]

theorem principal_slot_guards {Q : ℝ} (hQ : 4≤Q) (A η s : ℂ)
    (hR : ‖coordR Q A s (1/6)‖≤1/2) (hD : ‖coordD Q η 1 s‖≤1/4) :
    (1-(Q:ℂ)⁻¹≠0) ∧ (1+(Q:ℂ)⁻¹≠0) ∧
      (1-coordR Q A s (1/6)≠0) ∧ (1-coordD Q η 1 s≠0) ∧
      (slotDenominator (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q η 1 s)≠0) := by
  have hQ0 : 0<Q := by linarith
  have ht0 : 0≤Q⁻¹ := inv_nonneg.mpr hQ0.le
  have ht : Q⁻¹≤1/4 := by
    rw [←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have htn : ‖(Q:ℂ)⁻¹‖=Q⁻¹ := by simp [norm_inv, Complex.norm_real, abs_of_pos hQ0]
  have h1t : 1-(Q:ℂ)⁻¹≠0 :=
    one_sub_ne_zero_of_norm_le_half _ (by rw [htn]; linarith)
  have hpt : 1+(Q:ℂ)⁻¹≠0 := by
    rw [←Complex.ofReal_inv, ←Complex.ofReal_one, ←Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have h1R := one_sub_ne_zero_of_norm_le_half _ hR
  have h1D := one_sub_ne_zero_of_norm_le_half _ (by linarith : ‖coordD Q η 1 s‖≤1/2)
  have hd := (small_denominator_bounds ht0 ht hR hD).1
  rw [Complex.ofReal_inv] at hd
  exact ⟨h1t,hpt,h1R,h1D,norm_pos_iff.mp (by linarith)⟩

theorem principal_slot_lower {Q : ℝ} (hQ : 4≤Q) (A η s : ℂ)
    (hA : ‖A‖=1) (hη : ‖η‖=1)
    (hR : ‖coordR Q A s (1/6)‖≤1/2) (hD : ‖coordD Q η 1 s‖≤1/4) :
    Q^(3-5*s.re)/4-1 ≤ ‖principalSlot Q A η s+1‖ := by
  have hQ0 : 0<Q := by linarith
  have ht0 : 0≤Q⁻¹ := inv_nonneg.mpr hQ0.le
  have ht : Q⁻¹≤1/4 := by
    rw [←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  rcases principal_slot_guards hQ A η s hR hD with ⟨h1t,hpt,h1R,h1D,hden⟩
  rw [principal_slot_exact hQ0 A η s hη h1t hpt h1R h1D hden]
  have hl := algebraic_slot_lower (B := star η*(Q:ℂ)^s) ht0 ht hR hD
  rw [Complex.ofReal_inv, leading_norm hQ0 A η s hA hη] at hl
  exact hl

theorem principal_slot_upper {Q : ℝ} (hQ : 4≤Q) (A η s : ℂ)
    (hA : ‖A‖≤1) (hη : ‖η‖=1) (hs : 1/2≤s.re)
    (hR : ‖coordR Q A s (1/6)‖≤1/2) (hD : ‖coordD Q η 1 s‖≤1/4) :
    ‖principalSlot Q A η s+1‖ ≤ 4*(Q^(3-5*s.re)+Q^(-s.re)) := by
  have hQ0 : 0<Q := by linarith
  have ht0 : 0≤Q⁻¹ := inv_nonneg.mpr hQ0.le
  have ht : Q⁻¹≤1/4 := by
    rw [←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  rcases principal_slot_guards hQ A η s hR hD with ⟨h1t,hpt,h1R,h1D,hden⟩
  rw [principal_slot_exact hQ0 A η s hη h1t hpt h1R h1D hden]
  have hu := algebraic_slot_upper (B := star η*(Q:ℂ)^s) ht0 ht hR hD
  rw [Complex.ofReal_inv, native_D_norm hQ0 η s hη] at hu
  have hlead := leading_norm_le hQ0 A η s hA hη
  have hr := coordR_norm_le Q hQ0 A s (1/6) hA
  norm_num at hr
  rw [show 4-6*s.re-1=3-6*s.re by ring] at hr
  have htr : Q⁻¹*‖coordR Q A s (1/6)‖≤Q^(-s.re) := by
    calc
      _ ≤ Q⁻¹*Q^(3-6*s.re) := mul_le_mul_of_nonneg_left hr ht0
      _ = Q^(2-6*s.re) := by rw [←Real.rpow_neg_one, ←Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hz0 : 0≤Q^(3-5*s.re) := Real.rpow_nonneg hQ0.le _
  linarith

theorem tendsto_negative_power {ι : Type*} {l : Filter ι} {Q : ι → ℝ}
    (hQ : Filter.Tendsto Q l Filter.atTop) {a : ℝ} (ha : a<0) :
    Filter.Tendsto (fun n => (Q n)^a) l (𝓝 0) := by
  simpa only [neg_neg, Function.comp_def] using
    (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp hQ

theorem eventually_principal_guards {ι : Type*} {l : Filter ι} {Q : ι → ℝ}
    (hQ : Filter.Tendsto Q l Filter.atTop) (A η : ι → ℂ) (s : ℂ)
    (hA : ∀ n, ‖A n‖≤1) (hη : ∀ n, ‖η n‖=1) (hs : 1/2<s.re) :
    ∀ᶠ n in l, 4≤Q n ∧ ‖coordR (Q n) (A n) s (1/6)‖≤1/2 ∧
      ‖coordD (Q n) (η n) 1 s‖≤1/4 := by
  have hr := tendsto_negative_power hQ (show 3-6*s.re<0 by linarith)
  have hd := tendsto_negative_power hQ (show -s.re<0 by linarith)
  filter_upwards [hQ.eventually_ge_atTop 4,
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hd.eventually_le_const (by norm_num : (0:ℝ)<1/4)] with n hn hnr hnd
  have hQ0 : 0<Q n := by linarith
  have hR := coordR_norm_le (Q n) hQ0 (A n) s (1/6) (hA n)
  norm_num at hR
  rw [show 4-6*s.re-1=3-6*s.re by ring] at hR
  exact ⟨hn,hR.trans hnr, by rw [native_D_norm hQ0 _ _ (hη n)]; exact hnd⟩

/-- The native compensated slot tends to minus one strictly above `3/5`.
This is a local statement only, with no contour or global source inference. -/
theorem principal_slot_tendsto_neg_one {ι : Type*} {l : Filter ι} {Q : ι → ℝ}
    (hQ : Filter.Tendsto Q l Filter.atTop) (A η : ι → ℂ) (s : ℂ)
    (hA : ∀ n, ‖A n‖≤1) (hη : ∀ n, ‖η n‖=1) (hs : 3/5<s.re) :
    Filter.Tendsto (fun n => principalSlot (Q n) (A n) (η n) s) l (𝓝 (-1)) := by
  have hr := tendsto_negative_power hQ (show 3-5*s.re<0 by linarith)
  have hd := tendsto_negative_power hQ (show -s.re<0 by linarith)
  have hb : Filter.Tendsto (fun n => 4*((Q n)^(3-5*s.re)+(Q n)^(-s.re))) l (𝓝 0) := by
    simpa using (hr.add hd).const_mul 4
  have hg := eventually_principal_guards hQ A η s hA hη (by linarith)
  have hz : Filter.Tendsto (fun n => principalSlot (Q n) (A n) (η n) s+1) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [hg] with n hn
    exact principal_slot_upper hn.1 _ _ _ (hA n) (hη n) (by linarith) hn.2.1 hn.2.2
  simpa using hz.sub_const 1

/-- Unit-modulus native phases instead force divergence below `3/5`.
Thus compensation does not centre every fixed right-half point. -/
theorem principal_slot_diverges_below_three_fifths {ι : Type*} {l : Filter ι}
    {Q : ι → ℝ} (hQ : Filter.Tendsto Q l Filter.atTop) (A η : ι → ℂ) (s : ℂ)
    (hA : ∀ n, ‖A n‖=1) (hη : ∀ n, ‖η n‖=1)
    (hs : 1/2<s.re) (hs' : s.re<3/5) :
    Filter.Tendsto (fun n => ‖principalSlot (Q n) (A n) (η n) s+1‖) l Filter.atTop := by
  have hp := (tendsto_rpow_atTop (show 0<3-5*s.re by linarith)).comp hQ
  have hg := eventually_principal_guards hQ A η s (fun n => (hA n).le) hη hs
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [hg,hp.eventually_ge_atTop (4*(b+1))] with n hn hnb
  have hl := principal_slot_lower hn.1 _ _ _ (hA n) (hη n) hn.2.1 hn.2.2
  dsimp only [Function.comp_def] at hnb
  linarith

theorem algebraic_leading_difference (t R D B : ℂ)
    (hden : slotDenominator t R D≠0) (hBD : B*D=1) :
    (1-t)*(R*(B-t)-(1-t)*D)/slotDenominator t R D - R*B =
      (t*(R*B)*(R-1)+(1-t)^2*(R-D))/slotDenominator t R D := by
  field_simp
  unfold slotDenominator
  linear_combination R*(1-t)*hBD

theorem algebraic_leading_difference_bound {t : ℝ} {R D B : ℂ}
    (ht0 : 0≤t) (ht : t≤1/4) (hR : ‖R‖≤1/2) (hD : ‖D‖≤1/4)
    (hBD : B*D=1) :
    ‖(1-(t:ℂ))*(R*(B-t)-(1-(t:ℂ))*D)/slotDenominator t R D-R*B‖ ≤
      3*t*‖R*B‖+2*‖R‖+2*‖D‖ := by
  have hdb := (small_denominator_bounds ht0 ht hR hD).1
  have hd0 : slotDenominator t R D≠0 := norm_pos_iff.mp (by linarith)
  have ht1 : t≤1 := by linarith
  have htn : ‖(t:ℂ)‖=t := by simp [Complex.norm_real, abs_of_nonneg ht0]
  have hon : ‖1-(t:ℂ)‖=1-t := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
  rw [algebraic_leading_difference _ _ _ _ hd0 hBD, norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖slotDenominator t R D‖)).mpr
  have hn : ‖(t:ℂ)*(R*B)*(R-1)+(1-(t:ℂ))^2*(R-D)‖ ≤
      (3/2)*t*‖R*B‖+‖R‖+‖D‖ := by
    calc
      _ ≤ ‖(t:ℂ)*(R*B)*(R-1)‖+‖(1-(t:ℂ))^2*(R-D)‖ := norm_add_le _ _
      _ = t*‖R*B‖*‖R-1‖+(1-t)^2*‖R-D‖ := by simp only [norm_mul,norm_pow,htn,hon]
      _ ≤ t*‖R*B‖*(‖R‖+1)+(1-t)^2*(‖R‖+‖D‖) := by
        gcongr
        · simpa using norm_sub_le R (1:ℂ)
        · exact norm_sub_le R D
      _ ≤ t*‖R*B‖*(3/2)+1*(‖R‖+‖D‖) := by
        gcongr
        · linarith
        · nlinarith
      _ = _ := by ring
  have he0 : 0≤(3/2)*t*‖R*B‖+‖R‖+‖D‖ := by positivity
  have hp := mul_le_mul_of_nonneg_left hdb he0
  nlinarith [hp]

/-- The native correction differs from its exact leading mode by an absolute
error tending to zero on the whole right half-plane. -/
theorem principal_slot_leading_error {Q : ℝ} (hQ : 4≤Q) (A η s : ℂ)
    (hA : ‖A‖≤1) (hη : ‖η‖=1)
    (hR : ‖coordR Q A s (1/6)‖≤1/2) (hD : ‖coordD Q η 1 s‖≤1/4) :
    ‖principalSlot Q A η s+1-coordR Q A s (1/6)*(star η*(Q:ℂ)^s)‖ ≤
      3*Q^(2-5*s.re)+2*Q^(3-6*s.re)+2*Q^(-s.re) := by
  have hQ0 : 0<Q := by linarith
  have ht0 : 0≤Q⁻¹ := inv_nonneg.mpr hQ0.le
  have ht : Q⁻¹≤1/4 := by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) hQ
  rcases principal_slot_guards hQ A η s hR hD with ⟨h1t,hpt,h1R,h1D,hden⟩
  rw [principal_slot_exact hQ0 A η s hη h1t hpt h1R h1D hden]
  have hb := algebraic_leading_difference_bound (B := star η*(Q:ℂ)^s) ht0 ht hR hD
    (principal_coord_cancellation hQ0 η s hη)
  rw [Complex.ofReal_inv,native_D_norm hQ0 η s hη] at hb
  have hl := leading_norm_le hQ0 A η s hA hη
  have hr := coordR_norm_le Q hQ0 A s (1/6) hA
  norm_num at hr
  rw [show 4-6*s.re-1=3-6*s.re by ring] at hr
  calc
    _ ≤ 3*Q⁻¹*Q^(3-5*s.re)+2*Q^(3-6*s.re)+2*Q^(-s.re) := by
      apply hb.trans
      gcongr
    _ = _ := by rw [mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hQ0]; congr 2; ring

theorem principal_slot_leading_error_tendsto_zero {ι : Type*} {l : Filter ι}
    {Q : ι → ℝ} (hQ : Filter.Tendsto Q l Filter.atTop) (A η : ι → ℂ) (s : ℂ)
    (hA : ∀ n, ‖A n‖≤1) (hη : ∀ n, ‖η n‖=1) (hs : 1/2<s.re) :
    Filter.Tendsto (fun n => principalSlot (Q n) (A n) (η n) s+1-
      coordR (Q n) (A n) s (1/6)*(star (η n)*(Q n:ℂ)^s)) l (𝓝 0) := by
  have ha := tendsto_negative_power hQ (show 2-5*s.re<0 by linarith)
  have hb := tendsto_negative_power hQ (show 3-6*s.re<0 by linarith)
  have hc := tendsto_negative_power hQ (show -s.re<0 by linarith)
  have ht : Filter.Tendsto
      (fun n => 3*(Q n)^(2-5*s.re)+2*(Q n)^(3-6*s.re)+2*(Q n)^(-s.re)) l (𝓝 0) := by
    simpa using ((ha.const_mul 3).add (hb.const_mul 2)).add (hc.const_mul 2)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_principal_guards hQ A η s hA hη hs] with n hn
  exact principal_slot_leading_error hn.1 _ _ _ (hA n) (hη n) hn.2.1 hn.2.2

/-- At the exact transition, the compensated correction has modulus one,
so the minus-one centering cannot be extended to the closed `3/5` boundary. -/
theorem principal_slot_boundary_norm {ι : Type*} {l : Filter ι} {Q : ι → ℝ}
    (hQ : Filter.Tendsto Q l Filter.atTop) (A η : ι → ℂ) (s : ℂ)
    (hA : ∀ n, ‖A n‖=1) (hη : ∀ n, ‖η n‖=1) (hs : s.re=3/5) :
    Filter.Tendsto (fun n => ‖principalSlot (Q n) (A n) (η n) s+1‖) l (𝓝 1) := by
  have ht := principal_slot_leading_error_tendsto_zero hQ A η s (fun n => (hA n).le) hη
    (by rw [hs]; norm_num)
  have hn := tendsto_zero_iff_norm_tendsto_zero.mp ht
  have he : ∀ᶠ n in l,
      |‖principalSlot (Q n) (A n) (η n) s+1‖-1| ≤
      ‖principalSlot (Q n) (A n) (η n) s+1-
        coordR (Q n) (A n) s (1/6)*(star (η n)*(Q n:ℂ)^s)‖ := by
    filter_upwards [hQ.eventually_ge_atTop 4] with n hqn
    have hl : ‖coordR (Q n) (A n) s (1/6)*(star (η n)*(Q n:ℂ)^s)‖=1 := by
      rw [leading_norm (show 0<Q n by linarith) (A n) (η n) s (hA n) (hη n),hs]
      norm_num
    have hx := abs_norm_sub_norm_le
      (principalSlot (Q n) (A n) (η n) s+1)
      (coordR (Q n) (A n) s (1/6)*(star (η n)*(Q n:ℂ)^s))
    rw [hl] at hx
    exact hx
  have hz : Filter.Tendsto (fun n => ‖principalSlot (Q n) (A n) (η n) s+1‖-1) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (he.mono (fun _ h => by simpa only [Real.norm_eq_abs] using h)) hn
  simpa using hz.add_const 1

theorem weighted_slot_ne_zero {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i∈S, 0≤w i) (hB : ∀ i∈S, ‖B i+1‖≤δ)
    (hM : 0<∑ i∈S, w i) (hδ : δ<1) :
    (∑ i∈S, (w i:ℂ)*B i)≠0 := by
  intro hz
  have hb := weighted_slot_error S w B δ hw hB
  rw [hz,zero_add,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM] at hb
  nlinarith

/-- A finite actual all-power window has a nonzero native source multiplier
above `3/5`, when its displayed norm cutoff is sufficiently large.  No global
Euler correction or contour theorem below `7/8` is imported or inferred. -/
theorem actual_window_at_residue_ne_zero {ι : Type*} (η : Character)
    (J : Finset ι) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) (Pmin : ℝ)
    (hs : 3/5<s.re) (hP : 4≤Pmin)
    (hPr : Pmin^(3-6*s.re)≤1/2) (hPd : Pmin^(-s.re)≤1/4)
    (hsmall : 4*(Pmin^(3-5*s.re)+Pmin^(-s.re))<1)
    (hQ : ∀ j∈J, ∀ P∈T j, Pmin≤(Ideal.absNorm P.val:ℝ))
    (hη : ∀ j∈J, ∀ P∈T j, ‖idealCoeff η P.val‖=1)
    (hW : ∀ j∈J, ∀ P∈T j, 0≤W j ((Ideal.absNorm P.val:ℝ)/scale j))
    (hM : ∀ j∈J, 0<∑ P∈T j, W j ((Ideal.absNorm P.val:ℝ)/scale j)*
      (Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))) :
    windowMultiplier η J T (fun j t => (W j t:ℂ)) scale s 1 (1/6)≠0 := by
  rw [window_at_residue]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply weighted_slot_ne_zero (T j)
    (fun P => W j ((Ideal.absNorm P.val:ℝ)/scale j)*
      (Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)))
    (fun P => principalSlot (Ideal.absNorm P.val)
      (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s)
    (4*(Pmin^(3-5*s.re)+Pmin^(-s.re)))
  · intro P hPj
    exact mul_nonneg (hW j hj P hPj) (Real.rpow_nonneg (by positivity) _)
  · intro P hPj
    have hpq := hQ j hj P hPj
    have hqn : 4≤(Ideal.absNorm P.val:ℝ) := hP.trans hpq
    have hq0 : 0<(Ideal.absNorm P.val:ℝ) := by linarith
    have ha := actualAPhase_norm_le_one η (primaryGenerator P.val)
    have het := hη j hj P hPj
    have hr := coordR_norm_le (Ideal.absNorm P.val) hq0
      (actualAPhase η (primaryGenerator P.val)) s (1/6) ha
    norm_num at hr
    rw [show 4-6*s.re-1=3-6*s.re by ring] at hr
    have hrr : (Ideal.absNorm P.val:ℝ)^(3-6*s.re)≤Pmin^(3-6*s.re) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hpq (by linarith)
    have hdd : (Ideal.absNorm P.val:ℝ)^(-s.re)≤Pmin^(-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hpq (by linarith)
    have hll : (Ideal.absNorm P.val:ℝ)^(3-5*s.re)≤Pmin^(3-5*s.re) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hpq (by linarith)
    have hd : ‖coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s‖≤1/4 := by
      rw [native_D_norm hq0 _ _ het]
      exact hdd.trans hPd
    exact (principal_slot_upper hqn _ _ s ha het (by linarith)
      (hr.trans (hrr.trans hPr)) hd).trans (by linarith)
  · exact hM j hj
  · exact hsmall

/-- The cutoff requirements of the preceding finite native theorem are
available for every fixed exponent strictly above `3/5`. -/
theorem eventually_native_window_cutoff (s : ℂ) (hs : 3/5<s.re) :
    ∀ᶠ Pmin : ℝ in Filter.atTop,
      4≤Pmin ∧ Pmin^(3-6*s.re)≤1/2 ∧ Pmin^(-s.re)≤1/4 ∧
        4*(Pmin^(3-5*s.re)+Pmin^(-s.re))<1 := by
  have hr := tendsto_negative_power Filter.tendsto_id (show 3-6*s.re<0 by linarith)
  have hd := tendsto_negative_power Filter.tendsto_id (show -s.re<0 by linarith)
  have hl := tendsto_negative_power Filter.tendsto_id (show 3-5*s.re<0 by linarith)
  have hb : Filter.Tendsto (fun q : ℝ => 4*(q^(3-5*s.re)+q^(-s.re)))
      Filter.atTop (𝓝 0) := by simpa using (hl.add hd).const_mul 4
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ),
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),
    hd.eventually_le_const (by norm_num : (0:ℝ)<1/4),
    hb.eventually_lt_const (by norm_num : (0:ℝ)<1)] with q hq hqr hqd hqb
  exact ⟨hq,hqr,hqd,hqb⟩

end OpenAIReview.LowerStripSlot

#lint+ in OpenAIReview.LowerStripSlot

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty lower-strip slot audit."
  logInfo m!"Lower-strip slot audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-lower-strip-slot"
  IO.FS.writeFile ".lake/arithmetic-operator-lower-strip-slot/axioms.json"
    (Json.mkObj [("scope",toJson "native finite principal slot signs and compensation exponent; no global/source/contour or independent arithmetic estimate"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
