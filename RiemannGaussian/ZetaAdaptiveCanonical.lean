/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaLocalResidualLog

/-!
# Adaptive canonical discs reaching the critical line

The actual pole-removed zeta function admits zero-free boundary radii
arbitrarily close to one about its safe center. The complete residual
retains the eta upper bound, the Moebius center floor, and the uniform
logarithmic derivative estimate on the inner half-disc. No unweighted
count of zeros near the unit boundary is required here.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

variable (r : Set.Ico (3 / 4 : ℝ) 1)

/-- A complete local divisor admits a zero-free sphere in a fixed
interval of radii around every real ordinate. -/
theorem exists_adaptiveZetaSphere_zeroFree (y : ℝ) : ∃ R : ℝ,
    r.1 < R ∧ R < 1 ∧ ∀ z : ℂ, ‖z‖ = R → localZetaPoleRemoved y z ≠ 0 := by
  let f := localZetaPoleRemoved y
  let CB : Set ℂ := closedBall 0 (1 : ℝ)
  have han := analyticOnNhd_localZetaPoleRemoved_unitDisc y
  have horders : ∀ u : CB, meromorphicOrderAt f u ≠ ⊤ :=
    fun u ↦ meromorphicOrderAt_localZetaPoleRemoved_ne_top y u.property
  have hzeros : (CB ∩ f ⁻¹' {0}).Finite := by
    rw [han.meromorphicNFOn.zero_set_eq_divisor_support horders]
    exact (divisor f CB).finiteSupport (isCompact_closedBall 0 1)
  let bad : Finset ℝ := hzeros.toFinset.image norm
  have hnot : ¬Ioo r.1 (1 : ℝ) ⊆ (bad : Set ℝ) := by
    intro h
    exact (Set.Ioo_infinite r.property.2) (bad.finite_toSet.subset h)
  obtain ⟨R, hR, hbad⟩ := Set.not_subset.mp hnot
  refine ⟨R, hR.1, hR.2, fun z hz hzero ↦ ?_⟩
  apply hbad
  apply Finset.mem_coe.mpr
  apply Finset.mem_image.mpr
  refine ⟨z, ?_, hz⟩
  rw [Set.Finite.mem_toFinset]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall, dist_zero_right, hz]
  linarith [hR.2]

/-- A selected local radius with no zeros on its boundary. -/
def adaptiveZetaCanonicalRadius (y : ℝ) : ℝ := Classical.choose (exists_adaptiveZetaSphere_zeroFree r y)

/-- The selected radius lies in the fixed interval and its sphere is zero-free. -/
theorem adaptiveZetaCanonicalRadius_spec (y : ℝ) :
    r.1 < adaptiveZetaCanonicalRadius r y ∧ adaptiveZetaCanonicalRadius r y < 1 ∧
      ∀ z : ℂ, ‖z‖ = adaptiveZetaCanonicalRadius r y → localZetaPoleRemoved y z ≠ 0 :=
  Classical.choose_spec (exists_adaptiveZetaSphere_zeroFree r y)

/-- The selected canonical radius is positive. -/
theorem adaptiveZetaCanonicalRadius_pos (y : ℝ) : 0 < adaptiveZetaCanonicalRadius r y :=
  (by linarith [r.property.1] : 0 < r.1).trans (adaptiveZetaCanonicalRadius_spec r y).1

/-- The local function is analytic on the selected closed disc. -/
theorem analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc (y : ℝ) :
    AnalyticOnNhd ℂ (localZetaPoleRemoved y) (closedBall 0 (adaptiveZetaCanonicalRadius r y)) :=
  fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z

/-- The complete divisor vanishes on the chosen boundary sphere. -/
theorem divisor_adaptiveZetaPoleRemoved_sphere_eq_zero (y : ℝ) :
    divisor (localZetaPoleRemoved y) (sphere 0 (adaptiveZetaCanonicalRadius r y)) = 0 := by
  have han : AnalyticOnNhd ℂ (localZetaPoleRemoved y) (sphere 0 (adaptiveZetaCanonicalRadius r y)) :=
    fun z _ ↦ (differentiable_localZetaPoleRemoved y).analyticAt z
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) (adaptiveZetaCanonicalRadius r y)
  · have hfz := (adaptiveZetaCanonicalRadius_spec r y).2.2 z
      (by simpa only [mem_sphere, dist_zero_right] using hz)
    have ho : meromorphicOrderAt (localZetaPoleRemoved y) z = 0 :=
      (han z hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
    rw [han.meromorphicOn.divisor_apply hz]
    simp [ho]
  · change (if MeromorphicOn (localZetaPoleRemoved y) (sphere 0 (adaptiveZetaCanonicalRadius r y)) ∧
        z ∈ sphere 0 (adaptiveZetaCanonicalRadius r y) then _ else 0) = 0
    rw [if_neg (fun h ↦ hz h.2)]

/-- The actual local function admits a finite canonical decomposition
with a residual nonvanishing throughout the complete closed disc. -/
theorem exists_adaptiveZetaECanonicalDecomp (y : ℝ) : ∃ g : ℂ → ℂ,
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) g (adaptiveZetaCanonicalRadius r y) := by
  apply MeromorphicOn.exists_ecanonicalDecomp
    (analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y).meromorphicOn
  intro z
  apply meromorphicOrderAt_localZetaPoleRemoved_ne_top y
  exact (closedBall_subset_closedBall (by linarith [(adaptiveZetaCanonicalRadius_spec r y).2.1])) z.property

/-- The complete zero-free local residual of pole-removed zeta. -/
def adaptiveZetaCanonicalResidual (y : ℝ) : ℂ → ℂ := Classical.choose (exists_adaptiveZetaECanonicalDecomp r y)

/-- The residual satisfies the actual complete canonical decomposition. -/
theorem adaptiveZetaCanonicalResidual_decomp (y : ℝ) :
    Complex.ECanonicalDecomp (localZetaPoleRemoved y) (adaptiveZetaCanonicalResidual r y) (adaptiveZetaCanonicalRadius r y) :=
  Classical.choose_spec (exists_adaptiveZetaECanonicalDecomp r y)


/-- Removing every interior zero by its canonical factor preserves
the exact norm on the selected zero-free boundary. -/
theorem norm_adaptiveZetaCanonicalResidual_eq_on_sphere (y : ℝ) {z : ℂ}
    (hz : z ∈ sphere 0 (adaptiveZetaCanonicalRadius r y)) :
    ‖adaptiveZetaCanonicalResidual r y z‖ = ‖localZetaPoleRemoved y z‖ := by
  let f := localZetaPoleRemoved y
  let g := adaptiveZetaCanonicalResidual r y
  let R := adaptiveZetaCanonicalRadius r y
  have hR := adaptiveZetaCanonicalRadius_pos r y
  have han := analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y
  have hfz := (adaptiveZetaCanonicalRadius_spec r y).2.2 z
    (by simpa only [mem_sphere, dist_zero_right] using hz)
  have ho : meromorphicOrderAt f z = 0 :=
    (han z (sphere_subset_closedBall hz)).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hl := (adaptiveZetaCanonicalResidual_decomp r y).log_norm_eq (sphere_subset_closedBall hz) ho hR
  have hcanonical : (∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
      Real.log ‖Complex.canonicalFactor R i z‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem := (divisor f (ball 0 R)).supportWithinDomain hi
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one himem hz, Real.log_one, mul_zero]
  have hS : divisor f (sphere 0 R) = 0 := divisor_adaptiveZetaPoleRemoved_sphere_eq_zero r y
  have hsphere : (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) * Real.log ‖z - i‖) = 0 := by
    rw [hS]
    simp
  have ht : meromorphicTrailingCoeffAt f z = f z :=
    (han z (sphere_subset_closedBall hz)).meromorphicTrailingCoeffAt_of_ne_zero hfz
  change Real.log ‖g z‖ = _ at hl
  rw [hcanonical, hsphere, ht] at hl
  simp only [sub_zero, zero_add] at hl
  have hgp : 0 < ‖g z‖ := norm_pos_iff.mpr
    ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero z (sphere_subset_closedBall hz))
  have hfp : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using congrArg Real.exp hl

/-- The actual local eta envelope bounds the complete residual
throughout the selected closed disc. -/
theorem norm_adaptiveZetaCanonicalResidual_le (y : ℝ) {z : ℂ}
    (hz : z ∈ closedBall 0 (adaptiveZetaCanonicalRadius r y)) :
    ‖adaptiveZetaCanonicalResidual r y z‖ ≤ 8 * (|y| + 22) ^ 2 := by
  have hR := adaptiveZetaCanonicalRadius_pos r y
  have hdiff : DiffContOnCl ℂ (adaptiveZetaCanonicalResidual r y) (ball 0 (adaptiveZetaCanonicalRadius r y)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (adaptiveZetaCanonicalResidual_decomp r y).analyticOnNhd.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff (z := z)
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_adaptiveZetaCanonicalResidual_eq_on_sphere r y hw]
    apply norm_localZetaPoleRemoved_le
    exact (closedBall_subset_closedBall (by linarith [(adaptiveZetaCanonicalRadius_spec r y).2.1]))
      (sphere_subset_closedBall hw)
  · rwa [closure_ball 0 hR.ne']

/-- The exact safe-center norm is not diminished by removal of the
complete analytic divisor. -/
theorem norm_adaptiveZetaPoleRemoved_zero_le_residual (y : ℝ) :
    ‖localZetaPoleRemoved y 0‖ ≤ ‖adaptiveZetaCanonicalResidual r y 0‖ := by
  let f := localZetaPoleRemoved y
  let g := adaptiveZetaCanonicalResidual r y
  let R := adaptiveZetaCanonicalRadius r y
  have hR := adaptiveZetaCanonicalRadius_pos r y
  have hz : (0 : ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have han := analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y
  have hf0 := localZetaPoleRemoved_zero_ne_zero y
  have ho : meromorphicOrderAt f 0 = 0 :=
    (han 0 hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf0
  have hl := (adaptiveZetaCanonicalResidual_decomp r y).log_norm_eq hz ho hR
  have hcanonical : 0 ≤ ∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
      Real.log ‖Complex.canonicalFactor R i 0‖ := by
    apply finsum_nonneg
    intro i
    by_cases hi : divisor f (ball 0 R) i = 0
    · simp [hi]
    · have himem := (divisor f (ball 0 R)).supportWithinDomain hi
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        apply hi
        rw [(han.mono ball_subset_closedBall).meromorphicOn.divisor_apply]
        · have ho' : meromorphicOrderAt (localZetaPoleRemoved y) 0 = 0 := ho
          simp [ho']
        · simpa only [mem_ball, dist_zero_right, norm_zero] using hR
      have hn : ‖i‖ < R := by simpa only [mem_ball, dist_zero_right] using himem
      have hfactor : 1 ≤ ‖Complex.canonicalFactor R i 0‖ := by
        rw [norm_canonicalFactor_zero hR]
        exact (one_le_div (norm_pos_iff.mpr hi0)).mpr hn.le
      exact mul_nonneg (by exact_mod_cast (han.mono ball_subset_closedBall).divisor_nonneg i)
        (Real.log_nonneg hfactor)
  have hS : divisor f (sphere 0 R) = 0 := divisor_adaptiveZetaPoleRemoved_sphere_eq_zero r y
  have hsphere : (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) * Real.log ‖0 - i‖) = 0 := by
    rw [hS]
    simp
  have ht : meromorphicTrailingCoeffAt f 0 = f 0 := (han 0 hz).meromorphicTrailingCoeffAt_of_ne_zero hf0
  change Real.log ‖g 0‖ = _ at hl
  rw [hsphere, ht] at hl
  have hlog : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by rw [hl]; linarith
  have hgp : 0 < ‖g 0‖ := norm_pos_iff.mpr ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero 0 hz)
  have hfp : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  simpa only [Real.exp_log hgp, Real.exp_log hfp] using Real.exp_le_exp.mpr hlog

/-- The complete residual retains the explicit safe-center floor. -/
theorem sixteenth_le_norm_adaptiveZetaCanonicalResidual_zero (y : ℝ) :
    (1 / 16 : ℝ) ≤ ‖adaptiveZetaCanonicalResidual r y 0‖ :=
  (sixteenth_le_norm_localZetaPoleRemoved_zero y).trans (norm_adaptiveZetaPoleRemoved_zero_le_residual r y)


/-- The zero-free local residual has a normalized logarithmic primitive. -/
theorem exists_adaptiveZetaCanonicalLog (y : ℝ) : ∃ L : ℂ → ℂ, L 0 = 0 ∧
    ∀ z ∈ ball 0 (adaptiveZetaCanonicalRadius r y), HasDerivAt L (logDeriv (adaptiveZetaCanonicalResidual r y) z) z := by
  have hd : DifferentiableOn ℂ (logDeriv (adaptiveZetaCanonicalResidual r y))
      (ball 0 (adaptiveZetaCanonicalRadius r y)) := by
    intro z hz
    have hg := (adaptiveZetaCanonicalResidual_decomp r y).analyticOnNhd z (ball_subset_closedBall hz)
    have hl : AnalyticAt ℂ (logDeriv (adaptiveZetaCanonicalResidual r y)) z := by
      simpa only [logDeriv] using hg.deriv.div hg
        ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero z (ball_subset_closedBall hz))
    exact hl.differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at 0 0

/-- The chosen logarithm is normalized at the actual safe center. -/
def adaptiveZetaCanonicalLog (y : ℝ) : ℂ → ℂ := Classical.choose (exists_adaptiveZetaCanonicalLog r y)

/-- The normalized logarithm vanishes at the disc center. -/
@[simp] theorem adaptiveZetaCanonicalLog_zero (y : ℝ) : adaptiveZetaCanonicalLog r y 0 = 0 :=
  (Classical.choose_spec (exists_adaptiveZetaCanonicalLog r y)).1

/-- Its derivative is the actual local residual logarithmic derivative. -/
theorem adaptiveZetaCanonicalLog_hasDerivAt (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y)) :
    HasDerivAt (adaptiveZetaCanonicalLog r y) (logDeriv (adaptiveZetaCanonicalResidual r y) z) z :=
  (Classical.choose_spec (exists_adaptiveZetaCanonicalLog r y)).2 z hz

/-- Exponentiating the normalized logarithm recovers the whole local
residual, with its true center value retained. -/
theorem exp_adaptiveZetaCanonicalLog_mul_zero_eq (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y)) :
    Complex.exp (adaptiveZetaCanonicalLog r y z) * adaptiveZetaCanonicalResidual r y 0 = adaptiveZetaCanonicalResidual r y z := by
  let R := adaptiveZetaCanonicalRadius r y
  let g := adaptiveZetaCanonicalResidual r y
  let L := adaptiveZetaCanonicalLog r y
  let q : ℂ → ℂ := (fun w ↦ Complex.exp (-L w)) * g
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self (adaptiveZetaCanonicalRadius_pos r y)
  have hdiff : DifferentiableOn ℂ q (ball 0 R) := by
    intro w hw
    have hL := adaptiveZetaCanonicalLog_hasDerivAt r y hw
    have hg := (adaptiveZetaCanonicalResidual_decomp r y).analyticOnNhd w (ball_subset_closedBall hw)
    exact (hL.neg.cexp.mul hg.differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hderiv : EqOn (deriv q) 0 (ball 0 R) := by
    intro w hw
    have hL := adaptiveZetaCanonicalLog_hasDerivAt r y hw
    have hg := (adaptiveZetaCanonicalResidual_decomp r y).analyticOnNhd w (ball_subset_closedBall hw)
    have hq : HasDerivAt q
        (Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w) w :=
      hL.neg.cexp.mul hg.differentiableAt.hasDerivAt
    rw [hq.deriv]
    change Complex.exp (-L w) * (-logDeriv g w) * g w + Complex.exp (-L w) * deriv g w = 0
    rw [logDeriv_apply, mul_assoc (Complex.exp (-L w)) (-(deriv g w / g w)) (g w),
      neg_mul, div_mul_cancel₀ _ ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero w (ball_subset_closedBall hw))]
    ring
  have he := isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball hdiff hderiv hzero hz
  have hg0 : g 0 = Complex.exp (-L z) * g z := by
    simpa [q, L, adaptiveZetaCanonicalLog_zero r] using he
  change Complex.exp (L z) * g 0 = g z
  rw [hg0, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The actual upper envelope and center floor give a logarithmic
bound for the real part of the complete residual logarithm. -/
theorem adaptiveZetaCanonicalLog_re_le (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y)) :
    (adaptiveZetaCanonicalLog r y z).re ≤ 4 * localZetaLogHeight y := by
  have he := congrArg norm (exp_adaptiveZetaCanonicalLog_mul_zero_eq r y hz)
  rw [norm_mul, Complex.norm_exp] at he
  have hlow := sixteenth_le_norm_adaptiveZetaCanonicalResidual_zero r y
  have hu := norm_adaptiveZetaCanonicalResidual_le r y (ball_subset_closedBall hz)
  have hm := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (adaptiveZetaCanonicalLog r y z).re).le
  have ht : 128 ≤ (|y| + 22) ^ 2 := by nlinarith [abs_nonneg y]
  have hp := mul_le_mul_of_nonneg_right ht (sq_nonneg (|y| + 22))
  have hexp : Real.exp (4 * localZetaLogHeight y) = (|y| + 22) ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul,
      localZetaLogHeight, Real.exp_log (by positivity)]
  apply Real.exp_le_exp.mp
  rw [hexp]
  nlinarith

/-- The full complex logarithm obeys the Borel--Carathéodory bound
throughout the selected local disc. -/
theorem norm_adaptiveZetaCanonicalLog_le (y : ℝ) {z : ℂ}
    (hz : z ∈ ball 0 (adaptiveZetaCanonicalRadius r y)) :
    ‖adaptiveZetaCanonicalLog r y z‖ ≤
      8 * localZetaLogHeight y * ‖z‖ / (adaptiveZetaCanonicalRadius r y - ‖z‖) := by
  have hd : DifferentiableOn ℂ (adaptiveZetaCanonicalLog r y) (ball 0 (adaptiveZetaCanonicalRadius r y)) :=
    fun _ hw ↦ (adaptiveZetaCanonicalLog_hasDerivAt r y hw).differentiableAt.differentiableWithinAt
  have h := Complex.borelCaratheodory_zero
    (M := 4 * localZetaLogHeight y) (by linarith [two_lt_localZetaLogHeight y]) hd
    (fun _ hw ↦ adaptiveZetaCanonicalLog_re_le r y hw) (adaptiveZetaCanonicalRadius_pos r y) hz (adaptiveZetaCanonicalLog_zero r y)
  convert h using 1
  ring

/-- Cauchy's estimate bounds the complete residual logarithmic
derivative on the half-disc by an explicit logarithmic height. -/
theorem norm_logDeriv_adaptiveZetaCanonicalResidual_le (y : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logDeriv (adaptiveZetaCanonicalResidual r y) z‖ ≤ 320 * localZetaLogHeight y := by
  have hR : (3 / 4 : ℝ) < adaptiveZetaCanonicalRadius r y := by
    linarith [(adaptiveZetaCanonicalRadius_spec r y).1, r.property.1]
  have hL : 0 < localZetaLogHeight y := by linarith [two_lt_localZetaLogHeight y]
  have hbound {w : ℂ} (hw : w ∈ closedBall z (1 / 8 : ℝ)) : ‖w‖ ≤ 5 / 8 := by
    have hd : ‖w - z‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hn := norm_add_le (w - z) z
    rw [sub_add_cancel] at hn
    linarith
  have hsub : closedBall z (1 / 8 : ℝ) ⊆ ball 0 (adaptiveZetaCanonicalRadius r y) := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    linarith [hbound hw]
  have hd : DiffContOnCl ℂ (adaptiveZetaCanonicalLog r y) (ball z (1 / 8 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 8 : ℝ) ≠ 0)]
    intro w hw
    exact (adaptiveZetaCanonicalLog_hasDerivAt r y (hsub hw)).differentiableAt.differentiableWithinAt
  have hsphere : ∀ w ∈ sphere z (1 / 8 : ℝ), ‖adaptiveZetaCanonicalLog r y w‖ ≤ 40 * localZetaLogHeight y := by
    intro w hw
    have hnorm := hbound (sphere_subset_closedBall hw)
    have hden : 0 < adaptiveZetaCanonicalRadius r y - ‖w‖ := by linarith
    apply (norm_adaptiveZetaCanonicalLog_le r y (hsub (sphere_subset_closedBall hw))).trans
    rw [div_le_iff₀ hden]
    nlinarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 8) hd hsphere
  rw [(adaptiveZetaCanonicalLog_hasDerivAt r y (by simpa using (show ‖z‖ < adaptiveZetaCanonicalRadius r y by linarith))).deriv] at h
  convert h using 1
  ring


/-- The complete radial Jensen weight, with every analytic multiplicity
retained even when the chosen radius approaches the unit boundary. -/
def adaptiveZetaJensenWeight (y : ℝ) : ℝ :=
  ∑ᶠ i : ℂ, (divisor (localZetaPoleRemoved y) (ball 0 (adaptiveZetaCanonicalRadius r y)) i : ℝ) *
    Real.log (adaptiveZetaCanonicalRadius r y / ‖i‖)

/-- The weighted zero mass is exactly the logarithmic gain at the safe
center under removal of the complete canonical divisor. -/
theorem adaptiveZetaJensenWeight_eq_log_ratio (y : ℝ) :
    adaptiveZetaJensenWeight r y =
      Real.log (‖adaptiveZetaCanonicalResidual r y 0‖ / ‖localZetaPoleRemoved y 0‖) := by
  let f := localZetaPoleRemoved y
  let R := adaptiveZetaCanonicalRadius r y
  have hR := adaptiveZetaCanonicalRadius_pos r y
  have hz : (0 : ℂ) ∈ closedBall 0 R := by simpa using hR.le
  have han := analyticOnNhd_adaptiveZetaPoleRemoved_canonicalDisc r y
  have hf0 := localZetaPoleRemoved_zero_ne_zero y
  have ho : meromorphicOrderAt f 0 = 0 :=
    (han 0 hz).meromorphicNFAt |>.meromorphicOrderAt_eq_zero_iff.mpr hf0
  have hl := (adaptiveZetaCanonicalResidual_decomp r y).log_norm_eq hz ho hR
  have hS : divisor f (sphere 0 R) = 0 := divisor_adaptiveZetaPoleRemoved_sphere_eq_zero r y
  have hsphere : (∑ᶠ i : ℂ, ((divisor f (sphere 0 R) i : ℤ) : ℝ) * Real.log ‖0 - i‖) = 0 := by
    rw [hS]
    simp
  have ht : meromorphicTrailingCoeffAt f 0 = f 0 :=
    (han 0 hz).meromorphicTrailingCoeffAt_of_ne_zero hf0
  rw [hsphere, ht] at hl
  simp only [sub_zero] at hl
  have hc : (∑ᶠ i : ℂ, ((divisor f (ball 0 R) i : ℤ) : ℝ) *
      Real.log ‖Complex.canonicalFactor R i 0‖) = adaptiveZetaJensenWeight r y := by
    apply finsum_congr
    intro i
    rw [norm_canonicalFactor_zero hR]
  rw [hc] at hl
  have hg0 : ‖adaptiveZetaCanonicalResidual r y 0‖ ≠ 0 := norm_ne_zero_iff.mpr
    ((adaptiveZetaCanonicalResidual_decomp r y).ne_zero 0 hz)
  rw [Real.log_div hg0 (norm_ne_zero_iff.mpr hf0)]
  linarith

/-- The full boundary-weighted zero mass has a uniform logarithmic
budget independent of how close the selected radius is to one. -/
theorem adaptiveZetaJensenWeight_le (y : ℝ) :
    adaptiveZetaJensenWeight r y ≤ 4 * localZetaLogHeight y := by
  rw [adaptiveZetaJensenWeight_eq_log_ratio]
  have hfloor := sixteenth_le_norm_localZetaPoleRemoved_zero y
  have hfpos : 0 < ‖localZetaPoleRemoved y 0‖ := by linarith
  have hu := norm_adaptiveZetaCanonicalResidual_le r y
    (show (0 : ℂ) ∈ closedBall 0 (adaptiveZetaCanonicalRadius r y) by
      simpa using (adaptiveZetaCanonicalRadius_pos r y).le)
  have hgpos : 0 < ‖adaptiveZetaCanonicalResidual r y 0‖ := by
    linarith [sixteenth_le_norm_adaptiveZetaCanonicalResidual_zero r y]
  have hratio : ‖adaptiveZetaCanonicalResidual r y 0‖ / ‖localZetaPoleRemoved y 0‖ ≤
      (|y| + 22) ^ 4 := by
    rw [div_le_iff₀ hfpos]
    have ht : 128 ≤ (|y| + 22) ^ 2 := by nlinarith [abs_nonneg y]
    have hp := mul_le_mul_of_nonneg_right ht (sq_nonneg (|y| + 22))
    have hf := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by positivity : 0 ≤ |y| + 22) 4)
    nlinarith
  calc
    _ ≤ Real.log ((|y| + 22) ^ 4) := Real.log_le_log (div_pos hgpos hfpos) hratio
    _ = _ := by rw [Real.log_pow]; rfl

end

end RiemannGaussian
