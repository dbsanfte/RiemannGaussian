/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnalyticFactorAudit

/-!
# Finite artificial-mode normalization: slice cancellation and the joint obstruction

Arbitrarily remote repeated negative modes interpolate a nonzero source
value on one normalized slice. Their generic weak inverse has triangular
support. The exact two-variable lift, however, has a polynomial trace on
the selected pole surface; it cannot match the toy analytic factor there
on any open neighborhood. No physical cutoff or arithmetic packet is changed.
-/

namespace RiemannGaussian.ZetaRieszArtificialModeAudit
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators Classical
open ZetaRieszAnalyticFactorAudit

/-- A coherent logarithmic choice of the small artificial-mode parameter. -/
def offset (b : ℂ) (m : ℕ) : ℂ := 1-Complex.exp (-b/(m+1 : ℂ))

/-- The normalized one-variable factor, with m repeated negative modes. -/
def sliceFactor (m : ℕ) (a t : ℂ) : ℂ := 1/(1-a*t)^m

theorem sliceFactor_zero (m : ℕ) (a : ℂ) : sliceFactor m a 0 = 1 := by
  simp [sliceFactor]

theorem sliceFactor_offset_one (b : ℂ) (m : ℕ) :
    sliceFactor (m+1) (offset b m) 1 = Complex.exp b := by
  simp only [sliceFactor, offset, mul_one, sub_sub_cancel]
  rw [← Complex.exp_nat_mul]
  have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [show ((m+1 : ℕ) : ℂ)*(-b/(m+1 : ℂ)) = -b by push_cast; field_simp]
  simp [Complex.exp_neg]

theorem offset_tendsto_zero (b : ℂ) : Tendsto (offset b) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => -b/(m+1 : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, one_mul, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (-b)
  have he := (Complex.continuous_exp.tendsto 0).comp h
  convert! (tendsto_const_nhds (x := (1 : ℂ))).sub he using 1
  simp

/-- Any nonzero interpolation value can be matched with an arbitrarily
small parameter, hence with poles outside any prescribed fixed disk. -/
theorem exists_small_interpolator {h : ℂ} (hh : h ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : ℂ, ‖a‖ < eps ∧
      sliceFactor m a 0 = 1 ∧ sliceFactor m a 1 = h := by
  have he := (offset_tendsto_zero (Complex.log h)).norm.eventually
    (gt_mem_nhds (by simpa using heps))
  obtain ⟨m, hm⟩ := he.exists
  refine ⟨m+1, Nat.succ_pos _, offset (Complex.log h) m, ?_, sliceFactor_zero _ _, ?_⟩
  · simpa using hm
  · rw [sliceFactor_offset_one, Complex.exp_log hh]

/-- Dividing by the interpolator preserves both requested endpoint values. -/
theorem normalized_endpoints {H : ℂ → ℂ} (h0 : H 0 = 1) (h1 : H 1 ≠ 0)
    {m : ℕ} {a : ℂ} (hv : sliceFactor m a 1 = H 1) :
    H 0/sliceFactor m a 0 = 1 ∧ H 1/sliceFactor m a 1 = 1 := by
  simp [sliceFactor_zero, h0, hv, h1]

/-- Renormalization is an exact algebraic decomposition of the same response. -/
theorem exact_factorization (P H Q : ℂ) (hQ : Q ≠ 0) :
    1-P*H = (1-P*Q)+P*Q*(1-H/Q) := by
  field_simp
  ring

/-- Pole exclusion for the interpolator on a prescribed closed disk. -/
theorem slice_denominator_ne_zero {a t : ℂ} {r : ℝ}
    (har : ‖a‖*r < 1) (ht : ‖t‖ ≤ r) : 1-a*t ≠ 0 := by
  intro he
  have hnorm : ‖a*t‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg a)).trans_lt har
  rw [← sub_eq_zero.mp he] at hnorm
  norm_num at hnorm

theorem analyticOnNhd_sliceFactor (m : ℕ) {a : ℂ} {r : ℝ} (har : ‖a‖*r < 1) :
    AnalyticOnNhd ℂ (sliceFactor m a) (Metric.closedBall 0 r) := by
  intro t ht
  apply analyticAt_const.div
    ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).pow m)
  exact pow_ne_zero _ (slice_denominator_ne_zero har (by simpa using ht))

/-- Equality of the source values makes the selected simple pole removable
on a single slice. This does not impose any two-variable condition. -/
theorem slice_removable {P H Q : ℂ → ℂ}
    (hP : AnalyticAt ℂ P 1) (hH : AnalyticAt ℂ H 1) (hQ : AnalyticAt ℂ Q 1)
    (hv : H 1 = Q 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      (fun t => P t*(Q t-H t)/(1-t)) =ᶠ[𝓝[≠] (1 : ℂ)] F := by
  let G := fun t => -P t*(Q t-H t)
  have hG : AnalyticAt ℂ G 1 := hP.neg.mul (hQ.sub hH)
  obtain ⟨F, hF, he⟩ := exists_analytic_poleTaylor_remainder hG 1
  refine ⟨F, hF, ?_⟩
  filter_upwards [he] with t ht
  simp only [poleTaylorPrincipalPart, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, iteratedDeriv_zero, one_mul, pow_one] at ht
  have hzero : G 1 = 0 := by simp [G, hv]
  rw [hzero, zero_div, sub_zero] at ht
  convert ht using 1
  dsimp [G]
  rw [show 1-t = -(t-1) by ring, div_neg]
  ring

/-- The slice cancellation patches across the selected point on the entire
working disk, provided the other factors are analytic there. -/
theorem slice_analytic_extension {P H Q : ℂ → ℂ} {r : ℝ} (hr : 1 < r)
    (hP : AnalyticOnNhd ℂ P (Metric.ball 0 r))
    (hH : AnalyticOnNhd ℂ H (Metric.ball 0 r))
    (hQ : AnalyticOnNhd ℂ Q (Metric.ball 0 r)) (hv : H 1 = Q 1) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧
      ∀ t, t ≠ 1 → F t = P t*(Q t-H t)/(1-t) := by
  have h1 : (1 : ℂ) ∈ Metric.ball 0 r := by simpa using hr
  obtain ⟨F, hF, he⟩ := exists_analyticAtOn_of_finite_removable
    (Metric.ball 0 r) ({1} : Finset ℂ) (fun t => P t*(Q t-H t)/(1-t))
    (by simpa using h1) (by
      intro t ht hne
      exact ((hP t ht).mul ((hQ t ht).sub (hH t ht))).div
        (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr (Ne.symm (by simpa using hne)))) (by
      intro t ht
      have ht1 : t = 1 := by simpa using ht
      subst t
      exact slice_removable (hP 1 h1) (hH 1 h1) (hQ 1 h1) hv)
  exact ⟨F, hF, fun t ht => he t (by simpa using ht)⟩

/-- Cauchy's bound for the patched slice: every intermediate radius gives
the claimed geometric coefficient decay. -/
theorem slice_geometric {P H Q : ℂ → ℂ} {r q : ℝ} (hq : 1 < q) (hqr : q < r)
    (hP : AnalyticOnNhd ℂ P (Metric.ball 0 r))
    (hH : AnalyticOnNhd ℂ H (Metric.ball 0 r))
    (hQ : AnalyticOnNhd ℂ Q (Metric.ball 0 r)) (hv : H 1 = Q 1) :
    ∃ F : ℂ → ℂ, (∀ t, t ≠ 1 → F t = P t*(Q t-H t)/(1-t)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖signedTaylorMoment n F 0‖ ≤ M/q^n := by
  obtain ⟨F, hF, he⟩ := slice_analytic_extension (hq.trans hqr) hP hH hQ hv
  have ha := hF.mono (Metric.closedBall_subset_ball hqr)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) q).image_of_continuousOn
    ha.continuousOn).isBounded.exists_norm_le
  refine ⟨F, he, M, (norm_nonneg _).trans (hM _
    ⟨0, Metric.mem_closedBall_self (by linarith), rfl⟩), fun n => ?_⟩
  have hd : DiffContOnCl ℂ F (Metric.ball 0 q) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by linarith : q ≠ 0)]
    exact ha.differentiableOn
  exact norm_signedTaylorMoment_le (by linarith : 0 < q) hd
    (fun t ht => hM _ ⟨t, Metric.sphere_subset_closedBall ht, rfl⟩) n

/-- A fixed finite family has precisely this two-variable count factor. -/
def finiteFactor {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w z : ℂ) : ℂ :=
  ∏ i ∈ A, (w-xi i)/(w+z-xi i)

/-- Restriction of a fixed finite-mode factor to the selected pole surface. -/
def surfaceFactor {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w : ℂ) : ℂ :=
  ∏ i ∈ A, (w-xi i)/(-xi i)

theorem finiteFactor_surface {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w : ℂ) :
    finiteFactor A xi w (-w) = surfaceFactor A xi w := by
  simp [finiteFactor, surfaceFactor]

/-- This is a polynomial function of the tangential coordinate w. -/
theorem analyticOnNhd_surfaceFactor {ι : Type*} (A : Finset ι) (xi : ι → ℂ) :
    AnalyticOnNhd ℂ (surfaceFactor A xi) univ := by
  intro w _
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (analyticAt_id.sub analyticAt_const).div_const

theorem repeated_factor_path (m : ℕ) {a : ℂ} (ha : a ≠ 0) (t : ℂ) :
    finiteFactor (Finset.range m) (fun _ => 1-1/a) 1 (-t) = sliceFactor m a t := by
  simp only [finiteFactor, Finset.prod_const, Finset.card_range, sliceFactor]
  have he : (1-(1-1/a))/(1+-t-(1-1/a)) = 1/(1-a*t) := by
    have hn : 1+-t-(1-1/a) = (1-a*t)/a := by field_simp; ring
    rw [hn]
    simp only [sub_sub_cancel, div_div]
    field_simp
  rw [he, div_pow, one_pow]

/-- Exact factorization inside the two-variable response. -/
def residualResponse {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w z : ℂ) : ℂ :=
  (w/(w+z))*(finiteFactor A xi w z-toyFactor w z)/z^2

theorem response_split {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w z : ℂ) :
    toyResponse w z =
      (1-(w/(w+z))*finiteFactor A xi w z)/z^2+residualResponse A xi w z := by
  unfold toyResponse residualResponse
  ring

/-- Adding arbitrary complex artificial locations retains exactly the
already-proved support theorem, with all boundary derivatives. -/
theorem augmented_support {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (r : ℕ)
    {f : ZetaRieszNegativeModeSupport.Test}
    (hf : tsupport (Function.uncurry f) ⊆ {x : ℝ×ℝ | x.2 < x.1}) :
    ZetaRieszNegativeModeSupport.inversePrimitive r
      (insert none (A.image some)) (fun i => Option.elim i 0 xi) f = 0 :=
  ZetaRieszNegativeModeSupport.inversePrimitive_support _ _ _ hf

theorem augmented_response {ι : Type*} (A : Finset ι) (xi : ι → ℂ) (w z : ℂ) :
    ZetaRieszNegativeModeCascade.response
      (insert none (A.image some)) (fun i => Option.elim i 0 xi) w z =
      (1-(w/(w+z))*finiteFactor A xi w z)/z^2 := by
  simp only [ZetaRieszNegativeModeCascade.response]
  rw [Finset.prod_insert (by simp)]
  rw [Finset.prod_image (by intro i _ j _ h; exact Option.some.inj h)]
  simp [finiteFactor]

/-- No fixed finite artificial family can match the toy factor along an
open piece of the selected pole surface. The obstruction holds locally
at w=1, not merely at a remote point of the inverse transform. -/
theorem not_eventually_surface_match {ι : Type*} (A : Finset ι) (xi : ι → ℂ) :
    ¬ (surfaceFactor A xi =ᶠ[𝓝 (1 : ℂ)] fun w => 1/(w+1)) := by
  intro h
  let F := fun w : ℂ => (w+1)*surfaceFactor A xi w
  have hF : AnalyticOnNhd ℂ F univ := by
    intro w hw
    exact (analyticAt_id.add analyticAt_const).mul (analyticOnNhd_surfaceFactor A xi w hw)
  have he : F =ᶠ[𝓝 (1 : ℂ)] fun _ => (1 : ℂ) := by
    have hn : ∀ᶠ w : ℂ in 𝓝 1, w+1 ≠ 0 :=
      (continuousAt_id.add continuousAt_const).eventually_ne (by norm_num)
    filter_upwards [h, hn] with w hw hn
    simp [F, hw, hn]
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) univ from fun _ _ => analyticAt_const)
    isPreconnected_univ (mem_univ (1 : ℂ)) he
  have hbad := hall (mem_univ (-1 : ℂ))
  norm_num [F] at hbad

/-- The surviving normal residue is the entire surface mismatch, divided
by w. Matching its value at w=1 does not cancel nearby normal poles. -/
theorem residual_normal_residue {ι : Type*} (A : Finset ι) (xi : ι → ℂ)
    (hxi : ∀ i ∈ A, xi i ≠ 0) {w : ℂ} (hw : w ≠ 0) (hw1 : w+1 ≠ 0) :
    Tendsto (fun z => (w+z)*residualResponse A xi w z) (𝓝[≠] (-w))
      (𝓝 ((surfaceFactor A xi w-1/(w+1))/w)) := by
  have hf : AnalyticAt ℂ (finiteFactor A xi w) (-w) := by
    apply Finset.analyticAt_fun_prod
    intro i hi
    apply analyticAt_const.div ((analyticAt_const.add analyticAt_id).sub analyticAt_const)
    simpa using hxi i hi
  have hh : AnalyticAt ℂ (toyFactor w) (-w) :=
    ((analyticAt_const.add analyticAt_id).add analyticAt_const).div_const
  have hc : ContinuousAt (fun z => w*(finiteFactor A xi w z-toyFactor w z)/z^2) (-w) :=
    (continuousAt_const.mul (hf.continuousAt.sub hh.continuousAt)).div
      (continuousAt_id.pow 2) (pow_ne_zero _ (neg_ne_zero.mpr hw))
  have he : (fun z => (w+z)*residualResponse A xi w z) =ᶠ[𝓝[≠] (-w)]
      (fun z => w*(finiteFactor A xi w z-toyFactor w z)/z^2) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ -w := by simpa using hz
    have hn : w+z ≠ 0 := by intro h; exact hz' (by linear_combination h)
    unfold residualResponse
    field_simp
  apply Tendsto.congr' he.symm
  have hv : w*(finiteFactor A xi w (-w)-toyFactor w (-w))/(-w)^2 =
      (surfaceFactor A xi w-1/(w+1))/w := by
    rw [finiteFactor_surface]
    simp only [toyFactor, add_neg_cancel, zero_add]
    field_simp
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem not_continuousAt_residual {ι : Type*} (A : Finset ι) (xi : ι → ℂ)
    (hxi : ∀ i ∈ A, xi i ≠ 0) {w : ℂ} (hw : w ≠ 0) (hw1 : w+1 ≠ 0)
    (hm : surfaceFactor A xi w ≠ 1/(w+1)) :
    ¬ ContinuousAt (residualResponse A xi w) (-w) := by
  intro hc
  have ht : Tendsto (fun z => (w+z)*residualResponse A xi w z)
      (𝓝[≠] (-w)) (𝓝 0) := by
    have hc' : ContinuousAt (fun z => (w+z)*residualResponse A xi w z) (-w) :=
      (continuousAt_const.add continuousAt_id).mul hc
    have ht' : Tendsto (fun z => (w+z)*residualResponse A xi w z) (𝓝 (-w)) (𝓝 0) := by
      simpa only [add_neg_cancel, zero_mul] using hc'.tendsto
    exact ht'.mono_left nhdsWithin_le_nhds
  have he := tendsto_nhds_unique (residual_normal_residue A xi hxi hw hw1) ht
  exact (div_ne_zero (sub_ne_zero.mpr hm) hw) he

/-- Every neighborhood of the normalized slice contains a genuine
uncancelled selected pole for every fixed finite artificial family. -/
theorem frequently_residual_pole {ι : Type*} (A : Finset ι) (xi : ι → ℂ)
    (hxi : ∀ i ∈ A, xi i ≠ 0) :
    ∃ᶠ w : ℂ in 𝓝 1, ¬ ContinuousAt (residualResponse A xi w) (-w) := by
  have hm : ∃ᶠ w : ℂ in 𝓝 1, surfaceFactor A xi w ≠ 1/(w+1) :=
    not_eventually.mp (not_eventually_surface_match A xi)
  have hw : ∀ᶠ w : ℂ in 𝓝 1, w ≠ 0 := continuousAt_id.eventually_ne (by norm_num)
  have hw1 : ∀ᶠ w : ℂ in 𝓝 1, w+1 ≠ 0 :=
    (continuousAt_id.add continuousAt_const).eventually_ne (by norm_num)
  exact (hm.and_eventually (hw.and hw1)).mono (fun w h =>
    not_continuousAt_residual A xi hxi h.2.1 h.2.2 h.1)

end
end RiemannGaussian.ZetaRieszArtificialModeAudit
