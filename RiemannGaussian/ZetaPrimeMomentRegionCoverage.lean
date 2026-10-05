/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentNoncoherenceStrip
import RiemannGaussian.ZetaRieszJoinedPhaseRadius

/-!
# Finite-height arithmetic-radius coverage

The existing discharged signed-pole theorem supplies a full analytic disk
on a larger finite range than the previous `log(|y|+3)≤1800` transfer.
This is coverage by an existing region, not an all-height arithmetic gain.
Published width formulas alone are not proofs of their nonvanishing inputs.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Metric Set Topology
namespace RiemannGaussian.ZetaPrimeMomentRegionCoverage
open ZetaPrimeMomentCoherence ZetaPrimeMomentNoncoherence

/-- A full arithmetic radius above the campaign ceiling. -/
def coveredRadius : ℝ := 500051/1000000

/-- Import interface for a discharged explicit region. A printed width
formula cannot supply `hregion`: a Lean proof of actual nonvanishing is
required. Heights, the open right edge, and the whole disk are retained. -/
theorem analytic_radius_of_explicit_region (width : ℝ→ℝ)
    (hregion : ∀ s : ℂ,3≤|s.im| → 1-width s.im<s.re → riemannZeta s≠0)
    {R w y : ℝ} (hR : R<3/4) (hy : 54≤|y|) (hmargin : R<1/2+w)
    (hw : ∀ t : ℝ,|t-y|≤R → w≤width t) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (center y) R) := by
  intro s hs
  have hd : ‖s-center y‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hs
  have hi : |s.im-y|≤R := by
    have h := (Complex.abs_im_le_norm (s-center y)).trans hd
    norm_num [ZetaPrimeMomentCoherence.center] at h
    exact h
  have hheight : 3≤|s.im| := by
    have h := abs_add_le (y-s.im) s.im
    rw [sub_add_cancel,abs_sub_comm y s.im] at h
    linarith only [h,hi,hy,hR]
  have hs1 : s≠1 := by intro he; norm_num [he] at hheight
  have hr : (3/2-R : ℝ) ≤ s.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm (s-center y)).trans hd)).1
    simp only [sub_re,center_re] at h
    linarith
  have hnon := hregion s hheight (by have := hw s.im hi; linarith)
  have ha := analyticOn_riemannZeta s
    (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact (ha.deriv.div ha hnon).neg

/-- The original, independently discharged signed-pole region covers
this disk through logarithmic height 2000. No exposure assumption enters. -/
theorem analytic_covered_radius {y : ℝ} (hy : 54≤|y|)
    (hlog : Real.log (|y|+3)≤2000) :
    AnalyticOnNhd ℂ (fun s => -logDeriv riemannZeta s)
      (closedBall (center y) coveredRadius) := by
  intro s hs
  have hd : ‖s-center y‖≤coveredRadius := by
    simpa only [mem_closedBall,dist_eq_norm] using hs
  have hr : (3/2-coveredRadius : ℝ) ≤ s.re := by
    have hl := (abs_le.mp ((Complex.abs_re_le_norm (s-center y)).trans hd)).1
    simp only [sub_re,center_re] at hl
    linarith
  have hi : |s.im-y|≤coveredRadius := by
    have h := (Complex.abs_im_le_norm (s-center y)).trans hd
    norm_num [ZetaPrimeMomentCoherence.center] at h
    exact h
  have hb : |s.im|+2≤|y|+3 := by
    have h := abs_add_le (s.im-y) y
    rw [sub_add_cancel] at h
    dsimp [coveredRadius] at hi
    linarith
  have hls : Real.log (|s.im|+2)≤2000 :=
    (Real.log_le_log (by positivity) hb).trans hlog
  have hw : coveredRadius-1/2<zetaSignedPoleZeroMargin s.im := by
    unfold zetaSignedPoleZeroMargin coveredRadius
    apply (lt_div_iff₀ (zetaSignedPole_denominator_pos s.im)).mpr
    linarith only [hls]
  have hs1 : s≠1 := by
    intro he
    rw [he] at hi
    norm_num [coveredRadius] at hi
    linarith
  have ha := analyticOn_riemannZeta s
    (by simpa only [mem_compl_iff,mem_singleton_iff] using hs1)
  exact (ha.deriv.div ha (riemannZeta_ne_zero_of_signedPole_margin hs1
    (by linarith))).neg

/-- All actual ordinary-prime orders have this full-radius Cauchy bound. -/
theorem exists_ordinary_bound {y : ℝ} (hy : 54≤|y|)
    (hlog : Real.log (|y|+3)≤2000) :
    ∃ C : ℝ,0<C ∧ ∀ k : ℕ,
      ‖zetaOrdinaryPrimeLogMoment k (center y)‖≤C/coveredRadius^k :=
  ZetaRieszJoinedPhaseRadius.ordinary_moment_bound_of_analytic_radius
    (by norm_num [coveredRadius]) (by norm_num [coveredRadius])
    (analytic_covered_radius hy hlog)

/-- A genuine finite-height decay theorem, uniform in the campaign
radius. The Cauchy constant may depend on the fixed height. -/
theorem exists_moment_geometric_bound {y : ℝ} (hy : 54≤|y|)
    (hlog : Real.log (|y|+3)≤2000) :
    ∃ C : ℝ,0<C ∧ ∀ u : ℝ,0≤u →
      u≤ZetaPrimeMomentNoncoherenceStrip.campaignRadius → ∀ k : ℕ,
        ‖moments u y k‖≤C*(500050/500051 : ℝ)^k := by
  obtain ⟨C,hC,hm⟩ := exists_ordinary_bound hy hlog
  refine ⟨C,hC,fun u hu hU k => ?_⟩
  have hr : u/coveredRadius≤(500050/500051 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [coveredRadius] : 0<coveredRadius)).mpr
    norm_num [coveredRadius,ZetaPrimeMomentNoncoherenceStrip.campaignRadius] at hU ⊢
    exact hU
  have hu1 : u≤1 := by
    dsimp [ZetaPrimeMomentNoncoherenceStrip.campaignRadius] at hU
    linarith
  rw [moments,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu]
  calc
    _ ≤ u^(k+1)*(C/coveredRadius^k) := mul_le_mul_of_nonneg_left (hm k) (by positivity)
    _ = C*u*(u/coveredRadius)^k := by rw [pow_succ,div_pow]; ring
    _ ≤ C*(u/coveredRadius)^k :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC.le hu1)
        (pow_nonneg (div_nonneg hu (by norm_num [coveredRadius])) k)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hu (by norm_num [coveredRadius])) hr k) hC.le

theorem tendsto_moments_zero_of_covered_height {u y : ℝ} (hu : 0≤u)
    (hU : u≤ZetaPrimeMomentNoncoherenceStrip.campaignRadius)
    (hy : 54≤|y|) (hlog : Real.log (|y|+3)≤2000) :
    Tendsto (moments u y) atTop (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := exists_moment_geometric_bound hy hlog
  apply squeeze_zero_norm (hb u hu hU)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ)≤500050/500051) (by norm_num)).const_mul C

/-- Already-covered finite heights satisfy the canonical non-coherence
premise. This says nothing about the uncovered all-height gap. -/
theorem noncoherent_of_covered_height {u y : ℝ} (hu : 0≤u)
    (hU : u≤ZetaPrimeMomentNoncoherenceStrip.campaignRadius)
    (hy : 54≤|y|) (hlog : Real.log (|y|+3)≤2000) : Noncoherent u y := by
  intro m hm ht
  have he := tendsto_nhds_unique (tendsto_moments_zero_of_covered_height hu hU hy hlog) ht
  have hn : (m : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  exact hn (by simpa using he.symm)

end RiemannGaussian.ZetaPrimeMomentRegionCoverage
