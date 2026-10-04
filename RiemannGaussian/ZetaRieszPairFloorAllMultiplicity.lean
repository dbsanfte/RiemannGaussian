/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJoinedSourceError
import RiemannGaussian.ZetaRieszShiftedCenter

/-!
# One retained-pair upper bound suffices for every multiplicity

The current literal prefix pair defect has source m^2*(1-retainedCost u).
Thus the SAME independent 399/5000 upper bound excludes every positive
analytic multiplicity, without needing the older separate ceiling.

The arithmetic upper bound remains an explicit unproved premise. This
module supplies no new zero exclusion, independent floor saving or carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPairFloorAllMultiplicity
open ZetaRieszSelbergSourceAudit ZetaRieszJoinedSourceError
open ZetaRieszPairPrefixPayment ZetaRieszPrimeCountFrequency

/-- The existing joined evaluator is homogeneous of degree two; its
literal integer endpoints and moving length are unchanged. -/
theorem harmonicEvaluation_mul (a : ℕ→ℂ) (c : ℂ) (u : ℝ) (N : ℕ) :
    harmonicEvaluation (fun k => c*a k) u N=c^2*harmonicEvaluation a u N := by
  have hp i j : (c*a i)*(c*a j)=c^2*(a i*a j) := by ring
  unfold harmonicEvaluation
  simp_rw [hp,mul_div_assoc]
  rw [←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]
  ring

/-- All multiplicities share the same selected quadratic shape. No
simple-zero hypothesis is used to compute this source limit. -/
theorem tendsto_selected_evaluation (rho : NontrivialZetaZero)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => harmonicEvaluation
      (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ)) (3/2-rho.1.re) N)
      atTop (𝓝 (((analyticZetaZeroMultiplicity rho : ℝ)^2*
        (1-ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re)) : ℝ) : ℂ)) := by
  have hu : 0<3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have huq : 3/2-rho.1.re≤(3/5 : ℝ) := by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
    linarith only [hU]
  have ht := (harmonicEvaluation_tendsto (fun _ => (-1 : ℂ)) tendsto_const_nhds hu huq).const_mul
    ((analyticZetaZeroMultiplicity rho : ℂ)^2)
  convert ht.congr (fun N => (harmonicEvaluation_mul (fun _ => (-1 : ℂ))
    (analyticZetaZeroMultiplicity rho : ℂ) (3/2-rho.1.re) N).symm) using 1 <;> push_cast <;> simp

/-- The quantitative whole-source error price transfers the exact
selected limit to the SAME literal prefix carrier, for arbitrary m. -/
theorem tendsto_prefix_exact_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (prefixPairDefect (3/2-rho.1.re) rho.1.im) atTop
      (𝓝 (((analyticZetaZeroMultiplicity rho : ℝ)^2*
        (1-ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re)) : ℝ) : ℂ)) := by
  have hy : 54≤|rho.1.im| := (ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho).le
  have hu : 0≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hb := (ZetaRieszPairWholeCompletion.wholeCompletionBudget_tendsto.add
    (ZetaRieszPairJointQuadratic.squareBudget_tendsto hu hU)).add
      (tendsto_source_error_price rho)
  simp only [add_zero] at hb
  have hd : Tendsto (fun N : ℕ => prefixPairDefect (3/2-rho.1.re) rho.1.im N-
      harmonicEvaluation (fun _ => -(analyticZetaZeroMultiplicity rho : ℂ))
        (3/2-rho.1.re) N) atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop 65536).mono fun N hN =>
      norm_prefix_sub_selected_le rho hrho hexposed hU hy hN) hb
  simpa only [sub_add_cancel,zero_add] using hd.add (tendsto_selected_evaluation rho hU)

/-- Positive integer multiplicity only INCREASES this source. The
unchanged 399/5000 target is strictly below even its simple-zero value. -/
theorem target_lt_multiple_source {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 0 < m) :
    (399/5000 : ℝ)<(m : ℝ)^2*(1-ZetaRieszMaskSupport.retainedCost u) := by
  have hc := ZetaRieszEndgameSlack.retainedCost_upper hu hU
  have hs : (399/5000 : ℝ)<1-ZetaRieszMaskSupport.retainedCost u := by linarith only [hc]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hsq : 1≤(m : ℝ)^2 := by nlinarith only [hmR]
  have hp := mul_nonneg (show 0≤(m : ℝ)^2-1 by linarith only [hsq])
    (show 0≤1-ZetaRieszMaskSupport.retainedCost u by linarith only [hs])
  nlinarith only [hs,hp]

/-- The SAME fixed target on any cofinal sequence excludes EVERY
analytic multiplicity. The arithmetic bound is explicitly a premise. -/
theorem false_of_prefix_cofinal_bound (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (orders : ℕ→ℕ) (horders : Tendsto orders atTop atTop)
    (err : ℕ→ℝ) (he : Tendsto err atTop (𝓝 0))
    (hf : ∃ᶠ j in atTop,
      (prefixPairDefect (3/2-rho.1.re) rho.1.im (orders j)).re≤399/5000+err j) : False := by
  have hs := (Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_prefix_exact_source rho hrho hexposed hU)).comp horders
  simp only [Complex.ofReal_re] at hs
  have hh : (analyticZetaZeroMultiplicity rho : ℝ)^2*
      (1-ZetaRieszMaskSupport.retainedCost (3/2-rho.1.re))-0≤(399/5000 : ℝ) :=
    le_of_tendsto_of_frequently (hs.sub he) (hf.mono fun j hj => by
      dsimp only [Function.comp_def]
      linarith only [hj])
  simp only [sub_zero] at hh
  have hu : 1/2≤3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  exact (not_le_of_gt (target_lt_multiple_source hu hU
    (analyticZetaZeroMultiplicity_positive rho))) hh

/-- Specialize directly to the repository's native dyadic sequence.
No extra ceiling or simple-zero premise is needed for this target. -/
theorem false_of_native_prefix_bound (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling)
    (err : ℕ→ℝ) (he : Tendsto err atTop (𝓝 0))
    (hf : ∃ᶠ j in atTop,
      (prefixPairDefect (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j)).re≤399/5000+err j) : False :=
  false_of_prefix_cofinal_bound rho hrho hexposed hU dyadicMomentOrder
    tendsto_dyadicMomentOrder err he hf

/-- A conditional restricted zero exclusion from the SAME independent
arithmetic target. The premise must still be proved; no region is claimed
here. Exposure is obtained by the existing valid single-disk successor
theorem, not a generic mixed-mode rightward-chain argument. -/
theorem no_candidate_zero_of_independent_prefix_bounds
    (hbound : ∀ (u y : ℝ),1/2<u → u≤ZetaRieszWideOwnerAudit.radiusCeiling →
      54≤|y| → ∃ err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
        ∃ᶠ j in atTop,(prefixPairDefect u y (dyadicMomentOrder j)).re≤399/5000+err j)
    (rho0 : NontrivialZetaZero) (hbeta : (19999/20000 : ℝ)≤rho0.1.re) : False := by
  have hrho0 : 1/2<rho0.1.re := by linarith only [hbeta]
  obtain ⟨rho,hre,hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho0 hrho0
  have hrho : 1/2<rho.1.re := hrho0.trans_le hre
  have hu : 1/2<3/2-rho.1.re := by linarith only [NontrivialZetaZero.re_lt_one rho]
  have hU : 3/2-rho.1.re≤ZetaRieszWideOwnerAudit.radiusCeiling := by
    unfold ZetaRieszWideOwnerAudit.radiusCeiling
    linarith only [hbeta,hre]
  have hy := (ZetaRieszShiftedCenter.height_gt_fiftyFour rho hrho).le
  obtain ⟨err,he,hf⟩ := hbound (3/2-rho.1.re) rho.1.im hu hU hy
  exact false_of_native_prefix_bound rho hrho hexposed hU err he hf

end RiemannGaussian.ZetaRieszPairFloorAllMultiplicity
