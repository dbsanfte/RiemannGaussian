/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastOrderOverflow

/-!
# The sufficient floor for the existing sum and its signed complement

No new carrier is defined. The lower-threshold packet minus its short
overflow stays coupled to `ZetaRieszLeastBoundary.rest`. Their source is
transported through already paid errors. For a SIMPLE exposed zero on the
restricted radius interval the exact source is below `-79/1000`, so a
cofinal joint floor at that level suffices. For multiplicity at least two
the same source is greater than `3/2`: that floor alone cannot contradict
it. An additional cofinal ceiling at `3/2` handles every higher multiplicity.
Both independent arithmetic bounds remain open hypotheses; neither summand
is required to decay. Exposure isolates a location, not its multiplicity.
-/

namespace RiemannGaussian.ZetaRieszJointFloor
noncomputable section
open Filter Topology
open ZetaRieszPrimeCountFrequency ZetaRieszMaskSupport ZetaRieszDominantAllocation
open ZetaRieszTypeII ZetaRieszParityPacket ZetaRieszLeastOrderOverflow

/-- A sharper source budget on the actual restricted radius interval.
This is a source-side scalar estimate, not an arithmetic lower bound. -/
theorem retainedCost_lt_restricted {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) : retainedCost u < 921/1000 := by
  have hu0 : 0 < u := by linarith
  have huU : u ≤ 10001/20000 := hU
  have hh := Real.log_le_sub_one_of_pos (show 0 < 2*u by positivity)
  rw [Real.log_mul (by norm_num) hu0.ne'] at hh
  have hlog2 : (6931/10000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*u by positivity)
  have hml := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2*u by positivity)
  have hq := mul_nonneg (show 0 ≤ u-1/2 by linarith)
    (show 0 ≤ 10001/20000-u by linarith)
  have hD : (693/1000 : ℝ) ≤ -2*u*Real.log u := by nlinarith
  have hDp : 0 < -2*u*Real.log u := by linarith
  have hhi : Real.log (32/13 : ℝ) < 901/1000 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 901/1000) 10
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hlo : (3794/10000 : ℝ) < Real.log (19/13) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 3/16)
      (by norm_num : (3/16 : ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hmul := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 921/1000+Real.log (19/13 : ℝ) by linarith)
  unfold retainedCost
  apply sub_lt_iff_lt_add.mpr
  apply (div_lt_iff₀ hDp).mpr
  nlinarith

/-- A lower bound for the SAME retained cost. This makes the change of
source sign at multiplicity two explicit; it is not an arithmetic bound. -/
theorem retainedCost_gt_nine_tenths {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) : 9/10 < retainedCost u := by
  have hu0 : 0 < u := by linarith
  have huU : u ≤ 10001/20000 := hU
  have hu1 : u < 1 := by linarith
  have hDp : 0 < -2*u*Real.log u := by
    have := Real.log_neg hu0 hu1
    nlinarith
  have hlog : -Real.log 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hu
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at h
    exact h
  have hlog2 : Real.log 2 < (694/1000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*u by positivity)
  have hm2 := mul_lt_mul_of_pos_left hlog2 (show 0 < 2*u by positivity)
  have hD : -2*u*Real.log u ≤ (7/10 : ℝ) := by nlinarith
  have hlo : (9/10 : ℝ) < Real.log (32/13) := by
    have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 19/45)
      (by norm_num : (19/45 : ℝ) < 1) 5
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hhi : Real.log (19/13 : ℝ) < 19/50 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 19/50) 8
    norm_num [Finset.sum_range_succ] at he
    linarith
  have hquot : (9/7 : ℝ) < Real.log (32/13)/(-2*u*Real.log u) := by
    apply (lt_div_iff₀ hDp).mpr
    linarith
  unfold retainedCost
  linarith

/-- Every higher-multiplicity source is positive and above the proposed
ceiling. Thus the existing negative floor cannot exclude these sources. -/
theorem multiple_source_gt_three_halves {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) {m : ℕ} (hm : 2 ≤ m) :
    (3/2 : ℝ) < -(m : ℝ)+(m : ℝ)^2*retainedCost u := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc := retainedCost_gt_nine_tenths hu hU
  have hp := mul_lt_mul_of_pos_left hc (show 0 < (m : ℝ)^2 by positivity)
  have hfactor := mul_nonneg (show 0 ≤ (m : ℝ)-2 by linarith)
    (show 0 ≤ 9*(m : ℝ)+8 by positivity)
  nlinarith

/-- Both existing window errors are paid before any split of the core.
No estimate for the packet or its complementary response is used. -/
theorem tendsto_nondominant_sub_core {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => nondominantRemainder u y j-
      (u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 0) := by
  have huU : u ≤ ZetaRieszTypeII.radiusCeiling := hU.trans (by
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling,ZetaRieszTypeII.radiusCeiling])
  obtain ⟨r,C,hr0,hr1,_,hb⟩ := exists_core_window_error
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const C).comp
    tendsto_dyadicMomentOrder
  simp only [Function.comp_def,zero_mul] at ht
  have he : Tendsto (fun j => narrowRemainder u y j-
      (u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_) ht
    simpa only [narrowRemainder,← mul_sub] using
      hb (dyadicMomentOrder j) (dyadicPrimeCount j) y u hu hU
  have h := (tendsto_nondominant_sub_narrow hu huU y).add he
  simp only [add_zero] at h
  exact h.congr' (Eventually.of_forall fun _ => by ring)

/-- The already proved errors also pay the replacement in the WHOLE
joint sum. Neither the packet nor its signed complement is bounded here. -/
theorem tendsto_nondominant_sub_joint {u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (fun j => nondominantRemainder u y j-
      (u : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket u y (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest u y (dyadicMomentOrder j) (dyadicPrimeCount j)))
      atTop (𝓝 0) := by
  have he := tendsto_full_sub_joint_boundary hu hU (fun _ => y)
    dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder
  have h := (tendsto_nondominant_sub_core hu hU y).add he
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with j
  rw [ZetaRieszLeastBoundary.core_ledger]
  ring

/-- The exact source is attached to the joined existing expressions,
not to either summand separately. All literal masks remain unchanged. -/
theorem tendsto_joint_exact_source (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun j => ((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
      (lowerThresholdPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)-
        shortOverflowPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)+
        ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
          (dyadicMomentOrder j) (dyadicPrimeCount j))) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)+
        (analyticZetaZeroMultiplicity rho : ℂ)^2*(retainedCost (3/2-rho.1.re) : ℂ))) := by
  have hu : 0 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs := (tendsto_nondominant_exact_source rho hrho hexposed
    (hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source)).sub
      (tendsto_nondominant_sub_joint hu hU rho.1.im)
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall fun _ => by ring)

/-- For a SIMPLE zero, a cofinal floor for the JOINT sum, with any vanishing real error,
would suffice. This hypothesis is open. In particular, no separate decay,
norm estimate, or one-sided floor for either component is required. -/
theorem false_of_joint_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -(79/1000 : ℝ)-err j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
            (dyadicMomentOrder j) (dyadicPrimeCount j))).re) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_joint_exact_source rho hrho hexposed hU)
  simp only [hsimple,Nat.cast_one,one_pow,one_mul,Complex.add_re,
    Complex.neg_re,Complex.one_re,Complex.ofReal_re] at hs
  have hc : -(79/1000 : ℝ) ≤ (-1+retainedCost (3/2-rho.1.re))+0 :=
    ge_of_tendsto_of_frequently (hs.add he)
      (hfloor.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcost := retainedCost_lt_restricted hu hU
  linarith

/-- The same literal JOINT sum excludes a multiple exposed zero if it has
an independent cofinal ceiling. The ceiling is an OPEN arithmetic premise. -/
theorem false_of_joint_cofinal_ceiling_of_multiple (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
            (dyadicMomentOrder j) (dyadicPrimeCount j))).re ≤ 3/2+err j) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_joint_exact_source rho hrho hexposed hU)
  have hreal : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*(retainedCost (3/2-rho.1.re) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ)+
        (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re) := by
    norm_cast
  rw [hreal] at hs
  have hc : -(analyticZetaZeroMultiplicity rho : ℝ)+
      (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re)-0 ≤ 3/2 :=
    le_of_tendsto_of_frequently (hs.sub he)
      (hceiling.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcost := multiple_source_gt_three_halves hu hU hm
  linarith

/-- A two-sided cofinal band excludes EVERY analytic multiplicity, using
the existing carrier and source. The two cofinal subsequences may differ.
Neither arithmetic premise is proved by this conditional criterion. -/
theorem false_of_joint_cofinal_bounds (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (lowerError upperError : ℕ → ℝ)
    (hl : Tendsto lowerError atTop (𝓝 0)) (hu : Tendsto upperError atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -(79/1000 : ℝ)-lowerError j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
            (dyadicMomentOrder j) (dyadicPrimeCount j))).re)
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        (lowerThresholdPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)-
          shortOverflowPacket (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)+
          ZetaRieszLeastBoundary.rest (3/2-rho.1.re) rho.1.im
            (dyadicMomentOrder j) (dyadicPrimeCount j))).re ≤ 3/2+upperError j) : False := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · exact false_of_joint_cofinal_floor rho hrho hexposed hU hm lowerError hl hfloor
  · have hpos := analyticZetaZeroMultiplicity_positive rho
    exact false_of_joint_cofinal_ceiling_of_multiple rho hrho hexposed hU
      (by omega) upperError hu hceiling

end
end RiemannGaussian.ZetaRieszJointFloor
