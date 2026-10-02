/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNearLabelPayment

/-!
# Exact post-hinge profile price of the joined signed energy

The actual unit-log-corrected profile is charged only over its literal
post-hinge logarithmic interval. Its energy is at most (log X-L)_+,
without an endpoint allowance. On the current core this is eventually
at most 129N/200. This sharpens the price multiplying the ENTIRE retained
signed cross energy, not a count-wise positive envelope.

The independent numerical bound for that signed energy is still open.
The explicit 3/(320(N+1)) budget below is a sufficient condition, not
an assumed or proved arithmetic estimate for the carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszPostHingeEnergy
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszCenteredPrimeEnergy ZetaRieszDiagonalPayment
open ZetaRieszRejoinedPhaseFloor ZetaRieszWideOwnerAudit
open ZetaRieszNearLabelPayment
open ZetaRieszJointPrimeEnergy ZetaRieszJointAllocation
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint
open ZetaRieszJoinedPopulationFloor ZetaRieszSevenCountTail
open ZetaRieszRadialCompensation ZetaRieszLowCountRefund
open ZetaRieszRejoinedPopulationFloor

private theorem hinge_add_log (L x : ℝ) : max 0 (L-x)+x=max L x := by
  by_cases h : x ≤ L
  · rw [max_eq_right (sub_nonneg.mpr h),max_eq_left h]
    ring
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),max_eq_right (le_of_not_ge h)]
    ring

/-- The original retained profile is nondecreasing through its exact
zero endpoint. No sign of the arithmetic prefix is assumed. -/
theorem corrected_step_nonpos {X k : ℕ} (hk : k ∈ Finset.Icc 1 X) (L : ℝ) :
    correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1) ≤ 0 := by
  obtain ⟨hk0,hkX⟩ := Finset.mem_Icc.mp hk
  by_cases he : k=X
  · subst k
    simp [correctedProfile,centeredProfile]
  · have hk' : k+1 ≤ X := by omega
    have hl : log k ≤ log (k+1 : ℕ) := log_le_log
      (by exact_mod_cast hk0 : (0 : ℝ) < k) (by exact_mod_cast Nat.le_succ k)
    have hd : correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1)=
        max L (log k)-max L (log (k+1 : ℕ)) := by
      simp only [correctedProfile,centeredProfile,if_pos hkX,if_pos hk',
        zero_mul,add_zero,one_mul]
      linarith only [hinge_add_log L (log k),hinge_add_log L (log (k+1 : ℕ))]
    rw [hd]
    exact sub_nonpos.mpr (max_le_max_left L hl)

/-- A squared cutoff step costs no more than its ACTUAL post-hinge
increment. Telescoping retains the partial first step and final zero. -/
theorem corrected_step_energy_le {X k : ℕ} (hk : k ∈ Finset.Icc 1 X) (L : ℝ) :
    (k : ℝ)*(correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1))^2 ≤
      correctedProfile X L 1 0 (k+1)-correctedProfile X L 1 0 k := by
  let d := correctedProfile X L 1 0 k-correctedProfile X L 1 0 (k+1)
  have hd : d ≤ 0 := corrected_step_nonpos hk L
  have hstep : -d ≤ (k : ℝ)⁻¹ := by
    have h : |d| ≤ (k : ℝ)⁻¹ := corrected_profile_step_le hk L
    rwa [abs_of_nonpos hd] at h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hb := mul_le_mul_of_nonneg_left hstep hk0.le
  rw [mul_inv_cancel₀ hk0.ne'] at hb
  have hm := mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr hd)
  dsimp [d] at hm ⊢
  nlinarith only [hm]

/-- The exact post-hinge logarithmic width replaces the old 1+log X
profile allowance. This applies to the complete profile, hence every
original adverse subset, independently of phase and bin geometry. -/
theorem profileEnergy_post_hinge {X : ℕ} (hX : 0 < X) {L : ℝ} (hL : 0 ≤ L) :
    profileEnergy X (correctedProfile X L 1 0) ≤ max 0 (log X-L) := by
  let f := correctedProfile X L 1 0
  rw [profileEnergy_eq]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 X,(f (k+1)-f k) :=
      Finset.sum_le_sum (fun _ hk => corrected_step_energy_le hk L)
    _ = f (X+1)-f 1 := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      exact Finset.sum_Ico_sub f (by omega : 1 ≤ X+1)
    _ = max 0 (log X-L) := by
      have hX1 : 1 ≤ X := by omega
      simp only [f,correctedProfile,centeredProfile,
        if_neg (by omega : ¬X+1 ≤ X),if_pos hX1,Nat.cast_one,log_one,
        zero_mul,one_mul,add_zero,sub_zero,max_eq_right hL]
      by_cases h : L ≤ log X
      · rw [max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h)]
        ring
      · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h)),
          max_eq_left (sub_nonpos.mpr (le_of_not_ge h))]
        ring

/-- Favorable cutoffs remain uncharged. Their removal does not enlarge
the profile price used by the ORIGINAL whole funded adverse selection. -/
theorem adverseProfileEnergy_post_hinge {X : ℕ} (hX : 0 < X) (S : Finset ℕ)
    (w : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    adverseProfileEnergy X S w (correctedProfile X L 1 0) ≤ max 0 (log X-L) := by
  have hsub : negativeCutoffs X S w (correctedProfile X L 1 0) ⊆
      activeCutoffs X (correctedProfile X L 1 0) := Finset.filter_subset _ _
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans
      (profileEnergy_post_hinge hX hL)

open ZetaRieszParityPacket

/-- The cutoff endpoint is the actual supremum of original core labels,
including the empty-set case. No enlarged literalWindow is substituted. -/
theorem core_sup_log_le (u : ℝ) (N K : ℕ) (S : Finset ℕ)
    (hS : S ⊆ coreBand u N K) :
    log (max 1 (S.sup id) : ℕ) ≤ (203/100 : ℝ)*N := by
  rcases S.eq_empty_or_nonempty with hs|hs
  · simp only [hs,Finset.sup_empty,bot_eq_zero,max_eq_left (Nat.zero_le 1),Nat.cast_one,log_one]
    positivity
  · obtain ⟨n,hn,he⟩ := Finset.exists_mem_eq_sup S hs id
    have hw := (Finset.mem_filter.mp (hS hn)).2
    have hn0 : 1 ≤ n := by
      by_contra h
      have hz : n=0 := by omega
      simp only [hz,Nat.cast_zero,log_zero] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [he,id_eq,max_eq_right hn0]
    exact hw.2

/-- The floor and added two retain this exact quantitative lower bound
for the actual moving length; no asymptotic substitute is used. -/
theorem length_lower_bound {u : ℝ} (hu : 0 < u) (N : ℕ) :
    -2*(N : ℝ)*log u-2*log ((N : ℝ)+1) ≤ SquarefreeVaughanLogSource.length u N := by
  let x : ℝ := u⁻¹^N/((N : ℝ)+1)
  have hx : 0 < x := by dsimp [x]; positivity
  have hf : x ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ)+2 := by
    have h := Nat.lt_floor_add_one x
    dsimp [x,ZetaVaughanCutoffBudget.linearDampedCutoff,ZetaVaughanCutoffBudget.dampedCutoff] at h ⊢
    linarith only [h]
  have hl := log_le_log hx hf
  have he : log x=-(N : ℝ)*log u-log ((N : ℝ)+1) := by
    dsimp [x]
    rw [log_div (by positivity : u⁻¹^N ≠ 0) (by positivity : (N : ℝ)+1 ≠ 0),log_pow,log_inv]
    ring
  rw [he] at hl
  unfold SquarefreeVaughanLogSource.length
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hl]

private theorem log_successor_le {N : ℕ} (hN : 65536 ≤ N) :
    log ((N : ℝ)+1) ≤ (N : ℝ)/2000 := by
  have hb : log (65537 : ℝ) ≤ 12 := by
    apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 65537)).mpr
    have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12) 13
    norm_num [Finset.sum_range_succ] at h
    linarith only [h]
  have hg := log_le_sub_one_of_pos (show 0 < ((N : ℝ)+1)/65537 by positivity)
  rw [log_div (by positivity : (N : ℝ)+1 ≠ 0) (by norm_num : (65537 : ℝ) ≠ 0)] at hg
  have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
  linarith only [hg,hb,hn]

/-- The restricted radius gives a rational bound on its logarithm. -/
theorem radius_log_le {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) :
    log u ≤ -(693/1000 : ℝ) := by
  have hr : log radiusCeiling ≤ -(693/1000 : ℝ) := by
    have h := log_le_sub_one_of_pos (by norm_num [radiusCeiling] : (0 : ℝ) < 2*radiusCeiling)
    rw [log_mul (by norm_num) (by norm_num [radiusCeiling])] at h
    dsimp [radiusCeiling] at h ⊢
    linarith [log_two_gt_d9]
  exact (log_le_log hu hU).trans hr

/-- An explicit order threshold certifies the literal moving length.
It is independent of height and of all label/count/bin masks. -/
theorem length_ge_rational {N : ℕ} (hN : 65536 ≤ N) {u : ℝ}
    (hu : 0 < u) (hU : u ≤ radiusCeiling) :
    (277/200 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N := by
  have h := length_lower_bound hu N
  have hl := radius_log_le hu hU
  have hg := log_successor_le hN
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The actual moving, floor-dependent Riesz length leaves at most
129N/200 logarithmic profile price for EVERY original core subset. -/
theorem core_profile_bound {N : ℕ} (hN : 65536 ≤ N) {u : ℝ}
    (hu : 0 < u) (hU : u ≤ radiusCeiling) (K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : S ⊆ coreBand u N K) :
    adverseProfileEnergy (max 1 (S.sup id)) (S.filter Squarefree) w
      (correctedProfile (max 1 (S.sup id)) (SquarefreeVaughanLogSource.length u N) 1 0) ≤
        (129/200 : ℝ)*N := by
  have hp := adverseProfileEnergy_post_hinge
    (show 0 < max 1 (S.sup id) by omega) (S.filter Squarefree) w
    (SquarefreeVaughanLogSource.length_pos u N).le
  apply hp.trans
  apply max_le
  · positivity
  · have hx := core_sup_log_le u N K S hS
    have hL := length_ge_rational hN hu hU
    linarith only [hL,hx]

/-- The explicit estimate is available cofinally on the actual schedule;
no bound on the retained signed energy is assumed here. -/
theorem eventually_core_profile_bound {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (S : Finset ℕ) (w : ℕ → ℝ),
      S ⊆ coreBand u N K →
      adverseProfileEnergy (max 1 (S.sup id)) (S.filter Squarefree) w
        (correctedProfile (max 1 (S.sup id)) (SquarefreeVaughanLogSource.length u N) 1 0) ≤
          (129/200 : ℝ)*N := by
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN K S w hS
  exact core_profile_bound hN hu hU K S w hS

/-- This is ONLY the sufficient numerical energy condition. The
independent bound on E has not been proved for the literal carrier. -/
theorem cost_le_of_numeric_energy {N : ℕ} {E P : ℝ} (hP0 : 0 ≤ P)
    (hP : P ≤ (129/200 : ℝ)*N) (hE : E ≤ 3/(320*((N : ℝ)+1))) :
    sqrt (max E 0*P) ≤ (39/500 : ℝ) := by
  have hmax : max E 0 ≤ 3/(320*((N : ℝ)+1)) := max_le hE (by positivity)
  have hp := mul_le_mul hmax hP hP0 (by positivity : 0 ≤ 3/(320*((N : ℝ)+1)))
  have hcap : 3/(320*((N : ℝ)+1))*((129/200 : ℝ)*N) ≤ (39/500 : ℝ)^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 320*((N : ℝ)+1))).mpr
    have hn := Nat.cast_nonneg (α := ℝ) N
    nlinarith only [hn]
  exact sqrt_le_iff.mpr ⟨by norm_num,hp.trans hcap⟩

/-- A direct one-sided floor once the OPEN energy condition is supplied.
The error is the original paid error and is not replaced by a new debit. -/
theorem real_floor_of_numeric_energy {N : ℕ} {E P value err : ℝ}
    (hP0 : 0 ≤ P) (hP : P ≤ (129/200 : ℝ)*N)
    (hE : E ≤ 3/(320*((N : ℝ)+1)))
    (hfloor : -sqrt (max E 0*P)-err ≤ value) :
    -(39/500 : ℝ)-err ≤ value := by
  have h := cost_le_of_numeric_energy hP0 hP hE
  linarith only [h,hfloor]

/-- The smaller post-hinge price applies to the SAME whole funded
carrier and the SAME signed cross energy after all geometric payments.
All original count/bin masks, supply weights and overlaps are retained.
The numerical bound on the remaining energy is still open. -/
theorem eventually_joined_calibrated_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ : ℝ,0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧ 0 < κ ∧
      ∀ ε : ℝ,0 < ε → ∃ err : ℕ → ℝ,
        (∀ j,0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
        ∀ᶠ j : ℕ in atTop,∃ v : ℕ → ℝ,
          (∀ M ∈ radialIndices (dyadicMomentOrder j),0 ≤ v M ∧ v M ≤ 1/2) ∧
          let N := dyadicMomentOrder j
          let K := dyadicPrimeCount j
          let A := intermediatePrimes u N
          let L := SquarefreeVaughanLogSource.length u N
          let S₀ := coreBand u N K
          let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Paid := (S₀.filter (fun n : ℕ =>
            3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪
              bin56Band u N K
          let H := (S₀\(Paid ∪ wholeTail S₀ N 0))\ZetaRieszSharpOwnerPayment.sector u N K
          let Ts := radialTail S₀ N 0
          let Ys := radialSupply N h v
          let S := ((H ∪ Paid) ∪ Ts) ∪ Ys
          let X := max 1 (S.sup id)
          let f := correctedProfile X L 1 0
          let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
          let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
          let debit := tailCost c N+ε+growingDebit κ N
          let w := fun n => u^(N+1)*rejoinedWeights H Paid Ts Ys a b debit n*primeWeight A L y N n 1;
          0 < (∑ n ∈ Ys,atom n).re ∧
            -sqrt (((129/200 : ℝ)*N)*
              max (separatedEnergy X N (S.filter Squarefree) w f) 0)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re := by
  obtain ⟨h,c,κ,hh,hhu,hc,hκ,hbase⟩ := eventually_joined_separated_floor hu hU hy
  refine ⟨h,c,κ,hh,hhu,hc,hκ,?_⟩
  intro ε hε
  obtain ⟨err,he0,he,hfloor⟩ := hbase ε hε
  refine ⟨err,he0,he,?_⟩
  have hsupply := eventually_radial_supply_in_core hu hU hh hhu
  have hprofile := eventually_core_profile_bound (by linarith : 0 < u) hU
  filter_upwards [hfloor,hsupply,tendsto_dyadicMomentOrder.eventually hprofile]
    with j hj hY hcap
  obtain ⟨v,hv,hpos,hbound⟩ := hj
  refine ⟨v,hv,hpos,?_⟩
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S₀ := coreBand u N K
  let Paid := (S₀.filter (fun n : ℕ =>
    3 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∪ dense56Band u N K) ∪ bin56Band u N K
  let H := (S₀\(Paid ∪ wholeTail S₀ N 0))\ZetaRieszSharpOwnerPayment.sector u N K
  let Ts := radialTail S₀ N 0
  let Ys := radialSupply N h v
  let S := ((H ∪ Paid) ∪ Ts) ∪ Ys
  let X := max 1 (S.sup id)
  let f := correctedProfile X L 1 0
  let atom := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let a : ℝ := if 0 ≤ (∑ n ∈ Paid,atom n).re then 1 else 0
  let b : ℝ := if 0 ≤ (∑ n ∈ Ts,atom n).re then 1 else 0
  let w := fun n => u^(N+1)*rejoinedWeights H Paid Ts Ys a b
    (tailCost c N+ε+growingDebit κ N) n*primeWeight A L y N n 1
  have hS : S ⊆ S₀ := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn|hn
    · rcases Finset.mem_union.mp hn with hn|hn
      · rcases Finset.mem_union.mp hn with hn|hn
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hn).1).1
        · rcases Finset.mem_union.mp hn with hn|hn
          · rcases Finset.mem_union.mp hn with hn|hn
            · exact (Finset.mem_filter.mp hn).1
            · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
          · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
      · obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
        exact (Finset.mem_filter.mp hn).1
    · obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hY M hM (v M) (hv M hM).1 (hv M hM).2 hn
  have hp := hcap K S w hS
  have hm := mul_le_mul_of_nonneg_left hp
    (le_max_right (separatedEnergy X N (S.filter Squarefree) w f) 0)
  have hs := sqrt_le_sqrt hm
  change -sqrt (max (separatedEnergy X N (S.filter Squarefree) w f) 0*
    adverseProfileEnergy X (S.filter Squarefree) w f)-err j ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re at hbound
  change -sqrt (((129/200 : ℝ)*N)*max (separatedEnergy X N (S.filter Squarefree) w f) 0)-err j ≤
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N K).re
  conv_rhs at hs => rw [mul_comm]
  exact (sub_le_sub_right (neg_le_neg hs) (err j)).trans hbound

end RiemannGaussian.ZetaRieszPostHingeEnergy
