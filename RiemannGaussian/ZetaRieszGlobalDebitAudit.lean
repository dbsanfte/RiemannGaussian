/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRejoinedSupplyFloor
import RiemannGaussian.ZetaRieszAdaptiveRateAudit

set_option autoImplicit false

/-!
# A source-scale audit of the global signed-floor debit

This audits the actual shared period units and the actual radial-supply
charge in the current whole-carrier floor. It does not bound the carrier
by another positive majorant. Every inverse-polynomial debit of these
units diverges at source scale when u > 1/2. In particular, the currently
proved N^-4 relative tail charge cannot be paid separately after the
positive supply has been rejoined. The signed tail and the other retained
terms must supply a genuinely joint compensation.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszGlobalDebitAudit
open ZetaRieszFiveSignCoverFloor (completeGrid slabGrid biUnion_slabGrid_eq
  exists_completeGrid_period)
open ZetaRieszMultiPeriodSix (center)
open ZetaRieszHighSignCoverFloor (periodUnits)
open ZetaRieszPrimeCountFrequency
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszLowCountRefund (tailCost)

private theorem radial_unit_nonneg (N : ℕ) {b y : ℝ} (hb : 0 ≤ b) (hy : 0 < y)
    (i : ℕ) :
    0 ≤ Real.exp (-center b y i/2)*(center b y i)^N/N.factorial := by
  have ht : 0 ≤ center b y i := by
    unfold center
    rw [abs_of_pos hy]
    positivity
  positivity

/-- One actual complete-grid center lies within one unit to the right
of the factorial saddle. The lower bound is for the original shared
period budget, not a substitute radial measure. -/
theorem periodUnits_saddle_lower {N : ℕ} (hN : 4000 ≤ N) {y : ℝ} (hy : 54 ≤ y) :
    Real.exp (-1)*(2 : ℝ)^N/(3*((N : ℝ)+1)) ≤ periodUnits N y := by
  have hy0 : 0 < y := by linarith
  have hπ0 : 0 < Real.pi/y := div_pos Real.pi_pos hy0
  have hπu : Real.pi/y ≤ 1/16 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨i,hi,hTi⟩ := exists_completeGrid_period hN hy
    (b := Real.pi/y) (T := 2*(N : ℝ)+Real.pi/y)
    ⟨le_rfl,by
      calc
        Real.pi/y ≤ Real.pi/y+Real.pi/y := le_add_of_nonneg_right hπ0.le
        _ = 2*Real.pi/y := by ring⟩ (by linarith) (by linarith)
  have hcenter₁ : 2*(N : ℝ) ≤ center (Real.pi/y) y i := by linarith only [hTi.2]
  have hcenter₂ : center (Real.pi/y) y i ≤ 2*(N : ℝ)+1 := by
    linarith only [hTi.1,hπu]
  have hrad := ZetaRieszSaddleCredit.saddle_radial_lower
    (show 1 ≤ N by omega) hcenter₁ hcenter₂
  have hroot : Real.sqrt (N : ℝ) ≤ (N : ℝ)+1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith [Nat.cast_nonneg (α := ℝ) N]⟩
  have hlo : Real.exp (-1)*(2 : ℝ)^N/(3*((N : ℝ)+1)) ≤
      Real.exp (-1)*(2 : ℝ)^N/(3*Real.sqrt N) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hroot (by norm_num))
  have hsum := Finset.single_le_sum
    (fun j (_ : j ∈ completeGrid N (Real.pi/y) y) =>
      radial_unit_nonneg N hπ0.le hy0 j) hi
  have hother : 0 ≤ ∑ j ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y j/2)*
        (center (Real.pi/y+Real.pi/y) y j)^N/N.factorial :=
    Finset.sum_nonneg (fun j _ => radial_unit_nonneg N (by positivity) hy0 j)
  unfold periodUnits
  exact (hlo.trans hrad).trans (hsum.trans (le_add_of_nonneg_right hother))

/-- Exact source-scale lower bound. No zero or prime-distribution
hypothesis enters this positive budget audit. -/
theorem source_periodUnits_lower {N : ℕ} (hN : 4000 ≤ N) {y u : ℝ}
    (hy : 54 ≤ y) (hu : 0 ≤ u) :
    (u*Real.exp (-1)/3)*((2*u)^N/((N : ℝ)+1)) ≤
      u^(N+1)*periodUnits N y := by
  have hh := mul_le_mul_of_nonneg_left (periodUnits_saddle_lower hN hy)
    (pow_nonneg hu (N+1))
  calc
    _ = u^(N+1)*(Real.exp (-1)*(2 : ℝ)^N/(3*((N : ℝ)+1))) := by
      rw [mul_pow,pow_succ]
      field_simp
    _ ≤ _ := hh

/-- Even an arbitrarily high fixed inverse-polynomial period debit
grows without bound at source scale. Decreasing a local constant or
fixed polynomial charge cannot make this global debit o(1). -/
theorem polynomial_periodDebit_tendsto {u y c : ℝ} (hu : 1/2 < u)
    (hy : 54 ≤ y) (hc : 0 < c) (B : ℕ) :
    Tendsto (fun N : ℕ => c*u^(N+1)*periodUnits N y/((N : ℝ)+1)^B)
      atTop atTop := by
  have ht := (ZetaRieszShiftedCenter.polynomial_source_ratio_tendsto hu (B+1)).const_mul_atTop
    (show 0 < c*(u*Real.exp (-1)/3) by positivity)
  apply Filter.tendsto_atTop_mono' _ ?_ ht
  filter_upwards [eventually_ge_atTop (4000 : ℕ)] with N hN
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (source_periodUnits_lower (u := u) hN hy
      (by linarith)) hc.le)
    (show 0 ≤ ((N : ℝ)+1)^B by positivity)
  calc
    _ = (c*((u*Real.exp (-1)/3)*((2*u)^N/((N : ℝ)+1))))/((N : ℝ)+1)^B := by
      rw [pow_succ]
      field_simp
    _ ≤ _ := hh.trans_eq (by ring)

set_option maxHeartbeats 800000 in
/-- The actual global N^-4 tail charge has an explicit exponential
source-scale lower bound for EVERY supply satisfying the proved slab
capacity. The unknown capacity constant cancels exactly. -/
theorem supply_tailDebit_lower {N : ℕ} (hN : 4000 ≤ N)
    {u y c h : ℝ} (hu : 0 ≤ u) (hy : 54 ≤ y) (hc : 0 < c)
    (hhu : h ≤ 1/20) (w : ℕ → ℝ) (f : ℕ → ℂ)
    (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hscale : ∀ M ∈ radialIndices N,
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h (w M), f n).re) :
    (128*u*Real.exp 1/(3*((⌊2*y⌋₊ : ℝ)+1)))*
        ((2*u)^N/((N : ℝ)+1)^5) ≤
      u^(N+1)*tailCost c N*(∑ n ∈ radialSupply N h w, f n).re := by
  let κ := c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2)
  have hκ0 : 0 < κ := by dsimp [κ]; positivity
  have ht0 : 0 ≤ tailCost c N := ZetaRieszLowCountRefund.tailCost_nonneg hc.le N
  have hp := ZetaRieszRoughFiveJoinedFloor.period_grids_cost_paid
    (show 1 ≤ N by omega) hc hy hhu (κ := κ) rfl w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hp
  change κ*periodUnits N y ≤ (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re at hp
  have hY : 128*κ*periodUnits N y ≤ (∑ n ∈ radialSupply N h w, f n).re := by
    linarith only [hp]
  have hp' := mul_le_mul_of_nonneg_left hY
    (show 0 ≤ u^(N+1)*tailCost c N by positivity)
  have hs := mul_le_mul_of_nonneg_left (source_periodUnits_lower hN hy hu)
    (show 0 ≤ 128*κ*tailCost c N by positivity)
  have he : Real.exp 4/Real.exp 2*Real.exp (-1) = Real.exp 1 := by
    rw [← Real.exp_sub,← Real.exp_add]
    norm_num
  have hge : (128*u*Real.exp 1/(3*((⌊2*y⌋₊ : ℝ)+1)))*
      ((2*u)^N/((N : ℝ)+1)^5) =
      (128*κ*tailCost c N)*((u*Real.exp (-1)/3)*((2*u)^N/((N : ℝ)+1))) := by
    calc
      _ = (128*u/(3*((⌊2*y⌋₊ : ℝ)+1)))*
          (Real.exp 4/Real.exp 2*Real.exp (-1))*((2*u)^N/((N : ℝ)+1)^5) := by
        rw [he]
        ring
      _ = _ := by
        dsimp [κ,tailCost,ZetaRieszLogCountBudget.relativeCost]
        field_simp
  rw [hge]
  exact hs.trans (by convert hp' using 1; ring)

/-- The same lower bound applies to the COMBINED debit in the rejoined
floor, even when its additional period allowance is chosen to shrink.
The actual supply remains the same signed arithmetic population. -/
theorem combined_supplyDebit_lower {N : ℕ} (hN : 4000 ≤ N)
    {u y c h ε : ℝ} (hu : 0 ≤ u) (hy : 54 ≤ y) (hc : 0 < c)
    (hhu : h ≤ 1/20) (hε : 0 ≤ ε) (w : ℕ → ℝ) (f : ℕ → ℂ)
    (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hscale : ∀ M ∈ radialIndices N,
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h (w M), f n).re) :
    (128*u*Real.exp 1/(3*((⌊2*y⌋₊ : ℝ)+1)))*
        ((2*u)^N/((N : ℝ)+1)^5) ≤
      u^(N+1)*(tailCost c N+ε)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hb := supply_tailDebit_lower hN hu hy hc hhu w f hw hscale
  have hY : 0 ≤ (∑ n ∈ radialSupply N h w, f n).re := by
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hw),Complex.re_sum]
    exact Finset.sum_nonneg (fun M hM =>
      (show 0 ≤ c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M
        by positivity [radialEnvelope_nonneg N M]).trans (hscale M hM))
  have he := mul_nonneg (pow_nonneg hu (N+1)) (mul_nonneg hε hY)
  nlinarith only [hb,he]

/-- The global tail debit exceeds every fixed source-scale budget,
uniformly over all admissible supply choices. This audits the debit;
it does NOT claim the signed tail or the joined carrier diverges. -/
theorem eventually_supply_tailDebit_gt {u y c h : ℝ} (hu : 1/2 < u)
    (hy : 54 ≤ y) (hc : 0 < c) (hhu : h ≤ 1/20) (b : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (w : ℕ → ℝ) (f : ℕ → ℂ),
      (∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) →
      (∀ M ∈ radialIndices N,
        c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
          (∑ n ∈ supply M h (w M), f n).re) →
      b < u^(N+1)*tailCost c N*(∑ n ∈ radialSupply N h w, f n).re := by
  have ht := (ZetaRieszShiftedCenter.polynomial_source_ratio_tendsto hu 5).const_mul_atTop
    (show 0 < 128*u*Real.exp 1/(3*((⌊2*y⌋₊ : ℝ)+1)) by positivity)
  filter_upwards [ht.eventually_gt_atTop b,eventually_ge_atTop (4000 : ℕ)]
    with N hlarge hN w f hw hscale
  exact hlarge.trans_le (supply_tailDebit_lower hN (by linarith) hy hc hhu w f hw hscale)

/-- The obstruction is present in the actual arithmetic supplies of
the current joint floor: their slab-capacity hypotheses are discharged
by the proved supply construction, not assumed as a missing estimate. -/
theorem actual_tailDebit_unbounded {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧
      ∀ b : ℝ, ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n;
        b < u^(N+1)*tailCost c N*(∑ n ∈ radialSupply N h w, f n).re := by
  obtain ⟨h,c,κ,r,C,hh,hhu,hc,_,_,_,_,_,hbase⟩ :=
    ZetaRieszSharpSupplyFloor.eventually_core_floor_with_sharp_tail hu hU hy
  refine ⟨h,c,hh,hhu,hc,?_⟩
  intro b
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually
    (eventually_supply_tailDebit_gt hu hy hc hhu b)] with j hj hdebit
  obtain ⟨w,hw,_,hscale,_⟩ := hj
  refine ⟨w,hw,?_⟩
  exact hdebit w _ hw hscale

/-- Neither a moving epsilon nor a different admissible supply choice
removes this debit. The displayed charge in the current joint floor
exceeds every fixed budget along its actual cofinal orders. -/
theorem actual_combinedDebit_unbounded {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c : ℝ, 0 < h ∧ h ≤ 1/20 ∧ 0 < c ∧
      ∀ b : ℝ, ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let f := fun n => ZetaRieszJointAllocation.residualCoefficient A L N n*
          zetaPrimeLogKernel N (3/2+Complex.I*y) n;
        ∀ ε : ℝ, 0 ≤ ε → b <
          u^(N+1)*(tailCost c N+ε)*(∑ n ∈ radialSupply N h w, f n).re := by
  obtain ⟨h,c,κ,r,C,hh,hhu,hc,_,_,_,_,_,hbase⟩ :=
    ZetaRieszSharpSupplyFloor.eventually_core_floor_with_sharp_tail hu hU hy
  refine ⟨h,c,hh,hhu,hc,?_⟩
  intro b
  have ht := (ZetaRieszShiftedCenter.polynomial_source_ratio_tendsto hu 5).const_mul_atTop
    (show 0 < 128*u*Real.exp 1/(3*((⌊2*y⌋₊ : ℝ)+1)) by positivity)
  filter_upwards [hbase,tendsto_dyadicMomentOrder.eventually (ht.eventually_gt_atTop b),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hlarge hN
  obtain ⟨w,hw,_,hscale,_⟩ := hj
  refine ⟨w,hw,?_⟩
  dsimp only
  intro ε hε
  exact hlarge.trans_le (combined_supplyDebit_lower hN (by linarith) hy hc hhu hε w _ hw hscale)

end RiemannGaussian.ZetaRieszGlobalDebitAudit
