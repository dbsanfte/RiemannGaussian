/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourSmallFloor

set_option autoImplicit false

/-!
# Refunding the old absolute low-count head charges in the joint floor

Complete signed prime periods are uniform in the old small-prime thresholds.
Set those thresholds to zero and retain every low-count head in the signed
sum. Only the old logarithmic count tail remains charged to the SAME supply.
No arithmetic label is deleted by this refund.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLowCountRefund
open ZetaRieszTransitionFiveFloor ZetaRieszStaggeredFloor
open ZetaRieszRoughFivePeriodFloor (spent radialSupply_count)
open ZetaRieszRoughFiveJoinedFloor
open ZetaRieszPrimeCountFrequency ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszOneSidedArithmetic (weight weight_nonneg)
open ZetaRieszMultiPeriodSix
open ZetaRieszRadialCompensation ZetaRieszBandCompensation
open ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszFiveNegativeHead ZetaRieszSevenCountTail
open ZetaRieszFixedCountPeriod (response)
open ZetaRieszAllowancePrimeBoxes ZetaRieszMacroPrimeWindows
open ZetaRieszFiveSignCoverFloor (completeGrid slabGrid biUnion_slabGrid_eq
  exists_completeGrid_period exists_outer_subset_bound)

open ZetaRieszThreeSignCoverFloor (tripleRestSpent tripleRestSpent_eq
  nontriple_rest_filter_eq)
open ZetaRieszHighSignCoverFloor (high_rest_filter_eq exists_unpaid_band_floor)
open ZetaRieszFourSmallFloor (PaidFour exists_unpaid_four_away_supply_floor)

theorem smallTriples_zero (S : Finset ℕ) (M : ℕ) : smallTriples S M 0 = ∅ := by
  simp [smallTriples]

theorem smallFours_zero (S : Finset ℕ) (M : ℕ) : smallFours S M 0 = ∅ := by
  simp [smallFours]

theorem smallPositiveFives_zero (S : Finset ℕ) (M : ℕ) (L : ℝ) :
    smallPositiveFives S M 0 L = ∅ := by
  simp [smallPositiveFives]

theorem smallHeads_zero (S : Finset ℕ) (M : ℕ) (L : ℝ) :
    smallHeads S M 0 0 L = ∅ := by
  simp [smallHeads,headCondition]

theorem radialHeads_zero (S : Finset ℕ) (N : ℕ) (L : ℝ) :
    radialHeads S N 0 0 L = ∅ := by
  ext n
  simp [radialHeads,smallHeads_zero]

/-- Zero thresholds return all low-count heads to the exact original sum.
The remaining spent labels are precisely the original supply and tail. -/
theorem tripleRestSpent_zero (S : Finset ℕ) {N R : ℕ}
    (η : ℝ) {h L : ℝ} (hN : 1000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2) :
    tripleRestSpent S N 0 0 0 R η h L w =
      radialSupply N h w ∪ radialTail S N R ∪ wholeTail S N R := by
  rw [tripleRestSpent_eq S η hN hh hhu w hw]
  ext n
  simp [smallTriples_zero,smallFours_zero,smallPositiveFives_zero,radialHeads_zero]

/-- Only the original tail is norm-paid. The other low-count labels stay
literal, refunding their former charges before applying period cancellation. -/
theorem tail_only_floor {S T Y : Finset ℕ} (f : ℕ → ℂ)
    (hsub : Y ∪ T ⊆ S) (hd : Disjoint Y T)
    (htail : ‖∑ n ∈ T, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ S\(Y ∪ T), f n).re+max (∑ n ∈ T, f n).re 0+
      (63/64 : ℝ)*(∑ n ∈ Y, f n).re ≤ (∑ n ∈ S, f n).re := by
  have hs := congrArg Complex.re (Finset.sum_sdiff hsub (f := f))
  rw [Finset.sum_union hd] at hs
  simp only [Complex.add_re] at hs
  have hmax : max (∑ n ∈ T, f n).re 0 ≤
      (∑ n ∈ T, f n).re+(1/64 : ℝ)*(∑ n ∈ Y, f n).re := by
    have hb := Complex.re_le_norm (-(∑ n ∈ T, f n))
    simp only [Complex.neg_re,norm_neg] at hb
    exact max_le (by linarith [norm_nonneg (∑ n ∈ T, f n)]) (by linarith)
  linarith only [hs,hmax]

/-- Retain the actual tail charge instead of rounding it to 1/64. -/
theorem tail_floor {S T Y : Finset ℕ} (f : ℕ → ℂ) {b : ℝ}
    (hsub : Y ∪ T ⊆ S) (hd : Disjoint Y T)
    (htail : ‖∑ n ∈ T, f n‖ ≤ b*(∑ n ∈ Y, f n).re) :
    (∑ n ∈ S\(Y ∪ T), f n).re+max (∑ n ∈ T, f n).re 0+
      (1-b)*(∑ n ∈ Y, f n).re ≤ (∑ n ∈ S, f n).re := by
  have hs := congrArg Complex.re (Finset.sum_sdiff hsub (f := f))
  rw [Finset.sum_union hd] at hs
  simp only [Complex.add_re] at hs
  have hmax : max (∑ n ∈ T, f n).re 0 ≤
      (∑ n ∈ T, f n).re+b*(∑ n ∈ Y, f n).re := by
    have hb := Complex.re_le_norm (-(∑ n ∈ T, f n))
    simp only [Complex.neg_re,norm_neg] at hb
    exact max_le (by linarith [norm_nonneg (∑ n ∈ T, f n)]) (by linarith)
  nlinarith only [hs,hmax]

/-- Exact proved relative count-tail cost for a supply lower constant c. -/
def tailCost (c : ℝ) (N : ℕ) : ℝ :=
  ZetaRieszLogCountBudget.relativeCost N/c

theorem tailCost_nonneg {c : ℝ} (hc : 0 ≤ c) (N : ℕ) : 0 ≤ tailCost c N := by
  unfold tailCost ZetaRieszLogCountBudget.relativeCost
  positivity

theorem tendsto_tailCost (c : ℝ) : Tendsto (tailCost c) atTop (𝓝 0) := by
  change Tendsto (fun N => ZetaRieszLogCountBudget.relativeCost N/c) atTop (𝓝 0)
  simpa only [zero_div] using ZetaRieszLogCountBudget.tendsto_relativeCost.div_const c

/-- The literal radial count tail costs O(N^-4) of the SAME chosen supply.
No phase or small-prime mask is removed. -/
theorem radial_tail_sharp_cost (S A : Finset ℕ) {N : ℕ} {h L y c : ℝ}
    (hN : 1 ≤ N) (hhu : h ≤ 1/20) (hL : 0 < L) (hc : 0 < c)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hscale : ∀ M ∈ radialIndices N,
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h (w M),
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) :
    ‖∑ n ∈ radialTail S N 0,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      tailCost c N*(∑ n ∈ radialSupply N h w,
        residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hpay : ∀ M ∈ radialIndices N,
      ‖∑ n ∈ slabTail S N 0 M, f n‖ ≤ tailCost c N*(∑ n ∈ supply M h (w M), f n).re := by
    intro M hM
    have hb := (Finset.mem_filter.mp hM).2
    have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hmr : (0 : ℝ) < M := by linarith only [hb.1,hnr]
    have hM0 : 0 < M := by exact_mod_cast hmr
    have hNM : N ≤ 2*M := by exact_mod_cast (show (N : ℝ) ≤ 2*M by linarith only [hb.1,hnr])
    have hMN : M ≤ 2*N := by
      have hm := Finset.mem_range.mp (Finset.mem_filter.mp hM).1
      omega
    have ht := ZetaRieszLogCountBudget.logarithmic_count_norm_upper
      (slabTail S N 0 M) A hM0 hNM hMN hL y (by
        intro n hn
        obtain ⟨_,hs,hlo,hhi,hcount⟩ := Finset.mem_filter.mp hn
        refine ⟨hs,hlo,hhi.le,?_⟩
        simpa [ZetaRieszSevenPrimeHead.tailCondition] using hcount)
    have hp := mul_le_mul_of_nonneg_left (hscale M hM) (tailCost_nonneg hc.le N)
    have he : tailCost c N*
        (c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M) =
        ZetaRieszLogCountBudget.relativeCost N*(M : ℝ)*Real.exp (2*(M : ℝ))/
          ((M : ℝ)+1)*radialEnvelope N M := by
      unfold tailCost
      field_simp
    rw [he] at hp
    exact ht.trans hp
  change ‖∑ n ∈ (radialIndices N).biUnion (slabTail S N 0), f n‖ ≤ _
  rw [Finset.sum_biUnion (fun _ _ _ _ hne => slabTail_disjoint S N 0 hne),
    radialSupply,Finset.sum_biUnion (supply_disjoint hhu hw)]
  calc
    _ ≤ ∑ M ∈ radialIndices N, ‖∑ n ∈ slabTail S N 0 M, f n‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ radialIndices N, tailCost c N*(∑ n ∈ supply M h (w M), f n).re :=
      Finset.sum_le_sum hpay
    _ = _ := by rw [← Finset.mul_sum,Complex.re_sum]

private theorem norm_radial_payment {N : ℕ} {E : ℕ → Finset ℕ} {f : ℕ → ℂ}
    {h : ℝ} {v : ℕ → ℝ} {b : ℝ}
    (hE : (radialIndices N : Set ℕ).PairwiseDisjoint E)
    (hh : h ≤ 1/20) (hv : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2)
    (hpay : ∀ M ∈ radialIndices N,
      ‖∑ n ∈ E M, f n‖ ≤ b*(∑ n ∈ supply M h (v M), f n).re) :
    ‖∑ n ∈ (radialIndices N).biUnion E, f n‖ ≤ b*(∑ n ∈ radialSupply N h v, f n).re := by
  rw [Finset.sum_biUnion hE,radialSupply,Finset.sum_biUnion (supply_disjoint hh hv)]
  calc
    _ ≤ ∑ M ∈ radialIndices N, ‖∑ n ∈ E M, f n‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ radialIndices N, b*(∑ n ∈ supply M h (v M), f n).re := Finset.sum_le_sum hpay
    _ = _ := by rw [← Finset.mul_sum,Complex.re_sum]

set_option maxHeartbeats 1200000 in
/-- The literal core retains every old low-count head. Only the original
logarithmic count tail is charged, leaving 63/64 of the SAME supply before
the complete-period debit. Every radial boundary is still paid. -/
theorem eventually_core_floor_with_heads_rejoined {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h c κ r C : ℝ, 0 < h ∧ h ≤ 1/20 ∧
      0 < c ∧ 0 < κ ∧ κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let R : ℕ := 0
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let B := wholeTail S N R
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (w M), f n).re) ∧
          u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B), f n).re+
            max (∑ n ∈ Ts, f n).re 0+(63/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r^N*C ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hpay⟩ :=
    ZetaRieszRoughFivePeriodFloor.eventually_joint_slabs_floor_with_period_budget hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := ZetaRieszSevenCountTail.exists_missed_tail_bound
  refine ⟨h,c,κ,r,C,hh,hhu,hc,hκ,hκeq,hr,hr1,hC,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let R : ℕ := 0
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hR : Real.log R ≤ θ*N := by simp only [R,Nat.cast_zero,Real.log_zero]; positivity
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTail S N R M, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hscale,hY,_,_,_,_,_,hT,_⟩ :=
        hpay M 0 0 0 R ∅ ∅ ∅ ∅ ∅ (slabTail S N R M) A L
          (hL M hM).1 (by have := Finset.mem_range.mp (Finset.mem_filter.mp hM).1; omega)
          (by simpa using mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
          (by simpa using mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N))
          (by simpa using mul_nonneg hζ.le (Nat.cast_nonneg (α := ℝ) N))
          hR (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
          (by simp) (by simp) (by simp)
          (by
            intro n hn
            obtain ⟨_,hs,hlo,hhi,hcount⟩ := Finset.mem_filter.mp hn
            exact ⟨hs,hlo,hhi.le,hcount⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hT,hscale⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose w hw using hex
  have hwb : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2 :=
    fun M hM => ⟨(hw M hM).1,(hw M hM).2.1⟩
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let B := wholeTail S N R
  have hY : 0 < (∑ n ∈ Ys, f n).re := by
    change 0 < (∑ n ∈ radialSupply N h w, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hwb),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hw M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hw N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hTpay := norm_radial_payment
    (fun _ _ _ _ hne => slabTail_disjoint S N R hne) hhu hwb
    (fun M hM => (hw M hM).2.2.2.1)
  have hTsub : Ts ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hTcount : ∀ n ∈ Ts, 7 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N)
      (Finset.mem_filter.mp hn).2.2.2.2
  have hYcount : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => radialSupply_count (by omega) hh hhu w hwb hn
  have hYsub : Ys ⊆ S := by
    intro n hn
    obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
    exact hsub M hM (w M) (hwb M hM).1 (hwb M hM).2 hn
  have hYT : Disjoint Ys Ts := Finset.disjoint_left.mpr
    (fun n hnY hnT => by have := hYcount n hnY; have := hTcount n hnT; omega)
  have hfloor := tail_only_floor f (Finset.union_subset hYsub hTsub) hYT hTpay
  have hcore := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  let D := B\Ts
  have hDsub : D ⊆ S\(Ys ∪ Ts) := by
    intro n hn
    obtain ⟨hnB,hnT⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnS,_,hc⟩ := Finset.mem_filter.mp hnB
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with hnY | hnT'
    · have ht := ZetaRieszSevenPrimeHead.tailCondition_count_ge (by omega : 1 ≤ N) hc
      have hyc := hYcount n hnY
      omega
    · exact hnT hnT'
  have hnorm := hmissed N R S A y u hN (by linarith) hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hreal
  have hsum := congrArg Complex.re (Finset.sum_sdiff hDsub (f := f))
  have hsets : (S\(Ys ∪ Ts))\D = S\(Ys ∪ Ts ∪ B) := by
    ext n
    simp only [D,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hsets,Complex.add_re] at hsum
  have hscaled := congrArg (fun x : ℝ => u^(N+1)*x) hsum
  refine ⟨w,hwb,hY,fun M hM => (hw M hM).2.2.2.2,?_⟩
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul]
  nlinarith only [hcore,hreal,hscaled]

private theorem paid_parts (E : Finset ℕ) (f : ℕ → ℂ) (N : ℕ) (L : ℝ) :
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 5), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 6), f n)+
    (∑ n ∈ E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧
      n.primeFactors.card ≤ 55), f n)+
    (∑ n ∈ (E.filter (fun n : ℕ => n.primeFactors.card = 4)).filter
      (fun n => PaidFour N L n), f n) =
    ∑ n ∈ E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
      n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
      (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
      (n.primeFactors.card = 4 ∧ PaidFour N L n)), f n := by
  rw [Finset.filter_filter]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h3 : n.primeFactors.card = 3
  · simp [h3]
  by_cases h5 : n.primeFactors.card = 5
  · simp [h5]
  by_cases h6 : n.primeFactors.card = 6
  · simp [h6]
  by_cases h4 : n.primeFactors.card = 4
  · simp [h4]
  simp only [h3,h5,h6,h4,if_false,false_or,false_and,or_false,zero_add,add_zero]

set_option maxHeartbeats 1600000 in
/-- Rejoin every old low-count head before using the signed period
estimates. The SAME original supply now retains 125/128, rather than
65/128. The former head max credits are consumed into the one joint
paid-band max credit. Balanced negative fours and growing counts remain;
this is not the numerical cofinal floor. -/
theorem eventually_joined_floor_with_refunded_heads {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ h : ℝ, ∃ err : ℕ → ℝ,
      0 < h ∧ h ≤ 1/20 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let η : ℝ := 0
        let Q : ℕ := 0
        let P : ℕ := 0
        let V : ℕ := 0
        let R : ℕ := 0
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let E := S\tripleRestSpent S N Q P V R η h L w
        let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n))
        let Eo := E\Epaid
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          u^(N+1)*(W+G+max (∑ n ∈ Ts, f n).re 0+
            max (∑ n ∈ Epaid, f n).re 0+(125/128 : ℝ)*(∑ n ∈ Ys, f n).re)-err j ≤
              ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨h,c,κ,r₀,C₀,hh,hhu,hc,hκ,hκeq,hr₀,hr₀1,hC₀,hbase⟩ :=
    eventually_core_floor_with_heads_rejoined hu hU hy
  let η : ℝ := 0
  have hηu : η ≤ 1/1000 := by norm_num [η]
  obtain ⟨r₁,C₁,hr₁,hr₁1,hC₁,hfive⟩  :=
    ZetaRieszFiveSignCoverFloor.exists_unpaid_five_floor hu hU hy (by positivity : 0 < κ/5)
  obtain ⟨r₂,C₂,hr₂,hr₂1,hC₂,hsix⟩ := ZetaRieszSixSignCoverFloor.exists_unpaid_six_floor hu hU hy (by positivity : 0 < κ/5)
  obtain ⟨r₃,C₃,hr₃,hr₃1,hC₃,hthree⟩ := ZetaRieszThreeSignCoverFloor.exists_unpaid_three_floor hu hU hy
    (by positivity : 0 < κ/5)
  obtain ⟨err₄,herr₄0,herr₄,hhigh⟩ := exists_unpaid_band_floor hu hU hy
    (by positivity : 0 < κ/5)
  obtain ⟨r₅,C₅,hr₅,hr₅1,hC₅,hfour⟩ := exists_unpaid_four_away_supply_floor hu hU hy
    (by positivity : 0 < κ/5)
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  let d := fun j => 4*zetaMoebiusLogMajorantMass (1+1/262144)*
    Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have hd0 (j : ℕ) : 0 ≤ d j := by
    dsimp [d]
    positivity [zetaMoebiusLogMajorantMass_nonneg (1+1/262144)]
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  have hdLim : Tendsto d atTop (𝓝 0) := by
    have ht := (ZetaRieszJointDominantFloor.Refined.tendsto_allowance.const_mul (2 : ℝ)).comp
      tendsto_dyadicMomentOrder
    simp only [mul_zero] at ht
    convert ht using 1
    funext j
    dsimp [d,Function.comp_def]
    ring
  have h₀ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₀1).mul_const C₀).comp
    tendsto_dyadicMomentOrder
  have h₁ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₁ hr₁1).mul_const (2*C₁)).comp
    tendsto_dyadicMomentOrder
  have h₂ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₂ hr₂1).mul_const (2*C₂)).comp
    tendsto_dyadicMomentOrder
  have h₃ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₃ hr₃1).mul_const (2*C₃)).comp
    tendsto_dyadicMomentOrder
  have h₅ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₅ hr₅1).mul_const (2*C₅)).comp
    tendsto_dyadicMomentOrder
  let err := fun j => r₀^(dyadicMomentOrder j)*C₀+e j+5*d j+
    2*r₁^(dyadicMomentOrder j)*C₁+2*r₂^(dyadicMomentOrder j)*C₂+2*r₃^(dyadicMomentOrder j)*C₃+err₄ j+2*r₅^(dyadicMomentOrder j)*C₅
  have herr : Tendsto err atTop (𝓝 0) := by
    have ht := (((((h₀.add heLim).add (hdLim.const_mul (5 : ℝ))).add h₁).add h₂).add h₃).add herr₄ |>.add h₅
    simp only [zero_mul,mul_zero,zero_add] at ht
    convert ht using 1
    funext j
    dsimp [err,Function.comp_def]
    ring
  refine ⟨h,err,hh,hhu,
    (fun j => by dsimp [err]; positivity [he0 j,hd0 j,herr₄0 j]),herr,?_⟩
  filter_upwards [hbase,hfive,hsix,hthree,hhigh,hfour,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
      with j hj hfive hsix hthree hhigh hfour hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q : ℕ := 0
  let P : ℕ := 0
  let V : ℕ := 0
  let R : ℕ := 0
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let E := S\tripleRestSpent S N Q P V R η h L w
  let E3 := E.filter (fun n : ℕ => n.primeFactors.card = 3)
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let E6 := E.filter (fun n : ℕ => n.primeFactors.card = 6)
  let E4p := (E.filter (fun n : ℕ => n.primeFactors.card = 4)).filter
    (fun n => PaidFour N L n)
  let Ehi := E.filter (fun n : ℕ => 7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55)
  let Epaid := E.filter (fun n : ℕ => n.primeFactors.card = 3 ∨
          n.primeFactors.card = 5 ∨ n.primeFactors.card = 6 ∨
          (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n))
  let Eo := E\Epaid
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  have hQlog : Real.log Q ≤ (N : ℝ)/128 := by simp only [Q,Nat.cast_zero,Real.log_zero]; positivity
  have ht := hthree Q P V R η h w hh hhu hηu hQlog hw
  have hp := hfive Q P V R η h w hh hhu hw
  have hq := hsix Q P V R η h w hh hhu hw
  have h5eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (5 : ℕ) ≠ 3)
  have h6eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (6 : ℕ) ≠ 3)
  have hbandFloor := hhigh Q P V R η h w hh hhu hw
  have hheq := high_rest_filter_eq S N Q P V R η h L w
  have hfourFloor := hfour Q P V R η h w hh hhu hw
  have h4eq := nontriple_rest_filter_eq S N Q P V R η h L w (by norm_num : (4 : ℕ) ≠ 3)
  dsimp only at hfourFloor
  rw [←h4eq] at hfourFloor
  dsimp only at hp hq ht hbandFloor
  rw [←h5eq] at hp
  rw [←h6eq] at hq
  rw [←hheq] at hbandFloor
  let units := (∑ i ∈ completeGrid N (Real.pi/y) y,
    Real.exp (-center (Real.pi/y) y i/2)*(center (Real.pi/y) y i)^N/N.factorial)+
    (∑ i ∈ completeGrid N (Real.pi/y+Real.pi/y) y,
      Real.exp (-center (Real.pi/y+Real.pi/y) y i/2)*
        (center (Real.pi/y+Real.pi/y) y i)^N/N.factorial)
  change -u^(N+1)*(κ/5)*units-d j-2*r₁^N*C₁ ≤ ((u : ℂ)^(N+1)*∑ n ∈ E5, f n).re at hp
  change -u^(N+1)*(κ/5)*units-d j-2*r₂^N*C₂ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E6, f n).re at hq
  change -u^(N+1)*(κ/5)*units-d j-2*r₃^N*C₃ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E3, f n).re at ht
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hp hq ht
  change -u^(N+1)*(κ/5)*units-err₄ j ≤
    ((u : ℂ)^(N+1)*∑ n ∈ Ehi, f n).re at hbandFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hbandFloor
  rw [show 8*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(dyadicMomentOrder j : ℝ)/1000000) = 2*d j by dsimp [d]; ring]
    at hfourFloor
  change -u^(N+1)*(κ/5)*units-2*d j-2*r₅^N*C₅ ≤
    ((u : ℂ)^(N+1)*∑ n ∈ E4p, f n).re at hfourFloor
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hfourFloor
  have hbudget := period_grids_cost_paid (by omega : 1 ≤ N) hc hy hhu hκeq w f (radialIndices N)
    (slabGrid N (Real.pi/y) y) (slabGrid N (Real.pi/y+Real.pi/y) y) hw hscale
    (Finset.Subset.refl _)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  rw [biUnion_slabGrid_eq,biUnion_slabGrid_eq] at hbudget
  change κ*units ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hbudget
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hpaid : -u^(N+1)*(∑ n ∈ Ys, f n).re/128-5*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*((∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
        (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re) := by
    nlinarith only [hscaled,hp,hq,ht,hbandFloor,hfourFloor]
  have hpaidEq := congrArg Complex.re (paid_parts E f N L)
  simp only [Complex.add_re] at hpaidEq
  change (∑ n ∈ E3, f n).re+(∑ n ∈ E5, f n).re+
    (∑ n ∈ E6, f n).re+(∑ n ∈ Ehi, f n).re+(∑ n ∈ E4p, f n).re = (∑ n ∈ Epaid, f n).re at hpaidEq
  rw [hpaidEq] at hpaid
  have hcost : 0 ≤ u^(N+1)*(∑ n ∈ Ys, f n).re/128+5*d j+
      2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅ := by
    positivity [hY.le,hd0 j,herr₄0 j]
  have hpaidMax : u^(N+1)*max (∑ n ∈ Epaid, f n).re 0-
      u^(N+1)*(∑ n ∈ Ys, f n).re/128-5*d j-
      2*r₁^N*C₁-2*r₂^N*C₂-2*r₃^N*C₃-err₄ j-2*r₅^N*C₅ ≤
      u^(N+1)*(∑ n ∈ Epaid, f n).re := by
    by_cases hp : 0 ≤ (∑ n ∈ Epaid, f n).re
    · rw [max_eq_left hp]
      linarith only [hcost]
    · rw [max_eq_right (le_of_not_ge hp),mul_zero,zero_sub]
      linarith only [hpaid]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
      n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n)) E)
      (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ Epaid, f n).re = (∑ n ∈ E, f n).re at hs
  let credits := max (∑ n ∈ Ts, f n).re 0
  let B := wholeTail S N R
  have hSpent := tripleRestSpent_zero (R := R) (L := L) S η
    (by omega : 1000 ≤ N) hh hhu w hw
  change tripleRestSpent S N Q P V R η h L w = Ys ∪ Ts ∪ B at hSpent
  change u^(N+1)*((∑ n ∈ S\(Ys ∪ Ts ∪ B), f n).re+
    max (∑ n ∈ Ts, f n).re 0+(63/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  rw [←hSpent] at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(63/64 : ℝ)*(∑ n ∈ Ys, f n).re)-r₀^N*C₀ ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := hcore
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(W+G+credits+max (∑ n ∈ Epaid, f n).re 0+(125/128 : ℝ)*(∑ n ∈ Ys, f n).re)-
      (r₀^N*C₀+e j+5*d j+2*r₁^N*C₁+2*r₂^N*C₂+2*r₃^N*C₃+err₄ j+2*r₅^N*C₅) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hb,hpaidMax,hbridge,hscaledLedger]
  exact hfinal

/-- With zero prime threshold, only the logarithmic count condition remains. -/
theorem tailCondition_zero (N n : ℕ) :
    ZetaRieszSevenPrimeHead.tailCondition N 0 n ↔
      ZetaRieszLogCountBudget.countThreshold N ≤ n.primeFactors.card := by
  simp [ZetaRieszSevenPrimeHead.tailCondition]

theorem wholeTail_zero_eq (S : Finset ℕ) (N : ℕ) :
    wholeTail S N 0 = S.filter (fun n => Squarefree n ∧
      ZetaRieszLogCountBudget.countThreshold N ≤ n.primeFactors.card) := by
  simp only [wholeTail,tailCondition_zero]

/-- The refunded supply reduces the four-prime joining debit from 63/128
to 3/128. This equality does not pay that remaining debit. -/
theorem refunded_four_supply_debit (E Y : Finset ℕ) (f : ℕ → ℂ)
    (hd : Disjoint E Y) :
    (∑ n ∈ E, f n).re+(125/128 : ℝ)*(∑ n ∈ Y, f n).re =
      (∑ n ∈ E ∪ Y, f n).re-(3/128 : ℝ)*(∑ n ∈ Y, f n).re := by
  rw [Finset.sum_union hd,Complex.add_re]
  ring

/-- The effective remainder has two precise geometries. No old exponential
small-prime head survives as an independent debit or support restriction. -/
theorem remaining_effective_geometry {u : ℝ} {N K n : ℕ}
    (A : Finset ℕ) (h L y : ℝ) (w : ℕ → ℝ)
    (hn : n ∈ (coreBand u N K\(radialSupply N h w ∪ wholeTail (coreBand u N K) N 0))\
      (coreBand u N K\(radialSupply N h w ∪ wholeTail (coreBand u N K) N 0)).filter
        (fun n : ℕ => n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
          n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
          (n.primeFactors.card = 4 ∧ PaidFour N L n)))
    (hne : residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n ≠ 0) :
    (n.primeFactors.card = 4 ∧ (SquarefreeVaughanLogSource.coefficient L n).re < 0 ∧
      ∀ q ∈ n.primeFactors, 2*(N : ℝ)/5 < Real.log q) ∨
      (56 ≤ n.primeFactors.card ∧ n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N) := by
  obtain ⟨hnE,hnot⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hncore,hnotTail⟩ := Finset.mem_sdiff.mp hnE
  have hnar := (Finset.mem_filter.mp hncore).1
  have hnon := (Finset.mem_filter.mp hnar).1
  have hret := (Finset.mem_sdiff.mp hnon).1
  have horig := (Finset.mem_sdiff.mp hret).1
  have hcount := (Finset.mem_filter.mp (Finset.mem_filter.mp horig).1).2.1
  have hcounts : ¬(n.primeFactors.card = 3 ∨ n.primeFactors.card = 5 ∨
      n.primeFactors.card = 6 ∨ (7 ≤ n.primeFactors.card ∧ n.primeFactors.card ≤ 55) ∨
      (n.primeFactors.card = 4 ∧ PaidFour N L n)) :=
    fun hc => hnot (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hncore,hnotTail⟩,hc⟩)
  by_cases h4 : n.primeFactors.card = 4
  · have hnotPaid : ¬PaidFour N L n := fun hp =>
      hcounts (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4,hp⟩))))
    have hnonpos : (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 :=
      le_of_not_gt (fun hp => hnotPaid (Or.inl hp))
    have hnzero : (SquarefreeVaughanLogSource.coefficient L n).re ≠ 0 :=
      fun hz => hne (ZetaRieszFourSmallFloor.atom_zero_of_coefficient_re A L y N n hz)
    have hneg := lt_of_le_of_ne hnonpos hnzero
    have hnotSmall : ¬ZetaRieszFourSmallFloor.SmallPrime N n :=
      fun hs => hnotPaid (Or.inr ⟨hneg,hs⟩)
    refine Or.inl ⟨h4,hneg,?_⟩
    intro q hq
    by_contra hh
    exact hnotSmall ⟨q,hq,le_of_not_gt hh⟩
  · have hs : Squarefree n := by
      by_contra hs
      apply hne
      simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,hs]
    have hlt : n.primeFactors.card < ZetaRieszLogCountBudget.countThreshold N := by
      by_contra hbad
      apply hnotTail
      apply Finset.mem_union_right
      rw [wholeTail_zero_eq]
      exact Finset.mem_filter.mpr ⟨hncore,hs,le_of_not_gt hbad⟩
    right
    exact ⟨by omega,hlt⟩

end RiemannGaussian.ZetaRieszLowCountRefund
