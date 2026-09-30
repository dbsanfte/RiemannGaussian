/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRoughFivePeriodFloor

set_option autoImplicit false

/-!
# Complete rough five-prime periods in the whole joined floor

One quantitative supply selection pays the old heads and the signed period
cost. The period-covered parts are removed only from the original unpaid
five-prime sector. All higher-count prefix/pair credits, favorable spent
terms, exact unmatched parts and geometric boundary errors remain.
-/

namespace RiemannGaussian.ZetaRieszRoughFiveJoinedFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime
open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszPrimeCountFrequency ZetaRieszParityPacket
open ZetaRieszFiveNegativeHead ZetaRieszLogCountBudget ZetaRieszSevenPrimeHead
open ZetaRieszSevenCountTail ZetaRieszRoughFivePeriodFloor
open ZetaRieszStaggeredFloor ZetaRieszMultiPeriodSix

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h

/-- The strongest original radial floor and its quantitative supply scale
use one selection. The explicit precision is reserved for complete rough
five-prime periods; all earlier payments and the original 1/64 reserve remain. -/
theorem eventually_core_floor_with_scale {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ c κ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 < c ∧ 0 < κ ∧
      κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialHeads S N P V (SquarefreeVaughanLogSource.length u N)
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (v M), f n).re) ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hpay⟩ :=
    eventually_joint_slabs_floor_with_period_budget hy
  refine ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,?_⟩
  filter_upwards [tendsto_dyadicMomentOrder.eventually hpay,
    tendsto_dyadicMomentOrder.eventually (eventually_length_on_slabs hu hU),
    eventually_radial_supply_in_core hu hU hh hhu,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2000 : ℕ))]
    with j hpay hL hsub hN
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let L := SquarefreeVaughanLogSource.length u N
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hP : Real.log P ≤ ε*N := log_floor_exp_le
    (mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N))
  have hV : Real.log V ≤ ζ*N := log_floor_exp_le
    (mul_nonneg hζ.le (Nat.cast_nonneg (α := ℝ) N))
  have hR : Real.log R ≤ θ*N := log_floor_exp_le
    (mul_nonneg hθ.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      (0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallHeads S M P V L, f n‖ ≤ (3/32 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTail S N R M, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ supply M h v, f n).re) ∧
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hH,hF,hG,hT,_⟩ := hpay M Q P V R S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallHeads S M P V L) (slabTail S N R M) A L
        (hL M hM).1 (by have := Finset.mem_range.mp (Finset.mem_filter.mp hM).1; omega) hQ hP hV hR (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hc,hlo,hhi,hmax,hsmall,hpos⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hmax,hsmall,hpos⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hlo,hhi.le,hsmall⟩)
        (by
          intro n hn
          obtain ⟨_,hs,hlo,hhi,hcount⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hlo,hhi.le,hcount⟩)
      exact ⟨v,fun _ => ⟨⟨hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩,hscale⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv' using hex
  let hv := fun (M : ℕ) (hM : M ∈ radialIndices N) => (hv' M hM).1
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ts := radialTail S N R
  let Ys := radialSupply N h v
  have hY : 0 < (∑ n ∈ Ys, f n).re := by
    change 0 < (∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending hhu hvb (fun M hM => (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.1)
  have hGpay := norm_radial_payment
    (fun _ _ _ _ hne => smallHeads_disjoint S P V L hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2.1)
  have hTpay := norm_radial_payment
    (fun _ _ _ _ hne => slabTail_disjoint S N R hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2.2)
  have hTsub : Ts ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hTcount : ∀ n ∈ Ts, 7 ≤ n.primeFactors.card := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact tailCondition_count_ge (by omega : 1 ≤ N) (Finset.mem_filter.mp hn).2.2.2.2
  have hXsub : Xs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hZsub : Zs ⊆ S\Xs := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hHsub : Hs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hFsub : Fs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hGsub : Gs ⊆ S := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).1
  have hG6 : ∀ n ∈ Gs, headCondition L P V n := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.2.2
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact ⟨(Finset.mem_filter.mp hn).2.2.1,(Finset.mem_filter.mp hn).2.2.2.2.2.2.2⟩
  have hX3 : ∀ n ∈ Xs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hZ3 : ∀ n ∈ Zs, n.primeFactors.card = 3 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hH4 : ∀ n ∈ Hs, n.primeFactors.card = 4 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hY4 : ∀ n ∈ Ys, n.primeFactors.card = 4 :=
    fun _ hn => (radial_supply_geometry hN hh hhu hvb hn).1
  have hdisj (B C : Finset ℕ) (hB : ∀ n ∈ B, n.primeFactors.card = 3)
      (hC : ∀ n ∈ C, n.primeFactors.card = 4) : Disjoint B C :=
    Finset.disjoint_left.mpr (fun n hb hc => by have := hB n hb; have := hC n hc; omega)
  have hXZ : Disjoint Xs Zs := Finset.disjoint_left.mpr
    (fun _ hx hz => (Finset.mem_sdiff.mp (hZsub hz)).2 hx)
  have hHY : Disjoint Hs Ys := by
    apply Finset.disjoint_left.mpr
    intro n hn hnY
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨_,_,_,_,_,_,r,hr,hrsmall⟩ := Finset.mem_filter.mp hn
    have hrlog := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (show (r : ℝ) ≤ Q by exact_mod_cast hrsmall)
    have hh := (radial_supply_geometry hN hh hhu hvb hnY).2 r hr
    have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hsuball : Xs ∪ Zs ∪ Hs ∪ Ys ⊆ S := by
    apply Finset.union_subset
    · exact Finset.union_subset (Finset.union_subset hXsub
        (fun _ hn => (Finset.mem_sdiff.mp (hZsub hn)).1)) hHsub
    · intro n hn
      obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
      exact hsub M hM (v M) (hvb M hM).1 (hvb M hM).2 hn
  have hFdisj : Disjoint Fs (Xs ∪ Zs ∪ Hs ∪ Ys) := by
    apply Finset.disjoint_left.mpr
    intro n hnF hn
    have hf := (hF5 n hnF).1
    rcases Finset.mem_union.mp hn with hn | hnY
    · rcases Finset.mem_union.mp hn with hn | hnH
      · rcases Finset.mem_union.mp hn with hnX | hnZ
        · have := hX3 n hnX; omega
        · have := hZ3 n hnZ; omega
      · have := hH4 n hnH; omega
    · have := hY4 n hnY; omega
  have hGdisj : Disjoint Gs (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs) := by
    apply Finset.disjoint_left.mpr
    intro n hnG hn
    have hg := hG6 n hnG
    have hgcount : n.primeFactors.card = 6 ∨ n.primeFactors.card = 5 := hg.elim
      (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · rcases hg with ⟨hc,_⟩ | ⟨_,hneg,_⟩
      · have := (hF5 n hnF).1; omega
      · linarith [(hF5 n hnF).2]
  have hTdisj : Disjoint Ts (Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    apply Finset.disjoint_left.mpr
    intro n hnT hn
    have ht := hTcount n hnT
    simp only [Finset.mem_union] at hn
    rcases hn with ((((hn | hn) | hn) | hn) | hn) | hn
    · have := hX3 n hn; omega
    · have := hZ3 n hn; omega
    · have := hH4 n hn; omega
    · have := hY4 n hn; omega
    · have := (hF5 n hn).1; omega
    · rcases hG6 n hn with ⟨hc,_⟩ | ⟨hc,_⟩ <;> omega
  have hfloor := ZetaRieszLogCountBudget.re_sum_ge_joint_spending f (Finset.union_subset (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hTsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hTdisj hXpay hZpay hHpay hFpay hGpay hTpay
  refine ⟨v,hvb,hY,fun M hM => (hv' M hM).2,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

private theorem missed_subset {S E : Finset ℕ} {N R : ℕ} (hN : 1 ≤ N)
    (hE : ∀ n ∈ E, n.primeFactors.card ≤ 6) :
    wholeTail S N R\radialTail S N R ⊆ S\(E ∪ radialTail S N R) := by
  intro n hn
  obtain ⟨hnW,hnT⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hnS,_,hc⟩ := Finset.mem_filter.mp hnW
  refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
  intro he
  rcases Finset.mem_union.mp he with he | he
  · have := hE n he
    have := tailCondition_count_ge hN hc
    omega
  · exact hnT he

private theorem rest_split (S E : Finset ℕ) (N R : ℕ) :
    (S\(E ∪ radialTail S N R))\(wholeTail S N R\radialTail S N R) =
      S\(E ∪ radialTail S N R ∪ wholeTail S N R) := by
  ext n
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

/-- The enlarged count tail, including both radial edges, is paid in the
floor direction. Every earlier radial payment and its signed rest remain. -/
theorem eventually_core_full_floor_with_scale {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ c κ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 < c ∧ 0 < κ ∧
      κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2) ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialHeads S N P V (SquarefreeVaughanLogSource.length u N)
        let Ts := radialTail S N R
        let Ys := radialSupply N h v
        let B := wholeTail S N R
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ Ts ∪ B), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          (∀ M ∈ radialIndices N,
            c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
              (∑ n ∈ supply M h (v M), f n).re) ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hspend⟩ :=
    eventually_core_floor_with_scale hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_missed_tail_bound
  refine ⟨η,h,δ,ε,ζ,θ,c,κ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hc,hκ,hκeq,hr,hr1,hC,?_⟩
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hN
  obtain ⟨v,hvb,hY,hscale,hbase⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ys := radialSupply N h v
  let Ts := radialTail S N R
  let B := wholeTail S N R
  let E := Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs
  let D := B\Ts
  have hDsub : D ⊆ S\(E ∪ Ts) := missed_subset (by omega : 1 ≤ N)
    (fun n hn => ZetaRieszLogCountTail.old_selection_count_le S η Q P V L (by omega) hh hhu hvb hn)
  have hnorm := hmissed N R S A y u hN (by linarith) hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ r^N*C at hnorm
  have hreal := (Complex.abs_re_le_norm _).trans hnorm
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hreal
  obtain ⟨hlo,hhi⟩ := abs_le.mp hreal
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [rest_split S E N R] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,hscale,?_⟩
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts ∪ B), f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts), f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hbase
  rw [← hre] at hbase
  nlinarith only [hbase,hlo]

/-- Complete periods assigned to distinct two-unit radial slabs cannot
reuse a grid index. Cells assign CENTERS; complete periods may cross
cell boundaries, so the payment does not create internal clipped periods. -/
theorem slab_grids_disjoint {y v : ℝ} (H : Finset ℕ)
    (I : ℕ → Finset ℕ)
    (hI : ∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
      center v y i < 2*M+2) :
    (H : Set ℕ).PairwiseDisjoint I := by
  intro M hM M' hM' hne
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  have ht := hI M hM i hi
  have ht' := hI M' hM' i hi'
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (M : ℝ)+1 ≤ M' := by exact_mod_cast h
    linarith only [ht.2,ht'.1,hh]
  · have hh : (M' : ℝ)+1 ≤ M := by exact_mod_cast h
    linarith only [ht'.2,ht.1,hh]

/-- The SAME quantitative supply selection that paid every older sector
pays both growing period grids. No separately chosen phase window or
compatibility assumption enters this global estimate. -/
theorem period_grids_cost_paid {N : ℕ} (hN : 1 ≤ N) {c κ h y v : ℝ}
    (hc : 0 < c) (hy : 54 ≤ y) (hhu : h ≤ 1/20)
    (hκ : κ = c/(512*((⌊2*y⌋₊ : ℝ)+1)*Real.exp 2))
    (w : ℕ → ℝ) (f : ℕ → ℂ) (H : Finset ℕ) (I J : ℕ → Finset ℕ)
    (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hscale : ∀ M ∈ radialIndices N,
      c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M ≤
        (∑ n ∈ supply M h (w M), f n).re)
    (hH : H ⊆ radialIndices N)
    (hI : ∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
      center v y i < 2*M+2)
    (hJ : ∀ M ∈ H, ∀ i ∈ J M,
      2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
      center (v+Real.pi/y) y i < 2*M+2) :
    κ*((∑ i ∈ H.biUnion I, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ H.biUnion J, Real.exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
      (1/128 : ℝ)*(∑ n ∈ radialSupply N h w, f n).re := by
  have hnonneg M (hM : M ∈ radialIndices N) :
      0 ≤ (∑ n ∈ supply M h (w M), f n).re := by
    exact (show 0 ≤ c*(M : ℝ)*Real.exp (2*(M : ℝ))/((M : ℝ)+1)*radialEnvelope N M
      by positivity [radialEnvelope_nonneg N M]).trans (hscale M hM)
  have hrow M (hM : M ∈ H) :
      κ*((∑ i ∈ I M, Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
        (∑ i ∈ J M, Real.exp (-center (v+Real.pi/y) y i/2)*
          (center (v+Real.pi/y) y i)^N/N.factorial)) ≤
        (1/128 : ℝ)*(∑ n ∈ supply M h (w M), f n).re := by
    have hlo := (Finset.mem_filter.mp (hH hM)).2.1
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hm0 : 0 < M := by
      exact_mod_cast (show (0 : ℝ) < M by linarith only [hlo,hNR])
    have hNM : N ≤ 2*M := by
      exact_mod_cast (show (N : ℝ) ≤ 2*M by linarith only [hlo,hNR])
    have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hm0
    let U := Real.exp (2*(M : ℝ))*radialEnvelope N M
    have hU0 : 0 ≤ U := by dsimp [U]; positivity [radialEnvelope_nonneg N M]
    have hlow : (c/2)*U ≤ (∑ n ∈ supply M h (w M), f n).re := by
      apply le_trans _ (hscale M (hH hM))
      have hr : (1/2 : ℝ) ≤ (M : ℝ)/(M+1) :=
        (le_div_iff₀ (by positivity)).mpr (by linarith)
      have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hc.le) hU0
      convert hb using 1 <;> dsimp only [U] <;> ring
    have hd := period_debit_le_scale hc.le hy hm0 hNM (I M) (J M) v
      (fun i hi => ⟨(hI M hM i hi).1,(hI M hM i hi).2.le⟩)
      (fun i hi => ⟨(hJ M hM i hi).1,(hJ M hM i hi).2.le⟩)
    have hb := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 1/128)
    rw [hκ]
    exact hd.trans (by convert hb using 1; dsimp only [U]; ring)
  rw [Finset.sum_biUnion (slab_grids_disjoint H I hI),
    Finset.sum_biUnion (slab_grids_disjoint H J hJ)]
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs ⊢
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/128)
  rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hw),Complex.re_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hH (fun M hM _ => hnonneg M hM)

/-- Complete rough five-prime periods are now spent IN the whole
joinedPhysical floor. All former credits and higher-count savings remain.
The new period debit consumes only half the former 1/64 reserve; its
other 1/128 remains positive. The uncovered arithmetic sign parts are
literal, so no numerical floor or zero exclusion is asserted. -/
theorem eventually_joined_floor_with_rough_periods {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 54 ≤ y) :
    ∃ η h δ ε ζ θ : ℝ, ∃ err : ℕ → ℝ,
      0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧
      0 < θ ∧ θ ≤ 1/128 ∧ (∀ j, 0 ≤ err j) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠ j : ℕ in atTop, ∃ w : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ w M ∧ w M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let V := ⌊Real.exp (ζ*N)⌋₊
        let R := ⌊Real.exp (θ*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let Gs := radialHeads S N P V L
        let Ts := radialTail S N R
        let Ys := radialSupply N h w
        let E := S\spent S N Q P V R η h L w
        let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
        let Eo := E\E5
        let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
          max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
        let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
          weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
            ZetaRieszPairChamberFloor.pairSaving L y n)
        0 < (∑ n ∈ Ys, f n).re ∧ 0 ≤ G ∧
          ∀ (B : ℕ) (H : Finset ℕ) (I J : ℕ → Finset ℕ) (v : ℝ),
            Q ≤ B → V ≤ B → H ⊆ radialIndices N →
            Real.cos (y*v) = -1 →
            (∀ M ∈ H, ∀ i ∈ I M, 2*(M : ℝ) ≤ center v y i ∧
              center v y i < 2*M+2) →
            (∀ M ∈ H, ∀ i ∈ J M,
              2*(M : ℝ) ≤ center (v+Real.pi/y) y i ∧
              center (v+Real.pi/y) y i < 2*M+2) →
            (∀ i ∈ H.biUnion I, (39/20 : ℝ)*N ≤ center v y i-Real.pi/y ∧
              center v y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            (∀ i ∈ H.biUnion J,
              (39/20 : ℝ)*N ≤ center (v+Real.pi/y) y i-Real.pi/y ∧
              center (v+Real.pi/y) y i+Real.pi/y ≤ (203/100 : ℝ)*N) →
            let X := (H.biUnion I).biUnion (fun i => roughPeriod B (center v y i) y)
            let Y := (H.biUnion J).biUnion (fun i => roughPeriod B (center (v+Real.pi/y) y i) y)
            let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
              (∑ n ∈ E5\Y, signedPart (-1) A L y N n);
            u^(N+1)*(U+W+G+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
              max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
              max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+
              (∑ n ∈ Ys, f n).re/128)-err j ≤
                ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,c,κ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
      hc,hκ,hκeq,hr,hr1,hC,hbase⟩ := eventually_core_full_floor_with_scale hu hU hy
  let e := fun j => ‖(u : ℂ)^(dyadicMomentOrder j+1)*
    (coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y (dyadicMomentOrder j) (dyadicPrimeCount j))‖
  have he0 (j : ℕ) : 0 ≤ e j := norm_nonneg _
  have heLim : Tendsto e atTop (𝓝 0) := by
    have ht := (ZetaRieszGammaJoint.tendsto_core_sub_joined (by linarith : 0 < u)
      hU (fun _ => y) dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder).norm
    simpa only [norm_zero] using ht
  let err := fun j => r^(dyadicMomentOrder j)*C+e j
  have hevent : Tendsto err atTop (𝓝 0) := by
    have ht := (((tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).mul_const C).comp
      tendsto_dyadicMomentOrder).add heLim
    simpa only [err,Function.comp_def,zero_mul,zero_add] using ht
  refine ⟨η,h,δ,ε,ζ,θ,err,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,
    (fun j => add_nonneg (mul_nonneg (pow_nonneg hr _) hC) (he0 j)),hevent,?_⟩
  filter_upwards [hbase,
    eventually_unpaid_rough_five_floor hu hU hy hκ,
    tendsto_dyadicMomentOrder.eventually
      (ZetaRieszPairChamberFloor.eventually_core_subset_floor hu hU),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (1 : ℕ))]
      with j hj hrough hbound hN
  obtain ⟨w,hw,hY,hscale,hcore⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P := ⌊Real.exp (ε*N)⌋₊
  let V := ⌊Real.exp (ζ*N)⌋₊
  let R := ⌊Real.exp (θ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialHeads S N P V L
  let Ts := radialTail S N R
  let Ys := radialSupply N h w
  let E := S\spent S N Q P V R η h L w
  let E5 := E.filter (fun n : ℕ => n.primeFactors.card = 5)
  let Eo := E\E5
  let W := ∑ n ∈ Eo, if 7 ≤ n.primeFactors.card then
    max (f n).re 0-weight A N n*ZetaRieszSevenPrimeReflection.floorCost L y n else (f n).re
  let G := ∑ n ∈ Eo.filter (fun n : ℕ => 7 ≤ n.primeFactors.card),
    weight A N n*(ZetaRieszJoinedPrefixFloor.cutoffSaving L y n+
      ZetaRieszPairChamberFloor.pairSaving L y n)
  have hG : 0 ≤ G := Finset.sum_nonneg (fun n _ => mul_nonneg (weight_nonneg A N n)
    (add_nonneg (ZetaRieszJoinedPrefixFloor.cutoffSaving_nonneg L y n)
      (ZetaRieszPairChamberFloor.pairSaving_nonneg L y n)))
  refine ⟨w,hw,hY,hG,?_⟩
  intro B H I J v hQ hV hH hpeak hI hJ hiCore hjCore
  have hp := hrough Q P V R B η h w (H.biUnion I) (H.biUnion J) v
    hh hhu hw hQ hV hpeak hiCore hjCore
  have hd := period_grids_cost_paid hN hc hy hhu hκeq w f H I J
    hw hscale hH hI hJ
  let X := (H.biUnion I).biUnion (fun i => roughPeriod B (center v y i) y)
  let Y := (H.biUnion J).biUnion (fun i => roughPeriod B (center (v+Real.pi/y) y i) y)
  let U := (∑ n ∈ E5\X, signedPart 1 A L y N n)+
    (∑ n ∈ E5\Y, signedPart (-1) A L y N n)
  have hpaid : U ≤ (∑ n ∈ E5, f n).re+(∑ n ∈ Ys, f n).re/128 := by
    change U-κ*((∑ i ∈ H.biUnion I,
      Real.exp (-center v y i/2)*(center v y i)^N/N.factorial)+
      (∑ i ∈ H.biUnion J, Real.exp (-center (v+Real.pi/y) y i/2)*
        (center (v+Real.pi/y) y i)^N/N.factorial)) ≤ (∑ n ∈ E5, f n).re at hp
    change _ ≤ (1/128 : ℝ)*(∑ n ∈ Ys, f n).re at hd
    linarith only [hp,hd]
  have hb := hbound (dyadicPrimeCount j) y Eo
    (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
  change u^(N+1)*(W+G) ≤ ((u : ℂ)^(N+1)*∑ n ∈ Eo, f n).re at hb
  rw [← Complex.ofReal_pow,Complex.re_ofReal_mul] at hb
  have hs := congrArg Complex.re (Finset.sum_sdiff (Finset.filter_subset
    (fun n : ℕ => n.primeFactors.card = 5) E) (f := f))
  change (∑ n ∈ Eo, f n).re+(∑ n ∈ E5, f n).re = (∑ n ∈ E, f n).re at hs
  let credits := max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0
  change u^(N+1)*((∑ n ∈ E, f n).re+max (∑ n ∈ Xs, f n).re 0+
    max (∑ n ∈ Zs, f n).re 0+max (∑ n ∈ Hs, f n).re 0+
    max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+
    max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hcore
  have hcore' : u^(N+1)*((∑ n ∈ E, f n).re+credits+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
      ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
    convert hcore using 1
    dsimp only [credits]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hpaid (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  have hbridge := Complex.re_le_norm ((u : ℂ)^(N+1)*
    (coreResponse u y N (dyadicPrimeCount j)-
      ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)))
  rw [mul_sub,Complex.sub_re] at hbridge
  conv at hbridge => rhs; rw [← mul_sub]
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re-
    ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re ≤ e j at hbridge
  have hscaledLedger := congrArg (fun x : ℝ => u^(N+1)*x) hs
  have hfinal : u^(N+1)*(U+W+G+credits+(∑ n ∈ Ys, f n).re/128)-(r^N*C+e j) ≤
      ((u : ℂ)^(N+1)*ZetaRieszGammaJoint.joinedPhysical u y N (dyadicPrimeCount j)).re := by
    nlinarith only [hcore',hscaled,hb,hbridge,hscaledLedger]
  convert hfinal using 1
  dsimp only [credits]
  ring

end
end RiemannGaussian.ZetaRieszRoughFiveJoinedFloor
