/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixPrimeHead

/-!
# Paying an exponential six-prime head in both original signed ledgers

The minimum-prime coefficient and fractional prime mass bound pay a fixed
exponential head with both coefficient signs. Earlier selected widths are
retained. One original supply pays all selected charges; all favorable
observations and one exact signed complement remain.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeExponentialHead
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime
open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszPrimeCountFrequency ZetaRieszParityPacket

/-- The earlier signed supply and head width are retained while a
separate fixed exponential six-prime width costs one sixteenth. -/
theorem eventually_joint_slabs_floor {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ ε : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q P : ℕ) (D S H F G A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → Real.log P ≤ ε*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧ n.primeFactors.card = 6 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          ∃ r ∈ n.primeFactors, r ≤ P) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := (∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszFivePositiveHead.eventually_joint_slabs_spending_log_head_with_scale hy
  obtain ⟨ε,hε,hεu,hsmall⟩ := ZetaRieszSixPrimeHead.eventually_small_six_log_cost
    (show 0 < c/16 by positivity)
  refine ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,?_⟩
  filter_upwards [hpay,hsmall]
    with N hpay hsmall M Q P D S H F G A L hNM hQ hP hL0 hL hLu hH hF hG
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_⟩
  have hGpay := hsmall M P G A L y hNM hP hL0 hL hG
  have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/16)
  apply hGpay.trans
  convert h using 1
  ring

/-- The earlier signed supply and head width are retained while a
separate fixed exponential six-prime width costs one sixteenth. -/
theorem eventually_joint_slabs_ceiling {y : ℝ} (hy : 16 ≤ |y|) :
    ∃ η h δ ε : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (M Q P : ℕ) (D S H F G A : Finset ℕ) (L : ℝ),
        N ≤ 2*M → Real.log Q ≤ δ*N → Real.log P ≤ ε*N → 0 < L → (271/200 : ℝ)*M ≤ L → L ≤ (143/100 : ℝ)*M →
        (∀ n ∈ H, Squarefree n ∧ n.primeFactors.card = 4 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ ∃ r ∈ n.primeFactors, r ≤ Q) →
        (∀ n ∈ F, Squarefree n ∧ n.primeFactors.card = 5 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          (∀ p ∈ n.primeFactors, Real.log p ≤ (5/4 : ℝ)*M) ∧ (∃ r ∈ n.primeFactors, r ≤ Q) ∧
          0 < (SquarefreeVaughanLogSource.coefficient L n).re) →
        (∀ n ∈ G, Squarefree n ∧ n.primeFactors.card = 6 ∧
          2*(M : ℝ) ≤ Real.log n ∧ Real.log n ≤ 2*(M : ℝ)+2 ∧
          ∃ r ∈ n.primeFactors, r ≤ P) →
        ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1/2 ∧
          let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
          let Y := -(∑ n ∈ supply M h v, f n).re
          0 < Y ∧
            ‖∑ n ∈ slabTriples D M η, f n‖ ≤ (1/2 : ℝ)*Y ∧
            ‖∑ n ∈ smallTriples S M Q, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ H, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ F, f n‖ ≤ (1/8 : ℝ)*Y ∧
            ‖∑ n ∈ G, f n‖ ≤ (1/16 : ℝ)*Y := by
  obtain ⟨η,h,δ,c,hη,hηu,hh,hhu,hδ,hδu,hc,hpay⟩ :=
    ZetaRieszHeadCeiling.eventually_joint_slabs_upper_log_head_with_scale hy
  obtain ⟨ε,hε,hεu,hsmall⟩ := ZetaRieszSixPrimeHead.eventually_small_six_log_cost
    (show 0 < c/16 by positivity)
  refine ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,?_⟩
  filter_upwards [hpay,hsmall]
    with N hpay hsmall M Q P D S H F G A L hNM hQ hP hL0 hL hLu hH hF hG
  obtain ⟨v,hv,hvu,hscale,hY,hX,hZ,hHpay,hFpay⟩ :=
    hpay M Q D S H F A L hNM hQ hL0 hL hLu hH hF
  refine ⟨v,hv,hvu,hY,hX,hZ,hHpay,hFpay,?_⟩
  have hGpay := hsmall M P G A L y hNM hP hL0 hL hG
  have h := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 1/16)
  apply hGpay.trans
  convert h using 1
  ring


/-- Literal six-prime head through an arbitrary prime threshold in a
half-open original radial slab, including both coefficient signs. -/
def smallSixes (S : Finset ℕ) (M Q : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 6 ∧
    2*(M : ℝ) ≤ Real.log n ∧ Real.log n < 2*(M : ℝ)+2 ∧
    ∃ r ∈ n.primeFactors, r ≤ Q)

/-- The arbitrary-threshold six-prime head within the original radial union. -/
def radialSixes (S : Finset ℕ) (N Q : ℕ) : Finset ℕ :=
  (radialIndices N).biUnion (fun M => smallSixes S M Q)

/-- Arbitrary-threshold radial heads are pairwise disjoint. -/
theorem smallSixes_disjoint (S : Finset ℕ) (N : ℕ) :
    Pairwise (fun M M' : ℕ => Disjoint (smallSixes S M N) (smallSixes S M' N)) := by
  intro M M' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := (Finset.mem_filter.mp hn).2
  have hb' := (Finset.mem_filter.mp hn').2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2.2.2.1,hb'.2.2.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2.2.2.1,hb.2.2.1]

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h


/-- The actual core ledger pays the exponential six-prime radial head
from the same supply. Prior head widths remain unchanged. -/
theorem eventually_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N P
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hpay⟩ := eventually_joint_slabs_floor hy
  refine ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,?_⟩
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
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N P
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hP : Real.log P ≤ ε*N := log_floor_exp_le
    (mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallSixes S M P, f n‖ ≤ (1/16 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG⟩ := hpay M Q P S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallSixes S M P) A L
        (hL M hM).1 hQ hP (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
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
          obtain ⟨_,hs,hc,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
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
    (fun _ _ _ _ hne => smallSixes_disjoint S P hne) hhu hvb
    (fun M hM => (hv M hM).2.2.2.2.2.2.2)
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
  have hG6 : ∀ n ∈ Gs, n.primeFactors.card = 6 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
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
    have hf := hF5 n hnF
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
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · have := hF5 n hnF; omega
  have hfloor := ZetaRieszSixPrimeHead.re_sum_ge_joint_spending f (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hXpay hZpay hHpay hFpay hGpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- The actual core ledger pays the exponential six-prime radial head
from the same supply. Prior head widths remain unchanged. -/
theorem eventually_core_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N P
        let Ys := radialSupply N h v
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) := by
  obtain ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hpay⟩ := eventually_joint_slabs_ceiling hy
  refine ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,?_⟩
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
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N P
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hQ : Real.log Q ≤ δ*N := log_floor_exp_le
    (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N))
  have hP : Real.log P ≤ ε*N := log_floor_exp_le
    (mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) N))
  have hex : ∀ M : ℕ, ∃ v : ℝ, M ∈ radialIndices N →
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < -(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallSixes S M P, f n‖ ≤ (1/16 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG⟩ := hpay M Q P S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallSixes S M P) A L
        (hL M hM).1 hQ hP (SquarefreeVaughanLogSource.length_pos _ _) (hL M hM).2.1 (hL M hM).2.2
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
          obtain ⟨_,hs,hc,hlo,hhi,hsmall⟩ := Finset.mem_filter.mp hn
          exact ⟨hs,hc,hlo,hhi.le,hsmall⟩)
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ys := radialSupply N h v
  have hY : 0 < -(∑ n ∈ Ys, f n).re := by
    change 0 < -(∑ n ∈ radialSupply N h v, f n).re
    rw [radialSupply,Finset.sum_biUnion (supply_disjoint hhu hvb),Complex.re_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_pos'
    · intro M hM
      exact (hv M hM).2.2.1.le
    · exact ⟨N,self_mem_radialIndices (by omega),(hv N (self_mem_radialIndices (by omega))).2.2.1⟩
  have hXpay := union_spending (f := fun n => -f n) hhu hvb (fun M hM => by
    simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.1)
  have hZpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallTriples_disjoint (S\Xs) Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.1)
  have hHpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallFours_disjoint S Q hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.1)
  have hFpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallPositiveFives_disjoint S Q L hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.1)
  have hGpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => smallSixes_disjoint S P hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.2)
  simp only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] at hXpay hZpay hHpay hFpay hGpay
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
  have hG6 : ∀ n ∈ Gs, n.primeFactors.card = 6 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
  have hF5 : ∀ n ∈ Fs, n.primeFactors.card = 5 := by
    intro n hn
    obtain ⟨M,_,hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hn).2.2.1
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
    have hf := hF5 n hnF
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
    rcases Finset.mem_union.mp hn with hn | hnF
    · rcases Finset.mem_union.mp hn with hn | hnY
      · rcases Finset.mem_union.mp hn with hn | hnH
        · rcases Finset.mem_union.mp hn with hnX | hnZ
          · have := hX3 n hnX; omega
          · have := hZ3 n hnZ; omega
        · have := hH4 n hnH; omega
      · have := hY4 n hnY; omega
    · have := hF5 n hnF; omega
  have hfloor := ZetaRieszSixPrimeHead.re_sum_le_joint_spending f (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hXpay hZpay hHpay hFpay hGpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re ≤ _
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- Every six-prime head label in the inner window is paid, for every
prime threshold. No largest-share or sign restriction is added. -/
theorem mem_radialSixes_of_geometry {S : Finset ℕ} {N n Q : ℕ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hc : n.primeFactors.card = 6)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hsmall : ∃ r ∈ n.primeFactors, r ≤ Q) : n ∈ radialSixes S N Q := by
  let M := ⌊Real.log n/2⌋₊
  have hNR : (4000 : ℝ) ≤ N := by exact_mod_cast hN
  have hfloor : (M : ℝ) ≤ Real.log n/2 := Nat.floor_le (by positivity [Real.log_natCast_nonneg n])
  have hceil : Real.log n/2 < (M : ℝ)+1 := Nat.lt_floor_add_one _
  have hM : M ∈ radialIndices N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_,?_⟩
    · have h : M ≤ 2*N := by
        have h' : (M : ℝ) ≤ 2*N := by linarith
        exact_mod_cast h'
      omega
    constructor <;> linarith
  exact Finset.mem_biUnion.mpr ⟨M,hM,Finset.mem_filter.mpr
    ⟨hnS,hs,hc,by linarith,by linarith,hsmall⟩⟩

/-- The whole six-prime head at its actual finite threshold, including
all original core boundaries. -/
def wholeSixes (S : Finset ℕ) (Q : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ n.primeFactors.card = 6 ∧
    ∃ p ∈ n.primeFactors, p ≤ Q)

open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- The same original vanishing boundary allowance pays all omissions
of the two exponential head selections together. -/
theorem exists_full_head_missed_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (j : ℕ) (η δ ε y u : ℝ), 32 ≤ j → 4000 ≤ dyadicMomentOrder j →
        0 < η → 4 ≤ η*dyadicMomentOrder j →
        0 ≤ δ → 1/2 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P₆ := ⌊Real.exp (ε*N)⌋₊
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let L := SquarefreeVaughanLogSource.length u N
        let S := coreBand u N (dyadicPrimeCount j)
        let X := radialTriples S N η
        let Z := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q)
        let H := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let F := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
        let G := radialSixes S N P₆
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) ∧
          ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P₆
        ‖(u : ℂ)^(N+1)*∑ n ∈ B\(X ∪ Z ∪ H ∪ F ∪ G),
          residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
            r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000) := by
  obtain ⟨r,C,hr,hr1,hC,hbound⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro j η δ ε y u hj hN hη hηN hδ hu hU
  dsimp only
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let P₆ := ⌊Real.exp (ε*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let S := coreBand u N (dyadicPrimeCount j)
  let X := radialTriples S N η
  let Z := (radialIndices N).biUnion (fun M => smallTriples (S\X) M Q)
  let H := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let F := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let G := radialSixes S N P₆
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient L n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P₆
  let D := B\(X ∪ Z ∪ H ∪ F ∪ G)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let P := fun n : ℕ => Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
    ∃ p ∈ n.primeFactors, p ∈ A ∧ ZetaRieszJointAllocation.eligibleCofactor p (n/p) ∧
      (601/1000 : ℝ)*Real.log n ≤ Real.log p
  let E := (D.filter (fun n => ¬P n)).filter (fun n => residualCoefficient A L N n ≠ 0)
  have hE : deviationBand E (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnE,hlo,hhi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnD,hcoeff⟩ := Finset.mem_filter.mp hnE
    obtain ⟨hnD,hnP⟩ := Finset.mem_filter.mp hnD
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hnD
    rcases Finset.mem_union.mp hnB with hnB | hn6
    · have hnold : n ∉ X ∪ Z ∪ H ∪ F :=
        fun h => hnnot (Finset.mem_union_left G h)
      rcases Finset.mem_union.mp hnB with hbal | hnB
      · exact hnold (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (balanced_mem_radialTriples hN hη hηN hbal hlo hhi))))
      obtain ⟨hnS,hs,hcount,p,hp,hpQ⟩ := Finset.mem_filter.mp hnB
      have hmax := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt j hj u
        (Finset.mem_filter.mpr ⟨hnS,hnP⟩) hcoeff
      have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hplog : Real.log p ≤ δ*N := by
        have h := Real.log_le_log hpR (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
        exact h.trans (log_floor_exp_le (mul_nonneg hδ (Nat.cast_nonneg (α := ℝ) N)))
      rcases hcount with h3 | h4 | ⟨h5,hpos⟩
      · exact hnold (Finset.mem_union_left _ (mem_exponential_paid_of_geometry hN hnS hs
          (Or.inl h3) hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
      · exact hnold (Finset.mem_union_left _ (mem_exponential_paid_of_geometry hN hnS hs
          (Or.inr h4) hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
      · exact hnold (Finset.mem_union_right _ (mem_exponential_positive_paid_of_geometry
          hN hnS hs h5 hpos hlo hhi (fun p hp => (hmax p hp).le) ⟨p,hp,hplog⟩))
    · obtain ⟨hnS,hs,hcount,hsmall⟩ := Finset.mem_filter.mp hn6
      exact hnnot (Finset.mem_union_right _
        (mem_radialSixes_of_geometry hN hnS hs hcount hlo hhi hsmall))
  have hEsum : (∑ n ∈ E, f n) = ∑ n ∈ D.filter (fun n => ¬P n), f n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnE
    have hz : residualCoefficient A L N n = 0 := by
      by_contra h
      exact hnE (Finset.mem_filter.mpr ⟨hn,h⟩)
    simp only [f,hz,zero_mul]
  have hedge := hbound N E (residualCoefficient A L N)
    (fun n _ => ZetaRieszJointAllocation.norm_residualCoefficient_le A
      (SquarefreeVaughanLogSource.length_pos u N) N n) y u (by linarith) hU
  have hedge' : ‖(u : ℂ)^(N+1)*∑ n ∈ D.filter (fun n => ¬P n), f n‖ ≤ r^N*C := by
    rw [← hEsum]
    simpa only [hE,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
      SquarefreeEulerQuadratic.primeFilterKernel_one,f,L] using hedge
  have hL : L ≤ (139/100 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hlog : 2*Real.log 2 ≤ (139/100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hdom := ZetaRieszJointDominantFloor.Refined.norm_scaled_sum_le A (D.filter P)
    N (by omega : 320 ≤ N) y (by linarith : 0 ≤ u) hU
    (SquarefreeVaughanLogSource.length_pos u N) hL (by
      intro n hn
      obtain ⟨_,hs,hn1,hnp,p,hp,hpA,hel,hdom⟩ := Finset.mem_filter.mp hn
      refine ⟨hs,hn1,hnp,p,hp,hpA,hel,?_,hdom⟩
      have hp' := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hpA
      exact (Real.log_lt_log (by exact_mod_cast hp'.1.pos) (by exact_mod_cast hp'.2.2)).le)
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not D P f,mul_add]
  exact (norm_add_le _ _).trans ((add_le_add hdom hedge').trans_eq (by ring))

private theorem sdiff_union_payment (S X Z H Y F G B : Finset ℕ) :
    (S\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G))\(B\(X ∪ Z ∪ H ∪ F ∪ G)) =
      S\(X ∪ Z ∪ H ∪ Y ∪ F ∪ G ∪ B) := by
  ext n
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

/-- The entire six-prime exponential head is paid in the original core.
All prior charges, favorable observations and one sixteenth of ONE
supply remain, with one exact signed rest and the paid boundary error. -/
theorem eventually_core_full_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Ys := radialSupply N h v
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N P
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n
        0 < (∑ n ∈ Ys, f n).re ∧
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)-
              (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) ≤
                ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hspend⟩ := eventually_core_floor hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_full_head_missed_bound
  refine ⟨η,h,δ,ε,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η)] with j hj hj32 hN hsize
  obtain ⟨v,hvb,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let P := ⌊Real.exp (ε*N)⌋₊
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Ys := radialSupply N h v
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N P
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P
  let D := B\(Xs ∪ Zs ∪ Hs ∪ Fs ∪ Gs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed j η δ ε y u hj32 hN hη hηN hδ.le hu.le hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _ at hnorm
  have hreal : -(r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000)) ≤ u^(N+1)*(∑ n ∈ D, f n).re := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY : Disjoint B Ys := by
    apply Finset.disjoint_left.mpr
    intro n hnB hnY
    have hsupply := radial_supply_geometry (by omega : 2000 ≤ N) hh hhu hvb hnY
    rcases Finset.mem_union.mp hnB with hnB | hn6
    ·
      rcases Finset.mem_union.mp hnB with hbal | hhead
      · have hc := (Finset.mem_filter.mp hbal).2.2.1
        omega
      obtain ⟨_,_,_,p,hp,hpQ⟩ := Finset.mem_filter.mp hhead
      have hplog : Real.log p ≤ δ*N := by
        have ht := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
          (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
        exact ht.trans (log_floor_exp_le (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N)))
      have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
      linarith [(hsupply.2 p hp),Nat.cast_nonneg (α := ℝ) N]
    · have hc := (Finset.mem_filter.mp hn6).2.2.1
      omega

  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn
      · rcases Finset.mem_union.mp hn with hn | hn <;> exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    have hnY : n ∉ Ys := fun h => Finset.disjoint_left.mp hBY hnB h
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | hg
    · rcases Finset.mem_union.mp h with h | hf
      · rcases Finset.mem_union.mp h with h | hy
        · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_left Fs h))
        · exact hnY hy
      · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_right _ hf))
    · exact hnnot (Finset.mem_union_right _ hg)
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs))\D =
      S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B) := by
    exact sdiff_union_payment S Xs Zs Hs Ys Fs Gs B
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)-_ ≤ _
  change u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n).re+
    max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) ≤ _ at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]

/-- The entire six-prime exponential head is paid in the original core.
All prior charges, favorable observations and one sixteenth of ONE
supply remain, with one exact signed rest and the paid boundary error. -/
theorem eventually_core_full_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let Q := ⌊Real.exp (δ*N)⌋₊
        let P := ⌊Real.exp (ε*N)⌋₊
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
        let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
        let Ys := radialSupply N h v
        let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q (SquarefreeVaughanLogSource.length u N))
        let Gs := radialSixes S N P
        let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
          (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P
        let W := ∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)+
                (r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*Real.exp (-(N : ℝ)/1000000)) := by
  obtain ⟨η,h,δ,ε,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hspend⟩ := eventually_core_ceiling hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_full_head_missed_bound
  refine ⟨η,h,δ,ε,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hr,hr1,hC,?_⟩
  have hord : Tendsto (fun j => (dyadicMomentOrder j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_dyadicMomentOrder
  filter_upwards [hspend,eventually_ge_atTop (32 : ℕ),
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ)),
    hord.eventually_ge_atTop (4/η)] with j hj hj32 hN hsize
  obtain ⟨v,hvb,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let Q := ⌊Real.exp (δ*N)⌋₊
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let P := ⌊Real.exp (ε*N)⌋₊
  let S := coreBand u N (dyadicPrimeCount j)
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  let Xs := radialTriples S N η
  let Zs := (radialIndices N).biUnion (fun M => smallTriples (S\Xs) M Q)
  let Hs := (radialIndices N).biUnion (fun M => smallFours S M Q)
  let Ys := radialSupply N h v
  let Fs := (radialIndices N).biUnion (fun M => smallPositiveFives S M Q L)
  let Gs := radialSixes S N P
  let B := balancedTriples S N η ∪ S.filter (fun n => Squarefree n ∧
    (n.primeFactors.card = 3 ∨ n.primeFactors.card = 4 ∨
          (n.primeFactors.card = 5 ∧ 0 < (SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u N) n).re)) ∧ ∃ p ∈ n.primeFactors, p ≤ Q) ∪ wholeSixes S P
  let D := B\(Xs ∪ Zs ∪ Hs ∪ Fs ∪ Gs)
  have hηN : 4 ≤ η*N := by
    have ht := (div_le_iff₀ hη).mp hsize
    dsimp [N]
    nlinarith
  have hnorm := hmissed j η δ ε y u hj32 hN hη hηN hδ.le hu.le hU
  change ‖(u : ℂ)^(N+1)*∑ n ∈ D, f n‖ ≤ _ at hnorm
  have hreal : u^(N+1)*(∑ n ∈ D, f n).re ≤ r^N*C+2*zetaMoebiusLogMajorantMass (1+1/262144)*
      Real.exp (-(N : ℝ)/1000000) := by
    have ht := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
    simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using ht
  have hBY : Disjoint B Ys := by
    apply Finset.disjoint_left.mpr
    intro n hnB hnY
    have hsupply := radial_supply_geometry (by omega : 2000 ≤ N) hh hhu hvb hnY
    rcases Finset.mem_union.mp hnB with hnB | hn6
    ·
      rcases Finset.mem_union.mp hnB with hbal | hhead
      · have hc := (Finset.mem_filter.mp hbal).2.2.1
        omega
      obtain ⟨_,_,_,p,hp,hpQ⟩ := Finset.mem_filter.mp hhead
      have hplog : Real.log p ≤ δ*N := by
        have ht := Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
          (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
        exact ht.trans (log_floor_exp_le (mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) N)))
      have hδN := mul_le_mul_of_nonneg_right hδu (Nat.cast_nonneg (α := ℝ) N)
      linarith [(hsupply.2 p hp),Nat.cast_nonneg (α := ℝ) N]
    · have hc := (Finset.mem_filter.mp hn6).2.2.1
      omega

  have hDsub : D ⊆ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs) := by
    intro n hn
    obtain ⟨hnB,hnnot⟩ := Finset.mem_sdiff.mp hn
    have hnS : n ∈ S := by
      rcases Finset.mem_union.mp hnB with hn | hn
      · rcases Finset.mem_union.mp hn with hn | hn <;> exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    have hnY : n ∉ Ys := fun h => Finset.disjoint_left.mp hBY hnB h
    refine Finset.mem_sdiff.mpr ⟨hnS,?_⟩
    intro h
    rcases Finset.mem_union.mp h with h | hg
    · rcases Finset.mem_union.mp h with h | hf
      · rcases Finset.mem_union.mp h with h | hy
        · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_left Fs h))
        · exact hnY hy
      · exact hnnot (Finset.mem_union_left Gs (Finset.mem_union_right _ hf))
    · exact hnnot (Finset.mem_union_right _ hg)
  have hset : (S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs))\D =
      S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B) := by
    exact sdiff_union_payment S Xs Zs Hs Ys Fs Gs B
  have hsum := Finset.sum_sdiff (f := f) hDsub
  rw [hset] at hsum
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re] at hre
  refine ⟨v,hvb,hY,?_⟩
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs ∪ B), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16)+_
  change _ ≤ u^(N+1)*((∑ n ∈ S\(Xs ∪ Zs ∪ Hs ∪ Ys ∪ Fs ∪ Gs), f n).re+
    min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+(∑ n ∈ Ys, f n).re/16) at hfloor
  rw [← hre] at hfloor
  nlinarith only [hfloor,hreal]


/-- A surviving six-prime label has EVERY prime logarithm above the
fixed positive fraction of the moving order. -/
theorem remaining_six_prime_log_gt {S E : Finset ℕ} {N n : ℕ} {ε : ℝ}
    (hn : n ∈ S\(E ∪ wholeSixes S ⌊Real.exp (ε*N)⌋₊)) (hs : Squarefree n)
    (hc : n.primeFactors.card = 6) : ∀ p ∈ n.primeFactors, ε*N < Real.log p := by
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  intro p hp
  by_contra h
  have hpQ : p ≤ ⌊Real.exp (ε*N)⌋₊ := by
    apply Nat.le_floor
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    simpa only [Real.exp_log hp0] using
      Real.exp_le_exp.mpr (le_of_not_gt h)
  exact hnnot (Finset.mem_union_right E
    (Finset.mem_filter.mpr ⟨hnS,hs,hc,p,hp,hpQ⟩))


/-- Every positive fixed exponential threshold eventually includes the
previous polynomial head. Its inclusion does not require a numerical
starting order or a new arithmetic assumption. -/
theorem eventually_polynomial_head_included {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, N^2 ≤ ⌊Real.exp (ε*N)⌋₊ := by
  have ht : Tendsto (fun N : ℕ => 2*Real.log N/(N : ℝ)) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
    simpa only [Function.comp_def,pow_one,one_mul,add_zero,mul_div_assoc,mul_zero] using h
  filter_upwards [ht.eventually_lt_const hε,eventually_ge_atTop (1 : ℕ)] with N h hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := (div_lt_iff₀ hn).mp h
  apply Nat.le_floor
  have he : Real.log (N^2 : ℕ) ≤ ε*N := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
    linarith
  simpa only [Real.exp_log (show (0 : ℝ) < (N^2 : ℕ) by positivity)] using Real.exp_le_exp.mpr he

end
end RiemannGaussian.ZetaRieszSixPrimeExponentialHead
