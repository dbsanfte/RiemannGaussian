/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSevenPrimeHead
import RiemannGaussian.ZetaRieszLogCountTail

/-!
# The same count-tail budget also pays an exponential seven-prime head

Both signed comparisons preserve all earlier radial charges and the old
one-sixty-fourth reserve. Half of the count-tail spending now covers a
positive exponential seven-prime head. All omitted radial boundary labels
receive the existing geometric bound. The interior rest is still signed.
-/

namespace RiemannGaussian.ZetaRieszSevenCountTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic
open ZetaRieszRadialCompensation ZetaRieszTriplePrime
open ZetaRieszBandCompensation ZetaRieszSmallPrimeCompensation ZetaRieszFourPrimeHead
open ZetaRieszFivePositiveHead ZetaRieszPrimeCountFrequency ZetaRieszParityPacket
open ZetaRieszFiveNegativeHead ZetaRieszLogCountBudget ZetaRieszSevenPrimeHead

/-- The enlarged tail subset on one of the original disjoint radial slabs. -/
def slabTail (S : Finset ℕ) (N R M : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ 2*(M : ℝ) ≤ Real.log n ∧
    Real.log n < 2*(M : ℝ)+2 ∧ tailCondition N R n)

/-- Only original integer labels are selected; no prime completion is made. -/
def radialTail (S : Finset ℕ) (N R : ℕ) : Finset ℕ :=
  (radialIndices N).biUnion (slabTail S N R)

/-- Every original enlarged-tail label, including both radial boundaries. -/
def wholeTail (S : Finset ℕ) (N R : ℕ) : Finset ℕ :=
  S.filter (fun n => Squarefree n ∧ tailCondition N R n)

/-- Half-open radial slabs count each enlarged-tail label once. -/
theorem slabTail_disjoint (S : Finset ℕ) (N R : ℕ) :
    Pairwise (fun M M' : ℕ => Disjoint (slabTail S N R M) (slabTail S N R M')) := by
  intro M M' hne
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  have hb := (Finset.mem_filter.mp hn).2
  have hb' := (Finset.mem_filter.mp hn').2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hr : (M : ℝ)+1 ≤ M' := by exact_mod_cast hlt
    linarith [hb.2.2.1,hb'.2.1]
  · have hr : (M' : ℝ)+1 ≤ M := by exact_mod_cast hlt
    linarith [hb'.2.2.1,hb.2.1]

private theorem log_floor_exp_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (⌊Real.exp x⌋₊ : ℕ) ≤ x := by
  by_cases hz : ⌊Real.exp x⌋₊ = 0
  · simpa only [hz,Nat.cast_zero,Real.log_zero] using hx
  have hp : (0 : ℝ) < (⌊Real.exp x⌋₊ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have h := Real.log_le_log hp (Nat.floor_le (Real.exp_nonneg x))
  simpa only [Real.log_exp] using h


/-- The original core floor comparison now also pays every logarithmically
high prime count and the seven-prime head on the radial union, keeping all old head payments. -/
theorem eventually_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧
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
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hpay⟩ := ZetaRieszSevenPrimeHead.eventually_joint_slabs_floor hy
  refine ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,?_⟩
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
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < (∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ smallHeads S M P V L, f n‖ ≤ (3/32 : ℝ)*(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTail S N R M, f n‖ ≤ (1/64 : ℝ)*(∑ n ∈ supply M h v, f n).re := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩ := hpay M Q P V R S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallHeads S M P V L) (slabTail S N R M) A L
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
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
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
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change _ ≤ ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- The original core ceiling comparison now also pays every logarithmically
high prime count and the seven-prime head on the radial union, keeping all old head payments. -/
theorem eventually_core_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧
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
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) := by
  obtain ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hpay⟩ := ZetaRieszSevenPrimeHead.eventually_joint_slabs_ceiling hy
  refine ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,?_⟩
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
      0 ≤ v ∧ v ≤ 1/2 ∧ 0 < -(∑ n ∈ supply M h v, f n).re ∧
      ‖∑ n ∈ slabTriples S M η, f n‖ ≤ (1/2 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallTriples (S\Xs) M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallFours S M Q, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallPositiveFives S M Q L, f n‖ ≤ (1/8 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ smallHeads S M P V L, f n‖ ≤ (3/32 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) ∧
      ‖∑ n ∈ slabTail S N R M, f n‖ ≤ (1/64 : ℝ)*(-(∑ n ∈ supply M h v, f n).re) := by
    intro M
    by_cases hM : M ∈ radialIndices N
    · obtain ⟨v,hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩ := hpay M Q P V R S (S\Xs) (smallFours S M Q) (smallPositiveFives S M Q L) (smallHeads S M P V L) (slabTail S N R M) A L
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
      exact ⟨v,fun _ => ⟨hv,hvu,hY,hX,hZ,hH,hF,hG,hT⟩⟩
    · exact ⟨0,fun h => False.elim (hM h)⟩
  choose v hv using hex
  have hvb : ∀ M ∈ radialIndices N, 0 ≤ v M ∧ v M ≤ 1/2 :=
    fun M hM => ⟨(hv M hM).1,(hv M hM).2.1⟩
  let Ts := radialTail S N R
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
    (fun _ _ _ _ hne => smallHeads_disjoint S P V L hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.2.1)
  simp only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] at hXpay hZpay hHpay hFpay hGpay
  have hTpay := norm_radial_payment (f := fun n => -f n)
    (fun _ _ _ _ hne => slabTail_disjoint S N R hne) hhu hvb (fun M hM => by
      simpa only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] using (hv M hM).2.2.2.2.2.2.2.2)
  simp only [Finset.sum_neg_distrib,norm_neg,Complex.neg_re] at hTpay
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
  have hfloor := ZetaRieszLogCountBudget.re_sum_le_joint_spending f (Finset.union_subset (Finset.union_subset (Finset.union_subset hsuball hFsub) hGsub) hTsub) hXZ
    (hdisj Xs Hs hX3 hH4) (hdisj Zs Hs hZ3 hH4)
    (hdisj Xs Ys hX3 hY4) (hdisj Zs Ys hZ3 hY4) hHY hFdisj hGdisj hTdisj hXpay hZpay hHpay hFpay hGpay hTpay
  refine ⟨v,hvb,hY,?_⟩
  have hnorm := mul_le_mul_of_nonneg_left hfloor (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  change ((u : ℂ)^(N+1)*(∑ n ∈ S, f n)).re ≤ _
  rw [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact hnorm

/-- Every interior enlarged-tail label belongs to the paid radial union. -/
theorem mem_radialTail_of_geometry {S : Finset ℕ} {N R n : ℕ}
    (hN : 4000 ≤ N) (hnS : n ∈ S) (hs : Squarefree n)
    (hlo : (244/125 : ℝ)*N < Real.log n) (hhi : Real.log n ≤ (2029/1000 : ℝ)*N)
    (hsmall : tailCondition N R n) : n ∈ radialTail S N R := by
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
    ⟨hnS,hs,by linarith,by linarith,hsmall⟩⟩


open LogarithmicDeviation ZetaArithmeticDeviationBounds

/-- Both omitted radial boundaries of the enlarged tail have a source-scale
geometric bound, independently of height, selection and all allocations. -/
theorem exists_missed_tail_bound :
    ∃ r C : ℝ, 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ (N R : ℕ) (S A : Finset ℕ) (y u : ℝ),
        4000 ≤ N → 0 ≤ u → u ≤ ZetaRieszWideOwnerAudit.radiusCeiling →
        ‖(u : ℂ)^(N+1)*∑ n ∈ wholeTail S N R\radialTail S N R,
          residualCoefficient A (SquarefreeVaughanLogSource.length u N) N n*
            zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤ r^N*C := by
  obtain ⟨r,C,hr,hr1,hC,h⟩ := exists_uniform_deviation_bound (1 : Polynomial ℂ)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    (by norm_num : (0 : ℝ) < 244/125) (by norm_num) (by norm_num : (2 : ℝ) < 2029/1000)
    radial_edge_costs.1 radial_edge_costs.2
  refine ⟨r,C,hr,hr1,hC,?_⟩
  intro N R S A y u hN hu hU
  let D := wholeTail S N R\radialTail S N R
  have he : deviationBand D (244/125) (2029/1000) N = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hnD,hlo,hhi⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnB,hnT⟩ := Finset.mem_sdiff.mp hnD
    obtain ⟨hnS,hs,hc⟩ := Finset.mem_filter.mp hnB
    exact hnT (mem_radialTail_of_geometry hN hnS hs hlo hhi hc)
  have hb := h N D (residualCoefficient A (SquarefreeVaughanLogSource.length u N) N)
    (fun n _ => norm_residualCoefficient_le A (SquarefreeVaughanLogSource.length_pos u N) N n)
    y u hu hU
  simpa only [he,Finset.sum_empty,sub_zero,zetaPrimeLogKernel,
    SquarefreeEulerQuadratic.primeFilterKernel_one] using hb

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
theorem eventually_core_full_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
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
          u^(N+1)*(W.re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
            max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤
              ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hspend⟩ := eventually_core_floor hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_missed_tail_bound
  refine ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,?_⟩
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hN
  obtain ⟨v,hvb,hY,hbase⟩ := hj
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
  refine ⟨v,hvb,hY,?_⟩
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts ∪ B), f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)-r^N*C ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re
  change u^(N+1)*((∑ n ∈ S\(E ∪ Ts), f n).re+max (∑ n ∈ Xs, f n).re 0+max (∑ n ∈ Zs, f n).re 0+
    max (∑ n ∈ Hs, f n).re 0+max (∑ n ∈ Fs, f n).re 0+
    max (∑ n ∈ Gs, f n).re 0+max (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) ≤ ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re at hbase
  rw [← hre] at hbase
  nlinarith only [hbase,hlo]

/-- The enlarged count tail, including both radial edges, is paid in the
ceiling direction. Every earlier radial payment and its signed rest remain. -/
theorem eventually_core_full_ceiling {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h δ ε ζ θ r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 < δ ∧ δ ≤ 1/128 ∧ 0 < ε ∧ ε ≤ 1/128 ∧ 0 < ζ ∧ ζ ≤ 1/128 ∧ 0 < θ ∧ θ ≤ 1/128 ∧ 0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
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
        0 < -(∑ n ∈ Ys, f n).re ∧
          ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤
            u^(N+1)*(W.re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
              min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)+r^N*C := by
  obtain ⟨η,h,δ,ε,ζ,θ,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hspend⟩ := eventually_core_ceiling hu hU hy
  obtain ⟨r,C,hr,hr1,hC,hmissed⟩ := exists_missed_tail_bound
  refine ⟨η,h,δ,ε,ζ,θ,r,C,hη,hηu,hh,hhu,hδ,hδu,hε,hεu,hζ,hζu,hθ,hθu,hr,hr1,hC,?_⟩
  filter_upwards [hspend,tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (4000 : ℕ))]
    with j hj hN
  obtain ⟨v,hvb,hY,hbase⟩ := hj
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
  refine ⟨v,hvb,hY,?_⟩
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤ u^(N+1)*((∑ n ∈ S\(E ∪ Ts ∪ B), f n).re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+
    min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64)+r^N*C
  change ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re ≤ u^(N+1)*((∑ n ∈ S\(E ∪ Ts), f n).re+min (∑ n ∈ Xs, f n).re 0+min (∑ n ∈ Zs, f n).re 0+
    min (∑ n ∈ Hs, f n).re 0+min (∑ n ∈ Fs, f n).re 0+
    min (∑ n ∈ Gs, f n).re 0+min (∑ n ∈ Ts, f n).re 0+(∑ n ∈ Ys, f n).re/64) at hbase
  rw [← hre] at hbase
  nlinarith only [hbase,hhi]


/-- Every squarefree label remaining after the full tail payment has
strictly fewer than the explicit logarithmic number of prime factors. -/
theorem remaining_count_lt {S E : Finset ℕ} {N R n : ℕ}
    (hn : n ∈ S\(E ∪ wholeTail S N R)) (hs : Squarefree n) :
    n.primeFactors.card < countThreshold N := by
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  by_contra! h
  exact hnnot (Finset.mem_union_right E (Finset.mem_filter.mpr ⟨hnS,hs,Or.inl h⟩))

/-- Every unpaid seven-prime label lies beyond the entire fixed
exponential head, including the original clipped radial boundaries. -/
theorem remaining_seven_log_gt {S E : Finset ℕ} {N n : ℕ} {θ : ℝ}
    (hn : n ∈ S\(E ∪ wholeTail S N ⌊Real.exp (θ*N)⌋₊))
    (hs : Squarefree n) (hc : n.primeFactors.card = 7) :
    ∀ p ∈ n.primeFactors, θ*N < Real.log p := by
  intro p hp
  obtain ⟨hnS,hnnot⟩ := Finset.mem_sdiff.mp hn
  by_contra! hlog
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hple : p ≤ ⌊Real.exp (θ*N)⌋₊ := Nat.le_floor (by
    have hh := Real.exp_le_exp.mpr hlog
    simpa only [Real.exp_log hpR] using hh)
  exact hnnot (Finset.mem_union_right E (Finset.mem_filter.mpr
    ⟨hnS,hs,Or.inr ⟨hc,p,hp,hple⟩⟩))

end
end RiemannGaussian.ZetaRieszSevenCountTail
