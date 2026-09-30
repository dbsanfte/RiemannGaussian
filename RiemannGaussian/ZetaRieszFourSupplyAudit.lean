/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixSignCoverFloor

set_option autoImplicit false

/-!
# Exact four-prime supply debit in the signed period floor

The whole five/six payment must not be copied to count four without its
supply correction. The original positive supply is itself rough, count
four, and nonzero in the negative arithmetic sign part. Its intersection
with the previously spent set therefore cannot be removed for free.
-/

noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszFourSupplyAudit
open ZetaRieszRadialCompensation ZetaRieszBandCompensation ZetaRieszStaggeredFloor
open ZetaRieszJointAllocation
open ZetaRieszRoughFivePeriodFloor (spent)

/-- Every literal supply label is a rough four-prime label with negative
arithmetic coefficient; its negative sign part is the complete real atom. -/
theorem radial_supply_sign_data (A : Finset ℕ) {N n : ℕ} {h L y : ℝ}
    (hN : 2000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hL0 : 0 < L) (hL : ∀ M ∈ radialIndices N,
      (271/200 : ℝ)*M ≤ L ∧ L ≤ (143/100 : ℝ)*M)
    (hn : n ∈ radialSupply N h w) :
    n.primeFactors.card = 4 ∧ (∀ p ∈ n.primeFactors, (N : ℝ)/5 < Real.log p) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re < 0 ∧
      signedPart 1 A L y N n = 0 ∧
      signedPart (-1) A L y N n =
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  obtain ⟨M,hM,hn⟩ := Finset.mem_biUnion.mp hn
  have hb := (Finset.mem_filter.mp hM).2
  have hNR : (2000 : ℝ) ≤ N := by exact_mod_cast hN
  have hwM : h+w M ≤ (M : ℝ)/1000 := by linarith [(hw M hM).2]
  obtain ⟨ijk,hijk,hn⟩ := Finset.mem_biUnion.mp hn
  obtain ⟨hi,hjk⟩ := Finset.mem_product.mp hijk
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hc := tuple_count hh hi hj hk (hw M hM).1 hwM hp
  have hrough : ∀ q ∈ (∏ a, p a).primeFactors, (N : ℝ)/5 < Real.log q := by
    intro q hq
    rw [tuple_primeFactors hh hi hj hk (hw M hM).1 hwM hp] at hq
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hq
    have hs := start_bounds hh hi hj hk (hw M hM).1 hwM a
    have ht := (tuple_bounds hp a).2.1
    linarith [hs.1,hb.1]
  have hneg : (SquarefreeVaughanLogSource.coefficient L (∏ a, p a)).re < 0 :=
    lt_of_le_of_lt (tuple_coefficient_le_wide hh hi hj hk (hw M hM).1 hwM
      hL0 (hL M hM).1 (hL M hM).2 hp) (by linarith [hb.1])
  have hz : signedPart 1 A L y N (∏ a, p a) = 0 := by
    simp only [signedPart,one_mul,max_eq_right hneg.le,mul_zero,zero_mul]
  have he := signedPart_add A L y N (∏ a, p a)
  rw [hz,zero_add] at he
  exact ⟨hc,hrough,hneg,hz,he⟩

/-- At least one rough spent supply label has a strictly positive negative
sign part. The opposite-head zero-intersection argument for count five
is therefore FALSE at count four for the same original supply. -/
theorem rough_spent_supply_nonzero (S A : Finset ℕ) {N Q P V R : ℕ}
    (η : ℝ) {h L y : ℝ} (hN : 2000 ≤ N) (hh : 0 < h) (hhu : h ≤ 1/20)
    (w : ℕ → ℝ) (hw : ∀ M ∈ radialIndices N, 0 ≤ w M ∧ w M ≤ 1/2)
    (hL0 : 0 < L) (hL : ∀ M ∈ radialIndices N,
      (271/200 : ℝ)*M ≤ L ∧ L ≤ (143/100 : ℝ)*M)
    (hQ : Real.log Q ≤ (N : ℝ)/128)
    (hY : 0 < (∑ n ∈ radialSupply N h w,
      residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re) :
    ∃ n ∈ radialSupply N h w, n ∈ spent S N Q P V R η h L w ∧
      n.primeFactors.card = 4 ∧ (∀ r ∈ n.primeFactors, Q < r) ∧
      0 < signedPart (-1) A L y N n := by
  have hsum : 0 < ∑ n ∈ radialSupply N h w, signedPart (-1) A L y N n := by
    rw [Complex.re_sum] at hY
    convert hY using 1
    apply Finset.sum_congr rfl
    intro n hn
    exact (radial_supply_sign_data (y := y) A hN hh hhu w hw hL0 hL hn).2.2.2.2
  have hex : ∃ n ∈ radialSupply N h w, 0 < signedPart (-1) A L y N n := by
    by_contra hn
    push Not at hn
    have hs := Finset.sum_nonpos (fun n (hnY : n ∈ radialSupply N h w) => hn n hnY)
    linarith only [hs,hsum]
  obtain ⟨n,hn,hpos⟩ := hex
  have hd := radial_supply_sign_data (y := y) A hN hh hhu w hw hL0 hL hn
  refine ⟨n,hn,?_,hd.1,?_,hpos⟩
  · simp only [spent,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hn))))
  · intro r hr
    by_contra hnot
    have hrQ : r ≤ Q := le_of_not_gt hnot
    have hl : Real.log (r : ℝ) ≤ Real.log (Q : ℝ) := Real.log_le_log
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).pos)
      (by exact_mod_cast hrQ)
    have hNR := Nat.cast_nonneg (α := ℝ) N
    linarith [hd.2.1 r hr]

/-- Joining the remaining count-four labels to the supply spends the exact
63/128 supply difference; the retained 65/128 is not an independent credit. -/
theorem joint_four_supply_refund (E Y : Finset ℕ) (f : ℕ → ℂ)
    (hdis : Disjoint E Y) :
    (∑ n ∈ E, f n).re+(65/128 : ℝ)*(∑ n ∈ Y, f n).re =
      (∑ n ∈ E ∪ Y, f n).re-(63/128 : ℝ)*(∑ n ∈ Y, f n).re := by
  rw [Finset.sum_union hdis,Complex.add_re]
  ring

/-- A floor on a completed four-prime cover leaves its full supply debit
explicit. This is a conditional signed inequality, not a payment of it. -/
theorem joint_four_floor_with_supply_debit (E Y : Finset ℕ) (f : ℕ → ℂ)
    (hdis : Disjoint E Y) {cost : ℝ}
    (hfloor : -cost ≤ (∑ n ∈ E ∪ Y, f n).re) :
    -cost-(63/128 : ℝ)*(∑ n ∈ Y, f n).re ≤
      (∑ n ∈ E, f n).re+(65/128 : ℝ)*(∑ n ∈ Y, f n).re := by
  rw [joint_four_supply_refund E Y f hdis]
  linarith only [hfloor]

end RiemannGaussian.ZetaRieszFourSupplyAudit
