/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSharpPrimeWindows
import RiemannGaussian.ZetaRieszCardinalityChamber

/-!
# A signed five-prime supply retaining the pair cutoff costs

Reflection leaves only the unit, singleton, pair and triple divisor
channels when every prime is below the physical Riesz length. The pair
costs are subtracted before evaluating an explicit positive contribution
on the negative-cosine side. This is an inequality for the original atom,
not an absolute allowance or a new carrier.
-/

namespace RiemannGaussian.ZetaRieszFivePrimePairSupply
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszContinuumCascade ZetaRieszReflectedLinear ZetaRieszOneSidedArithmetic
open ZetaRieszJointAllocation ZetaRieszPrimeEndpoint

private theorem four_subset_inactive {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) (hc : S.card = 5) {L : ℝ}
    (hx : ∀ i ∈ S, x i ≤ L) {A : Finset ι} (hA : A ∈ S.powersetCard 4) :
    (∑ i ∈ S, x i)-L ≤ ∑ i ∈ A, x i := by
  obtain ⟨hAS,hAc⟩ := Finset.mem_powersetCard.mp hA
  have hdiff : (S\A).card = 1 := by rw [Finset.card_sdiff_of_subset hAS,hc,hAc]
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hdiff
  have hiS : i ∈ S := (Finset.mem_sdiff.mp (show i ∈ S\A by rw [hi]; simp)).1
  have he := Finset.sum_sdiff (f := x) hAS
  rw [hi,Finset.sum_singleton] at he
  linarith [hx i hiS]

/-- Every low-order channel is retained exactly. The fourth and fifth
subset levels vanish by physical saturation, not by an absolute estimate. -/
theorem reflected_kernel_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (x : ι → ℝ) (hc : S.card = 5) {L : ℝ}
    (hL : 0 ≤ L) (hLT : L ≤ ∑ i ∈ S, x i) (hx : ∀ i ∈ S, x i ≤ L) :
    kernel S x ((∑ i ∈ S, x i)-L) =
      4*L-3*(∑ i ∈ S, x i)-∑ i ∈ S, max 0 (x i-((∑ j ∈ S, x j)-L)) +
        (∑ A ∈ S.powersetCard 2, max 0 ((∑ i ∈ S, x i)-L-∑ i ∈ A, x i)) -
        (∑ A ∈ S.powersetCard 3, max 0 ((∑ i ∈ S, x i)-L-∑ i ∈ A, x i)) := by
  let D := (∑ i ∈ S, x i)-L
  have hD : 0 ≤ D := sub_nonneg.mpr hLT
  have hfour : (∑ A ∈ S.powersetCard 4, (-1 : ℝ)^A.card*max 0 (D-∑ i ∈ A, x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    rw [max_eq_left (sub_nonpos.mpr (four_subset_inactive S x hc hx hA)),mul_zero]
  have hfive : (∑ A ∈ S.powersetCard 5, (-1 : ℝ)^A.card*max 0 (D-∑ i ∈ A, x i)) = 0 := by
    rw [← hc,Finset.powersetCard_self,Finset.sum_singleton]
    rw [max_eq_left (by dsimp [D]; linarith : D-(∑ i ∈ S, x i) ≤ 0),mul_zero]
  have hsingle : (∑ A ∈ S.powersetCard 1, (-1 : ℝ)^A.card*max 0 (D-∑ i ∈ A, x i)) =
      -(∑ i ∈ S, max 0 (D-x i)) := by
    rw [Finset.powersetCard_one,Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk,Finset.card_singleton,Finset.sum_singleton,
      pow_one,neg_one_mul,Finset.sum_neg_distrib]
  have htwo : (∑ A ∈ S.powersetCard 2, (-1 : ℝ)^A.card*max 0 (D-∑ i ∈ A, x i)) =
      ∑ A ∈ S.powersetCard 2, max 0 (D-∑ i ∈ A, x i) := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [(Finset.mem_powersetCard.mp hA).2]
    norm_num
  have hthree : (∑ A ∈ S.powersetCard 3, (-1 : ℝ)^A.card*max 0 (D-∑ i ∈ A, x i)) =
      -(∑ A ∈ S.powersetCard 3, max 0 (D-∑ i ∈ A, x i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    rw [(Finset.mem_powersetCard.mp hA).2]
    norm_num
  have hsum : (∑ i ∈ S, max 0 (D-x i)) =
      5*D-(∑ i ∈ S, x i)+(∑ i ∈ S, max 0 (x i-D)) := by
    have he (i : ι) : max 0 (D-x i) = D-x i+max 0 (x i-D) := by
      rcases le_total (x i) D with h | h
      · rw [max_eq_right (by linarith),max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith),max_eq_right (by linarith)]; ring
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,hc]
    norm_num
  change kernel S x D = _
  rw [kernel,Finset.sum_powerset,hc]
  rw [show 5+1 = 6 from rfl]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [hfour,hfive,hsingle,htwo,hthree]
  simp only [Finset.powersetCard_zero,Finset.sum_singleton,Finset.card_empty,
    Finset.sum_empty,pow_zero,sub_zero,one_mul,max_eq_right hD]
  rw [hsum]
  dsimp [D]
  ring

/-- Exact five-prime arithmetic magnitude with both sides of the pair
balance retained. The triple hinges are favorable additional credit. -/
theorem neg_coefficient_eq_pair_balance_add_triples {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLT : L ≤ Real.log n) (hpL : ∀ p ∈ n.primeFactors, Real.log p ≤ L) :
    -(SquarefreeVaughanLogSource.coefficient L n).re =
      (Real.log n/L)*(3*Real.log n-4*L+
        (∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
        (∑ A ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ A, Real.log p))+
        (∑ A ∈ n.primeFactors.powersetCard 3, max 0 (Real.log n-L-∑ p ∈ A, Real.log p))) := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hsum := CoprimeEulerPhase.squarefree_log_eq_prime_sum hs
  have hker := reflected_kernel_eq n.primeFactors (fun p => Real.log p) hc hL.le
    (hsum ▸ hLT) hpL
  rw [← hsum,kernel_primeFactors hs] at hker
  have hreflection := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [moebius_eq_primeCount hs,hc] at hreflection
  norm_num at hreflection
  rw [hreflection] at hker
  have hR : VaughanLogAverage.riesz L n =
      3*Real.log n-4*L+(∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
        (∑ A ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ A, Real.log p))+
        (∑ A ∈ n.primeFactors.powersetCard 3, max 0 (Real.log n-L-∑ p ∈ A, Real.log p)) := by
    linarith
  simp only [SquarefreeVaughanLogSource.coefficient,
    if_pos (show Squarefree n ∧ ¬n.Prime from ⟨hs,hnp⟩),Complex.ofReal_re,hR]
  ring

/-- A lower bound for the favorable arithmetic magnitude of every
squarefree five-prime label below the physical length. Pair deficits are
kept explicitly; the omitted triple-cutoff term has a proved positive sign. -/
theorem neg_coefficient_ge_pair_balance {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLT : L ≤ Real.log n) (hpL : ∀ p ∈ n.primeFactors, Real.log p ≤ L) :
    (Real.log n/L)*(3*Real.log n-4*L+
      (∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
      (∑ A ∈ n.primeFactors.powersetCard 2,
        max 0 (Real.log n-L-∑ p ∈ A, Real.log p))) ≤
      -(SquarefreeVaughanLogSource.coefficient L n).re := by
  rw [neg_coefficient_eq_pair_balance_add_triples hs hc hL hLT hpL]
  have hscalar : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have htriple : 0 ≤ ∑ A ∈ n.primeFactors.powersetCard 3,
      max 0 (Real.log n-L-∑ p ∈ A, Real.log p) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  exact mul_le_mul_of_nonneg_left (by linarith) hscalar

/-- Independent positive credit for the actual five-prime atom on the
negative-cosine side. This keeps the pair-overlap cost, original allocation
and phase, and supplies an explicit quantity to the four/five comparison. -/
theorem re_atom_ge_pair_credit (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hs : Squarefree n) (hc : n.primeFactors.card = 5) {L y : ℝ} (hL : 0 < L)
    (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2)
    (hcos : Real.cos (y*Real.log n) ≤ 0) :
    weight A N n*(Real.log n/L)*max 0
      (3*Real.log n-4*L+(∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
        (∑ B ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ B, Real.log p)))*
      (-Real.cos (y*Real.log n)) ≤
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have ht : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hP : largestPrime n ∈ n.primeFactors := by
    have hn : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    rw [largestPrime,dif_pos hn]
    exact Finset.max'_mem _ _
  have hnonpos := ZetaRieszFivePrimeFloor.coefficient_five_nonpos hc hL hLlo hLhi
    (Or.inl (by linarith [hmax _ hP]))
  have hbal := neg_coefficient_ge_pair_balance hs hc hL (by linarith)
    (fun p hp => by linarith [hmax p hp])
  have hscalar : 0 ≤ Real.log n/L := div_nonneg ht hL.le
  have hb : (Real.log n/L)*max 0
      (3*Real.log n-4*L+(∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
        (∑ B ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ B, Real.log p))) ≤
      -(SquarefreeVaughanLogSource.coefficient L n).re := by
    rw [mul_max_of_nonneg _ _ hscalar,mul_zero]
    exact max_le (by linarith) hbal
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (weight_nonneg A N n)) (neg_nonneg.mpr hcos)
  rw [re_residual_atom]
  simpa only [mul_assoc,neg_mul,mul_neg,neg_neg] using hh

/-- The favorable fixed-count population can retain any prescribed
fraction of its raw positive credit. This is relative spending, never
a polynomial error multiplied by the absolute source envelope. -/
theorem eventually_unassigned_ge (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (n : ℕ), n.primeFactors.card ≤ k →
      (∀ p ∈ n.primeFactors, Real.log p ≤ (9/16 : ℝ)*Real.log n) →
        1-ε ≤ 1-boundedShare A N n := by
  have ht : Tendsto (fun N : ℕ => (k : ℝ)*Real.exp (-(N : ℝ)/1000)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const
      (by norm_num : (0 : ℝ) < 1000)
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
    simpa only [neg_div,Function.comp_def,mul_zero] using he.const_mul (k : ℝ)
  filter_upwards [ht.eventually_lt_const hε] with N hN A n hc hbal
  by_cases h : Squarefree n ∧ 1 < n ∧ ¬n.Prime
  · have hb := ZetaRieszParityOrderTail.share_small_of_selected_primes_interior A N h.1 h.2.1
      (fun p hp _ _ => hbal p hp)
    have hcard : (n.primeFactors.card : ℝ) ≤ k := by exact_mod_cast hc
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))
    rw [boundedShare,if_pos h]
    linarith
  · rw [boundedShare,if_neg h]
    linarith

/-- The explicit pair credit pays the literal old allocation with an
arbitrarily small relative loss, uniformly over every selected five-prime
label. Neither the phase nor the signed complement is replaced by a norm. -/
theorem eventually_re_atom_ge_raw_pair_credit {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℕ) (n : ℕ) (L y : ℝ),
      Squarefree n → n.primeFactors.card = 5 → 0 < L →
      2*Real.log n ≤ 3*L → 4*L ≤ 3*Real.log n →
      (∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2) → Real.cos (y*Real.log n) ≤ 0 →
      (1-ε)*amplitude N n*(Real.log n/L)*max 0
        (3*Real.log n-4*L+(∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
          (∑ B ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ B, Real.log p)))*
        (-Real.cos (y*Real.log n)) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  filter_upwards [eventually_unassigned_ge 5 hε] with N hN A n L y hs hc hL hLlo hLhi hmax hcos
  have hu := hN A n hc.le (fun p hp => by
    linarith [hmax p hp,Real.log_natCast_nonneg n])
  have hw : (1-ε)*amplitude N n ≤ weight A N n :=
    mul_le_mul_of_nonneg_right hu (ZetaRieszCosineCarrier.factorial_envelope_nonneg _ _)
  apply le_trans _ (re_atom_ge_pair_credit A N hs hc hL hLlo hLhi hmax hcos)
  apply mul_le_mul_of_nonneg_right _ (neg_nonneg.mpr hcos)
  apply mul_le_mul_of_nonneg_right _ (le_max_left _ _)
  exact mul_le_mul_of_nonneg_right hw (div_nonneg (Real.log_natCast_nonneg n) hL.le)

/-- Summed credit replaces only the selected favorable five-prime
population. Every other label stays in the same signed finite sum; no
part of a previously spent supply may be counted again through this rule. -/
theorem re_sum_ge_pair_credit (S D A : Finset ℕ) (N : ℕ) {L y : ℝ}
    (hDS : D ⊆ S) (hL : 0 < L)
    (hD : ∀ n ∈ D, Squarefree n ∧ n.primeFactors.card = 5 ∧
      2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n ∧
      (∀ p ∈ n.primeFactors, Real.log p ≤ Real.log n/2) ∧ Real.cos (y*Real.log n) ≤ 0) :
    (∑ n ∈ S\D, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re+
      (∑ n ∈ D, weight A N n*(Real.log n/L)*max 0
        (3*Real.log n-4*L+(∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)))-
          (∑ B ∈ n.primeFactors.powersetCard 2, max 0 (Real.log n-L-∑ p ∈ B, Real.log p)))*
        (-Real.cos (y*Real.log n))) ≤
      (∑ n ∈ S, residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have he := congrArg Complex.re (Finset.sum_sdiff
    (f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) hDS)
  rw [Complex.add_re] at he
  rw [← he]
  apply add_le_add le_rfl
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hs,hc,hlo,hhi,hm,hcos⟩ := hD n hn
  exact re_atom_ge_pair_credit A N hs hc hL hlo hhi hm hcos

/-- The cutoff-ratio interval used for the refined compensation test
contains the actual moving length throughout the original core. It is
eventual, retains the integer physical cutoff, and does not freeze T=2N. -/
theorem eventually_core_cutoff_ratio {u : ℝ} (hu : 1/2 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, (39/20 : ℝ)*N < T → T ≤ (203/100 : ℝ)*N →
      (693/1015 : ℝ) ≤ SquarefreeVaughanLogSource.length u N/T ∧
      SquarefreeVaughanLogSource.length u N/T ≤ 139/195 := by
  have hUr : ZetaRieszWideOwnerAudit.radiusCeiling < Real.exp (-(693/1000 : ℝ)) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])).mp
    have h := Real.log_le_sub_one_of_pos
      (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] :
        (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling)
    rw [Real.log_mul (by norm_num) (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])] at h
    dsimp [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    linarith [Real.log_two_gt_d9]
  have hlo := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 693/1000) (hU.trans_lt hUr)
  filter_upwards [hlo,eventually_ge_atTop (2 : ℕ)] with N hlow hN T hT hTu
  have hhi := ZetaRieszHeadOrders.length_le_two_log_two hu hN
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hT0 : 0 < T := by linarith
  constructor
  · apply (le_div_iff₀ hT0).mpr
    nlinarith
  · apply (div_le_iff₀ hT0).mpr
    nlinarith [Real.log_two_lt_d9]

end
end RiemannGaussian.ZetaRieszFivePrimePairSupply
