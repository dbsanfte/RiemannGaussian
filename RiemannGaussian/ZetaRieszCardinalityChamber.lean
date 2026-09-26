/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszContinuumCascade
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact signed Riesz coefficients near cofactor-count thresholds

If every subset of a given cardinality is on the same side of the cutoff,
the complete signed kernel depends only on the total cofactor logarithm.
The incidence count is performed before any estimate. This applies to
unequal prime logarithms, not only a repeated equal-share boundary.

Concrete thirteen- and forty-nine-prime sectors have quantitative opposite
arithmetic coefficients. Their complete complex phases and factorial weights
are not estimated here. Neither population comparisons nor cancellation
between counts follows; the retained signed prime-sum bound remains open.
-/

namespace RiemannGaussian.ZetaRieszCardinalityChamber
noncomputable section
open scoped BigOperators
open Finset

/-- Every coordinate belongs to exactly `choose (card S-1) (j-1)` subsets. -/
theorem sum_subsets_sum {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    (∑ A ∈ S.powersetCard j, ∑ i ∈ A, x i) =
      ((S.card-1).choose (j-1) : ℝ)*(∑ i ∈ S, x i) := by
  have he (A : Finset ι) (hA : A ∈ S.powersetCard j) :
      (∑ i ∈ A, x i) = ∑ i ∈ S, if i ∈ A then x i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    exact (Finset.filter_mem_eq_inter.trans
      (Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hA).1)).symm
  rw [Finset.sum_congr rfl he, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc := Finset.card_filter_powersetCard_subset {i} S j
    (Finset.singleton_subset_iff.mpr hi) (by simpa using hj)
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
    congrArg (fun n : ℕ => (n : ℝ)*x i) hc

/-- The empty subset has no coordinate incidence. -/
def incidence (k j : ℕ) : ℕ := if j = 0 then 0 else (k-1).choose (j-1)

theorem sum_subsets_sum_all {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) (j : ℕ) :
    (∑ A ∈ S.powersetCard j, ∑ i ∈ A, x i) =
      (incidence S.card j : ℝ)*(∑ i ∈ S, x i) := by
  by_cases hj : j = 0
  · subst j
    simp [incidence]
  · simpa [incidence, hj] using sum_subsets_sum S x (by omega : 1 ≤ j)

/-- All active subset cardinalities, with the original alternating signs. -/
def chamberKernel (k m : ℕ) (s d : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), (-1 : ℝ)^j*((k.choose j : ℝ)*d-(incidence k j : ℝ)*s)

/-- A cardinality chamber is independent of redistribution of its coordinates.
No positivity or equality of the individual coordinates is assumed here. -/
theorem kernel_chamber {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) (d : ℝ) {m : ℕ} (hm : m ≤ S.card)
    (hlo : ∀ A ∈ S.powerset, A.card ≤ m → (∑ i ∈ A, x i) ≤ d)
    (hhi : ∀ A ∈ S.powerset, m < A.card → d ≤ ∑ i ∈ A, x i) :
    ZetaRieszContinuumCascade.kernel S x d = chamberKernel S.card m (∑ i ∈ S, x i) d := by
  rw [ZetaRieszContinuumCascade.kernel, Finset.sum_powerset]
  have he (j : ℕ) (hj : j ∈ Finset.range (S.card+1)) :
      (∑ A ∈ S.powersetCard j, (-1 : ℝ)^A.card*max 0 (d-∑ i ∈ A, x i)) =
      if j ≤ m then (-1 : ℝ)^j*((S.card.choose j : ℝ)*d-
        (incidence S.card j : ℝ)*(∑ i ∈ S, x i)) else 0 := by
    by_cases h : j ≤ m
    · rw [if_pos h]
      have hf (A : Finset ι) (hA : A ∈ S.powersetCard j) :
          (-1 : ℝ)^A.card*max 0 (d-∑ i ∈ A, x i) =
          (-1 : ℝ)^j*(d-∑ i ∈ A, x i) := by
        have ha := Finset.mem_powersetCard.mp hA
        rw [ha.2, max_eq_right (sub_nonneg.mpr (hlo A (Finset.mem_powerset.mpr ha.1) (ha.2 ▸ h)))]
      rw [Finset.sum_congr rfl hf, ← Finset.mul_sum, Finset.sum_sub_distrib,
        sum_subsets_sum_all]
      simp [Finset.sum_const, nsmul_eq_mul]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro A hA
      have ha := Finset.mem_powersetCard.mp hA
      rw [max_eq_left (sub_nonpos.mpr (hhi A (Finset.mem_powerset.mpr ha.1)
        (by omega))), mul_zero]
  rw [Finset.sum_congr rfl he]
  unfold chamberKernel
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The alternating binomial sums telescope exactly, including the unit subset. -/
theorem chamberKernel_eq (n m : ℕ) (s d : ℝ) :
    chamberKernel (n+2) (m+1) s d =
      (-1 : ℝ)^(m+1)*(((n+1).choose (m+1) : ℝ)*d-(n.choose m : ℝ)*s) := by
  induction m with
  | zero =>
      simp [chamberKernel, incidence, Finset.sum_range_succ]
      ring
  | succ m ih =>
      have h : chamberKernel (n+2) (m+2) s d = chamberKernel (n+2) (m+1) s d +
          (-1 : ℝ)^(m+2)*(((n+2).choose (m+2) : ℝ)*d-
            ((n+1).choose (m+1) : ℝ)*s) := by
        simp only [chamberKernel, Finset.sum_range_succ, incidence]
        simp
      rw [show m+1+1 = m+2 by omega, h, ih]
      have h₁ := Nat.choose_succ_succ (n+1) (m+1)
      have h₂ := Nat.choose_succ_succ n m
      rw [show (n+2).choose (m+2) = (n+1).choose (m+1)+(n+1).choose (m+2) from h₁,
        Nat.cast_add, show (n+1).choose (m+1) = n.choose m+n.choose (m+1) from h₂,
        Nat.cast_add]
      simp only [pow_succ]
      ring

theorem subset_sum_bounds {ι : Type*} (S A : Finset ι)
    (x : ι → ℝ) {r : ℝ} (hA : A ⊆ S) (hx : ∀ i ∈ S, r ≤ x i) :
    (A.card : ℝ)*r ≤ ∑ i ∈ A, x i ∧
      (∑ i ∈ A, x i) ≤ A.card*r+((∑ i ∈ S, x i)-S.card*r) := by
  constructor
  · simpa using Finset.sum_le_sum (fun i hi => hx i (hA hi))
  · have hh := Finset.sum_le_sum_of_subset_of_nonneg hA
      (f := fun i => x i-r) (fun i hi _ => sub_nonneg.mpr (hx i hi))
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hh
    linarith

/-- A lower coordinate bound and the total excess imply every subset test.
These are finite signed identities, not an asymptotic count-onset theorem. -/
theorem kernel_near_threshold {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) {r d : ℝ} {m : ℕ} (hm : m ≤ S.card) (hr : 0 ≤ r)
    (hx : ∀ i ∈ S, r ≤ x i)
    (hlo : m*r+((∑ i ∈ S, x i)-S.card*r) ≤ d) (hhi : d ≤ (m+1)*r) :
    ZetaRieszContinuumCascade.kernel S x d =
      chamberKernel S.card m (∑ i ∈ S, x i) d := by
  apply kernel_chamber S x d hm
  · intro A hA hcard
    have hb := (subset_sum_bounds S A x (Finset.mem_powerset.mp hA) hx).2
    have hc : (A.card : ℝ) ≤ m := by exact_mod_cast hcard
    nlinarith
  · intro A hA hcard
    have hb := (subset_sum_bounds S A x (Finset.mem_powerset.mp hA) hx).1
    have hc : (m+1 : ℝ) ≤ A.card := by exact_mod_cast hcard
    nlinarith

/-- Twelve unequal cofactor coordinates retain a negative response on an
open-width neighborhood of the upper factorial-face corner. -/
theorem upper_chamber {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) (hc : S.card = 12) {T P L : ℝ} (hT : 0 < T)
    (hs : ∑ i ∈ S, x i = T-P)
    (hP₀ : (21/40 : ℝ)*T ≤ P)
    (hL₀ : (693/1000 : ℝ)*T ≤ L) (hL₁ : L ≤ (347/500 : ℝ)*T)
    (hx : ∀ i ∈ S, (79/2000 : ℝ)*T ≤ x i) :
    ZetaRieszContinuumCascade.kernel S x (L-P) = 330*L-210*P-120*T ∧
      ZetaRieszContinuumCascade.kernel S x (L-P) ≤ -(123/100 : ℝ)*T := by
  have he := kernel_near_threshold S x (d := L-P) (m := 4) (r := (79/2000 : ℝ)*T)
    (by omega) (by positivity) hx (by rw [hs,hc]; norm_num; linarith)
    (by norm_num; linarith)
  have hid : ZetaRieszContinuumCascade.kernel S x (L-P) = 330*L-210*P-120*T := by
    rw [he,hc,hs,show (12 : ℕ) = 10+2 from rfl,show (4 : ℕ) = 3+1 from rfl,
      chamberKernel_eq]
    norm_num [Nat.choose]
    ring
  exact ⟨hid, by rw [hid]; linarith⟩

/-- Forty-eight unequal cofactor coordinates have a positive response.
The narrower ratio window stays below the seventeenth-subset hinge. -/
theorem lower_chamber {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) (hc : S.card = 48) {T P L : ℝ} (hT : 0 < T)
    (hs : ∑ i ∈ S, x i = T-P)
    (hP₀ : (21/40 : ℝ)*T ≤ P) (hP₁ : P ≤ (52501/100000 : ℝ)*T)
    (hL₀ : (6931/10000 : ℝ)*T ≤ L) (hL₁ : L ≤ (1733/2500 : ℝ)*T)
    (hx : ∀ i ∈ S, (1979/200000 : ℝ)*T ≤ x i) :
    ZetaRieszContinuumCascade.kernel S x (L-P) =
      (Nat.choose 47 16 : ℝ)*(L-P)-(Nat.choose 46 15 : ℝ)*(T-P) ∧
      (3/500 : ℝ)*(Nat.choose 47 16 : ℝ)*T ≤
        ZetaRieszContinuumCascade.kernel S x (L-P) := by
  have he := kernel_near_threshold S x (d := L-P) (m := 16) (r := (1979/200000 : ℝ)*T)
    (by omega) (by positivity) hx (by rw [hs,hc]; norm_num; linarith)
    (by norm_num; linarith)
  have hid : ZetaRieszContinuumCascade.kernel S x (L-P) =
      (Nat.choose 47 16 : ℝ)*(L-P)-(Nat.choose 46 15 : ℝ)*(T-P) := by
    rw [he,hc,hs,show (48 : ℕ) = 46+2 from rfl,show (16 : ℕ) = 15+1 from rfl,
      chamberKernel_eq]
    norm_num
  refine ⟨hid, ?_⟩
  rw [hid]
  norm_num [Nat.choose]
  linarith

/-- The same formula for the literal squarefree divisor sum. -/
theorem riesz_chamber {a : ℕ} (ha : Squarefree a) {m : ℕ}
    (hm : m ≤ a.primeFactors.card) {r D : ℝ} (hr : 0 ≤ r)
    (hp : ∀ p ∈ a.primeFactors, r ≤ Real.log p)
    (hlo : m*r+(Real.log a-a.primeFactors.card*r) ≤ D) (hhi : D ≤ (m+1)*r) :
    VaughanLogAverage.riesz D a = chamberKernel a.primeFactors.card m (Real.log a) D := by
  rw [← ZetaRieszContinuumCascade.kernel_primeFactors ha]
  have hs := CoprimeEulerPhase.squarefree_log_eq_prime_sum ha
  simpa only [← hs] using kernel_near_threshold _ _ hm hr hp
    (by simpa only [← hs] using hlo) hhi

theorem saturated_coefficient {P a : ℕ} (hP : P.Prime) (hs : Squarefree (P*a))
    (hc : 2 ≤ a.primeFactors.card) {L : ℝ} (hsat : Real.log a ≤ L) :
    SquarefreeVaughanLogSource.coefficient L (P*a) =
      ((Real.log (P*a : ℕ)/L * ZetaRieszContinuumCascade.kernel a.primeFactors
        (fun p => Real.log p) (L-Real.log P) : ℝ) : ℂ) := by
  have ha1 : a ≠ 1 := by intro he; simp [he] at hc
  have hnp : ¬a.Prime := by
    intro hp
    rw [hp.primeFactors, Finset.card_singleton] at hc
    omega
  exact ZetaRieszContinuumCascade.coefficient_saturated_prime hP
    (hP.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hs.of_mul_right
    ha1 hnp ⟨hs, Nat.not_prime_mul hP.ne_one ha1⟩ hsat

/-- An independent quantitative coefficient bound for actual squarefree
thirteen-prime labels. This does not sign their complex carrier atoms. -/
theorem thirteen_prime_coefficient {P a : ℕ} (hP : P.Prime) (hs : Squarefree (P*a))
    (hc : a.primeFactors.card = 12) {L : ℝ}
    (howner : (21/40 : ℝ)*Real.log (P*a : ℕ) ≤ Real.log P)
    (hL₀ : (693/1000 : ℝ)*Real.log (P*a : ℕ) ≤ L)
    (hL₁ : L ≤ (347/500 : ℝ)*Real.log (P*a : ℕ))
    (hx : ∀ p ∈ a.primeFactors, (79/2000 : ℝ)*Real.log (P*a : ℕ) ≤ Real.log p) :
    SquarefreeVaughanLogSource.coefficient L (P*a) =
      ((Real.log (P*a : ℕ)/L * (330*L-210*Real.log P-120*Real.log (P*a : ℕ)) : ℝ) : ℂ) ∧
      (SquarefreeVaughanLogSource.coefficient L (P*a)).re ≤
        -(123/100 : ℝ)*(Real.log (P*a : ℕ))^2/L := by
  have hT : 0 < Real.log (P*a : ℕ) := Real.log_pos (by
    exact_mod_cast hP.one_lt.trans_le (Nat.le_mul_of_pos_right _
      (Nat.pos_of_ne_zero hs.of_mul_right.ne_zero)))
  have hL : 0 < L := by linarith
  have hlog : Real.log (P*a : ℕ) = Real.log P+Real.log a := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hsum : ∑ p ∈ a.primeFactors, Real.log p = Real.log (P*a : ℕ)-Real.log P := by
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_right, hlog]
    ring
  have hk := upper_chamber _ _ hc hT hsum howner hL₀ hL₁ hx
  have he := saturated_coefficient hP hs (by omega) (L := L) (by linarith)
  constructor
  · rw [he, hk.1]
  · rw [he, Complex.ofReal_re]
    calc
      _ ≤ Real.log (P*a : ℕ)/L * (-(123/100 : ℝ)*Real.log (P*a : ℕ)) :=
        mul_le_mul_of_nonneg_left hk.2 (div_nonneg hT.le hL.le)
      _ = _ := by ring

/-- An opposing quantitative coefficient bound for actual squarefree
forty-nine-prime labels, with all geometric premises explicit. -/
theorem fortyNine_prime_coefficient {P a : ℕ} (hP : P.Prime) (hs : Squarefree (P*a))
    (hc : a.primeFactors.card = 48) {L : ℝ}
    (hP₀ : (21/40 : ℝ)*Real.log (P*a : ℕ) ≤ Real.log P)
    (hP₁ : Real.log P ≤ (52501/100000 : ℝ)*Real.log (P*a : ℕ))
    (hL₀ : (6931/10000 : ℝ)*Real.log (P*a : ℕ) ≤ L)
    (hL₁ : L ≤ (1733/2500 : ℝ)*Real.log (P*a : ℕ))
    (hx : ∀ p ∈ a.primeFactors, (1979/200000 : ℝ)*Real.log (P*a : ℕ) ≤ Real.log p) :
    (3/500 : ℝ)*(Nat.choose 47 16 : ℝ)*(Real.log (P*a : ℕ))^2/L ≤
      (SquarefreeVaughanLogSource.coefficient L (P*a)).re := by
  have hT : 0 < Real.log (P*a : ℕ) := Real.log_pos (by
    exact_mod_cast hP.one_lt.trans_le (Nat.le_mul_of_pos_right _
      (Nat.pos_of_ne_zero hs.of_mul_right.ne_zero)))
  have hL : 0 < L := by linarith
  have hlog : Real.log (P*a : ℕ) = Real.log P+Real.log a := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hsum : ∑ p ∈ a.primeFactors, Real.log p = Real.log (P*a : ℕ)-Real.log P := by
    rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_right, hlog]
    ring
  have hk := lower_chamber _ _ hc hT hsum hP₀ hP₁ hL₀ hL₁ hx
  rw [saturated_coefficient hP hs (by omega) (L := L) (by linarith), Complex.ofReal_re]
  calc
    _ = Real.log (P*a : ℕ)/L * ((3/500 : ℝ)*(Nat.choose 47 16 : ℝ)*Real.log (P*a : ℕ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk.2 (div_nonneg hT.le hL.le)

/-- The narrow lower-face ratio window contains every canonical limiting
source ratio in the restricted radius interval. No radial slice is frozen. -/
theorem source_ratio_in_chamber {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000) :
    6931/10000 < -2*u*Real.log u ∧ -2*u*Real.log u < 1733/2500 := by
  have hu0 : 0 < u := by linarith
  have ha : 0 < 2*u := by positivity
  have hlo := Real.log_le_sub_one_of_pos ha
  have hhi := Real.one_sub_inv_le_log_of_pos ha
  rw [Real.log_mul (by norm_num) hu0.ne'] at hlo hhi
  have hscaled := mul_le_mul_of_nonneg_left hhi ha.le
  have he : (2*u)*(1-(2*u)⁻¹) = 2*u-1 := by field_simp
  rw [he] at hscaled
  have h₂ := Real.log_two_gt_d9
  have h₃ := Real.log_two_lt_d9
  have hc : (2*u-1)*(2*u-10001/10000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  constructor <;> nlinarith

/-- The interior forty-four-cofactor model crosses zero at `149/215`.
Its earlier regression at `lambda=693/1000` therefore has the opposite
sign from the canonical source ratio. All subset signs are included. -/
theorem interior_kernel_transition {lam : ℝ} (hlo : 693/1000 ≤ lam) (hhi : lam ≤ 694/1000) :
    ZetaRieszContinuumCascade.kernel (Finset.univ : Finset (Fin 44))
      (fun _ => (1/100 : ℝ)) (lam-14/25) =
      (Nat.choose 43 13 : ℝ)*(149/215-lam) := by
  have he := kernel_near_threshold (Finset.univ : Finset (Fin 44))
    (fun _ => (1/100 : ℝ)) (d := lam-14/25) (m := 13) (r := 1/100)
    (by norm_num) (by norm_num) (by simp)
    (by norm_num; linarith) (by norm_num; linarith)
  rw [he]
  norm_num only [Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
  rw [show (44 : ℕ) = 42+2 from rfl, show (13 : ℕ) = 12+1 from rfl, chamberKernel_eq]
  norm_num [Nat.choose]
  ring

/-- At the canonical limiting source ratio the interior model is negative,
not the positive value at the coarser rational regression `693/1000`.
This does not infer a sign for the literal integrated carrier. -/
theorem interior_kernel_source_negative {u : ℝ} (hu : 1/2 ≤ u) (hU : u ≤ 10001/20000) :
    ZetaRieszContinuumCascade.kernel (Finset.univ : Finset (Fin 44))
      (fun _ => (1/100 : ℝ)) (-2*u*Real.log u-14/25) < 0 := by
  have h := source_ratio_in_chamber hu hU
  rw [interior_kernel_transition (by linarith : 693/1000 ≤ -2*u*Real.log u)
    (by linarith : -2*u*Real.log u ≤ 694/1000)]
  apply mul_neg_of_pos_of_neg
  · norm_num [Nat.choose]
  · linarith

end
end RiemannGaussian.ZetaRieszCardinalityChamber
