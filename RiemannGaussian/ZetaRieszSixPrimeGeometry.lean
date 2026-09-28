/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedSperner

/-!
# The reflected core halves the six-prime lower coefficient cost

Two disjoint surviving pairs contradict the reflected cutoff's being at
most one third of the total logarithm. The same exact signed divisor
window therefore has upper capacity three, rather than six. This improves
the original six-prime coefficient without changing a carrier or removing
any allocation, arithmetic support or phase.
-/

namespace RiemannGaussian.ZetaRieszSixPrimeGeometry
noncomputable section
open scoped BigOperators Classical
open Set MeasureTheory
open ZetaRieszSperner ZetaRieszSignedSperner ZetaSquarefreeRieszWindows

/-- A family of pairs on four coordinates containing no complementary
pair occupies at most three of the six possibilities. -/
theorem pair_family_card_le_three {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 4) (A : Finset (Finset ι))
    (hc : ∀ S ∈ A, S.card = 2) (hopp : ∀ S ∈ A, Sᶜ ∉ A) : A.card ≤ 3 := by
  let B := A.image (fun S => Sᶜ)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro S hS hB
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hB
    exact hopp T hT hS
  have hB : B.card = A.card := Finset.card_image_of_injective _ compl_injective
  have hsub : A ∪ B ⊆ (Finset.univ : Finset ι).powersetCard 2 := by
    intro S hS
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hc S hS
    · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
      rw [Finset.card_compl,hι,hc T hT]
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hB,Finset.card_powersetCard,
    Finset.card_univ,hι] at hh
  norm_num [Nat.choose] at hh
  omega

/-- At the one-third cutoff, a surviving pair's complementary pair
cannot survive. The two deleted primes are no larger than the others. -/
theorem window_pair_compl_notMem {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {a b v : ℝ} (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {S : Finset ι}
    (hc : S.card = 2) (hS : S ∈ subsetWindow w b v) :
    Sᶜ ∉ subsetWindow w b v := by
  intro hSc
  have hsum := Finset.sum_le_sum (s := S) (fun i _ => hw i)
  simp only [Finset.sum_const,nsmul_eq_mul,hc,Nat.cast_ofNat] at hsum
  have h₁ := (Finset.mem_filter.mp hS).2.2
  have h₂ := (Finset.mem_filter.mp hSc).2.2
  have he := Finset.sum_add_sum_compl S w
  linarith

/-- The complete cofactor cannot meet this reflected window either. -/
theorem univ_notMem_window {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 4) (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) :
    (Finset.univ : Finset ι) ∉ subsetWindow w b v := by
  intro h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hw i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hι,Nat.cast_ofNat] at hsum
  have hh := (Finset.mem_filter.mp h).2.2
  linarith

/-- The surviving even-rank windows have capacity three. This keeps the
unit boundary and excludes the full-cofactor boundary explicitly. -/
theorem even_window_card_le_three {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 4) (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) :
    (A.filter (fun S => S.card % 2 = 0)).card ≤ 3 := by
  have ha := (subsetWindow_antichain w hb hw v).subset hA
  by_cases he : (∅ : Finset ι) ∈ A
  · have hsub : A ⊆ {∅} := by
      intro S hS
      have hse : (∅ : Finset ι) = S := by
        by_contra hne
        exact ha he hS hne (Finset.empty_subset _)
      simp only [Finset.mem_singleton]
      exact hse.symm
    have hh := (Finset.card_le_card (Finset.filter_subset (fun S : Finset ι => S.card % 2 = 0) A)).trans
      (Finset.card_le_card hsub)
    simp only [Finset.card_singleton] at hh
    omega
  · apply pair_family_card_le_three hι
    · intro S hS
      have hs := Finset.mem_filter.mp hS
      have hcard : S.card ≤ 4 := hι ▸ S.card_le_univ
      have hzero : S.card ≠ 0 := by
        intro h
        exact he (Finset.card_eq_zero.mp h ▸ hs.1)
      have hfour : S.card ≠ 4 := by
        intro h
        have hSU : S = Finset.univ := S.card_eq_iff_eq_univ.mp (h.trans hι.symm)
        exact univ_notMem_window hι w hb hab hw ht (hSU ▸ hA hs.1)
      omega
    · intro S hS hSc
      have hs := Finset.mem_filter.mp hS
      have hs' := Finset.mem_filter.mp hSc
      have hcard : S.card ≤ 4 := hι ▸ S.card_le_univ
      have hzero : S.card ≠ 0 := by
        intro h
        exact he (Finset.card_eq_zero.mp h ▸ hs.1)
      have hfour : S.card ≠ 4 := by
        intro h
        have hSU : S = Finset.univ := S.card_eq_iff_eq_univ.mp (h.trans hι.symm)
        exact univ_notMem_window hι w hb hab hw ht (hSU ▸ hA hs.1)
      exact window_pair_compl_notMem w hab hw ht (by omega) (hA hs.1) (hA hs'.1)

/-- Negative-rank observations are retained until the signed inequality;
only the positive ranks spend the improved geometric capacity. -/
theorem signed_window_le_three {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 4) (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) :
    (∑ S ∈ A, (-1 : ℝ)^S.card) ≤ 3 := by
  have hterm (S : Finset ι) :
      (-1 : ℝ)^S.card ≤ if S.card % 2 = 0 then (1 : ℝ) else 0 := by
    rcases Nat.mod_two_eq_zero_or_one S.card with he | ho
    · rw [neg_one_pow_eq_pow_mod_two,he]
      norm_num
    · rw [neg_one_pow_eq_pow_mod_two,ho]
      norm_num
  have hs := Finset.sum_le_sum (fun S (_ : S ∈ A) => hterm S)
  rw [← Finset.sum_filter] at hs
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
  exact hs.trans (by exact_mod_cast even_window_card_le_three hι w hb hab hw ht hA)

/-- The actual four-prime cofactor window inherits the sharper upper
bound with its full Mobius sum and original strict endpoint convention. -/
theorem signedDivisorWindow_le_three {m : ℕ} (hm : Squarefree m)
    (hc : m.primeFactors.card = 4) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ p ∈ m.primeFactors, b ≤ Real.log p)
    (ht : 3*v ≤ a+b+Real.log m) : signedDivisorWindow b v m ≤ 3 := by
  let D := m.divisors.filter (fun d : ℕ => v-b < Real.log d ∧ Real.log d < v)
  have hi : Set.InjOn (divisorPrimeSet m) (D : Set ℕ) :=
    (divisorPrimeSet_injective hm).mono (Finset.filter_subset _ _)
  have hsub : D.image (divisorPrimeSet m) ⊆
      subsetWindow (fun p : m.primeFactors => Real.log (p.val : ℝ)) b v := by
    intro A hA
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hA
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rw [divisorPrimeSet_log_sum hm (Finset.mem_filter.mp hd).1]
    exact (Finset.mem_filter.mp hd).2
  have he : signedDivisorWindow b v m =
      ∑ S ∈ D.image (divisorPrimeSet m), (-1 : ℝ)^S.card := by
    rw [Finset.sum_image (fun d hd e he hh => hi hd he hh),signedDivisorWindow,
      ← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).1
    have hc' : (divisorPrimeSet m d).card = d.primeFactors.card := by
      rw [← divisorPrimeSet_map hm hd',Finset.card_map]
    rw [hc']
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount
      (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd'))
  rw [he]
  apply signed_window_le_three (by simpa only [Fintype.card_coe] using hc)
    (fun p : m.primeFactors => Real.log (p.val : ℝ)) hb hab
    (fun p => hw p.val p.property) _ hsub
  rw [Finset.sum_coe_sort m.primeFactors (fun p : ℕ => Real.log p),
    ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hm]
  exact ht

/-- The original two-prime window integral has upper capacity three
throughout the lower third of the total logarithm. -/
theorem riesz_six_lower_third_le {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card = 6) {D : ℝ} (hD : 3*D ≤ Real.log n) :
    VaughanLogAverage.riesz D n ≤ 3*Real.log n.minFac := by
  obtain ⟨p,q,m,hp,hq,hpq,he,hm,hpm,hqm,hpmin,hqmin,hcount⟩ :=
    exists_two_smallest_factorization hn (by omega)
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hpd : p ∣ n := he ▸ dvd_mul_right p (q*m)
  have hqd : q ∣ n := by
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_mul_right q m) p
  have hep : p = n.minFac := le_antisymm
    (hpmin n.minFac ((Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero))
    (Nat.minFac_le_of_dvd hp.two_le hpd)
  have hlogpq : Real.log p ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast hp.pos)
    (by exact_mod_cast hpmin q (hq.mem_primeFactors hqd hn.ne_zero))
  have hlog : Real.log n = Real.log p+Real.log q+Real.log m := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hm.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hm.ne_zero)]
    ring
  have hi := integrableOn_signedDivisorWindow D (Real.log p) (Real.log q) m
  have hw (s : ℝ) (hs : s ∈ Ioo 0 (Real.log p)) :
      signedDivisorWindow (Real.log q) (D-s) m ≤ 3 := by
    apply signedDivisorWindow_le_three hm (by omega)
      (Real.log_pos (by exact_mod_cast hq.one_lt)) hlogpq
      (fun r hr => Real.log_le_log (by exact_mod_cast hq.pos)
        (by exact_mod_cast hqmin r hr))
    linarith [hs.1]
  have hh := setIntegral_mono_on hi (integrableOn_const (hs := by simp)) measurableSet_Ioo hw
  rw [← riesz_two_primes_eq_window_integral D hp hq hpq hpm hqm,← he] at hh
  simp only [setIntegral_const,Real.volume_real_Ioo,sub_zero,
    max_eq_left (Real.log_natCast_nonneg p),smul_eq_mul] at hh
  rw [hep] at hh
  simpa only [mul_comm] using hh

/-- Reflection carries the cutoff improvement back to the literal core
coefficient. Its lower capacity is three, not the previous six. -/
theorem coefficient_six_lower {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : n.primeFactors.card = 6) (hcut : 2*Real.log n ≤ 3*L) :
    -(3*(Real.log n/L)*Real.log n.minFac) ≤
      (SquarefreeVaughanLogSource.coefficient L n).re := by
  by_cases hn : Squarefree n
  · have hn1 : n ≠ 1 := by intro h; simp [h] at hc
    have hnp : ¬ n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
    have hr := VaughanLogAverage.riesz_reflection L hn hn1 hnp
    rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hn,hc] at hr
    norm_num at hr
    have hh := riesz_six_lower_third_le hn hc
      (show 3*(Real.log n-L) ≤ Real.log n by linarith)
    rw [hr] at hh
    have hscale := mul_le_mul_of_nonneg_left hh
      (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    have hs : Squarefree n ∧ ¬ n.Prime := ⟨hn,hnp⟩
    simp only [SquarefreeVaughanLogSource.coefficient,if_pos hs,Complex.ofReal_re]
    have he : -Real.log n*VaughanLogAverage.riesz L n/L =
        -(Real.log n/L)*VaughanLogAverage.riesz L n := by ring
    rw [he]
    nlinarith only [hscale]
  · simp only [SquarefreeVaughanLogSource.coefficient,hn,false_and,if_false,Complex.zero_re]
    exact neg_nonpos.mpr (by positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac])

/-- The original six-prime interval is now [-3,4] in least-prime units
throughout the two-thirds-or-higher original cutoff range. -/
theorem coefficient_six_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : n.primeFactors.card = 6) (hcut : 2*Real.log n ≤ 3*L) :
    -(3*(Real.log n/L)*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        4*(Real.log n/L)*Real.log n.minFac := by
  refine ⟨coefficient_six_lower hL hc hcut,?_⟩
  by_cases hn : Squarefree n
  · exact (ZetaRieszSignedSperner.coefficient_six_bounds hL hn hc).2
  · simp only [SquarefreeVaughanLogSource.coefficient,hn,false_and,if_false,Complex.zero_re]
    positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac]

/-- Relative to the original mean-prime antichain allowance, the two
signed six-prime costs are one half and two thirds, including zero labels. -/
theorem coefficient_six_relative_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : n.primeFactors.card = 6) (hcut : 2*Real.log n ≤ 3*L) :
    -((1/2 : ℝ)*middleLayerAllowance L n) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        (2/3 : ℝ)*middleLayerAllowance L n := by
  refine ⟨?_,?_⟩
  · by_cases hn : Squarefree n
    · have hn1 : n ≠ 1 := by intro h; simp [h] at hc
      have hm := smallest_prime_log_le_mean hn (by omega) (Nat.minFac_prime hn1)
        (fun p hp => Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
          (Nat.dvd_of_mem_primeFactors hp))
      have hs : Squarefree n ∧ 2 ≤ n.primeFactors.card := ⟨hn,by omega⟩
      have he : (1/2 : ℝ)*middleLayerAllowance L n =
          3*(Real.log n/L)*(Real.log n/n.primeFactors.card) := by
        rw [middleLayerAllowance,if_pos hs,hc]
        norm_num [Nat.choose]
        ring
      rw [he]
      exact (neg_le_neg (mul_le_mul_of_nonneg_left hm
        (by positivity [Real.log_natCast_nonneg n]))).trans (coefficient_six_lower hL hc hcut)
    · simp [middleLayerAllowance,SquarefreeVaughanLogSource.coefficient,hn]
  · rw [← six_allowance_ratio L hc]
    exact (coefficient_bounds hL n).2

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- The six-prime floor keeps the original cosine's two orientations,
charging half the old coefficient allowance on its positive side. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  middleLayerAllowance L n *
    ((1/2 : ℝ)*max (Real.cos (y*Real.log n)) 0 +
      (2/3 : ℝ)*max (-Real.cos (y*Real.log n)) 0)

/-- The ceiling exchanges the two original phase orientations. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  middleLayerAllowance L n *
    ((2/3 : ℝ)*max (Real.cos (y*Real.log n)) 0 +
      (1/2 : ℝ)*max (-Real.cos (y*Real.log n)) 0)

/-- Both refined six-prime charges are nonnegative. -/
theorem costs_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ floorCost L y n ∧ 0 ≤ ceilingCost L y n := by
  have hM := middleLayerAllowance_nonneg hL n
  constructor <;> dsimp only [floorCost,ceilingCost] <;> positivity

/-- Every phase now saves at least one third of the old allowance;
the actual carrier still uses its full signed cosine. -/
theorem costs_le_two_thirds {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    floorCost L y n ≤ (2/3 : ℝ)*(middleLayerAllowance L n*|Real.cos (y*Real.log n)|) ∧
      ceilingCost L y n ≤ (2/3 : ℝ)*(middleLayerAllowance L n*|Real.cos (y*Real.log n)|) := by
  have hM := middleLayerAllowance_nonneg hL n
  by_cases hx : 0 ≤ Real.cos (y*Real.log n)
  · simp only [floorCost,ceilingCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),
      mul_zero,add_zero,abs_of_nonneg hx]
    have hp := mul_nonneg hM hx
    constructor <;> nlinarith only [hp]
  · have hx' := le_of_not_ge hx
    simp only [floorCost,ceilingCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),
      mul_zero,zero_add,abs_of_nonpos hx']
    have hp := mul_nonpos_of_nonneg_of_nonpos hM hx'
    constructor <;> nlinarith only [hp]

/-- The strengthened signed interval acts directly on the observed
six-prime atom, with its exact unassigned fraction and factorial order. -/
theorem residual_six_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : n.primeFactors.card = 6)
    (hcut : 2*Real.log n ≤ 3*L) :
    -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*ceilingCost L y n := by
  have hh := coefficient_six_relative_bounds hL hc hcut
  have hw := weight_nonneg A N n
  rw [re_residual_atom]
  suffices hs : -floorCost L y n ≤
        (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤
        ceilingCost L y n by
    exact ⟨by simpa only [mul_neg] using mul_le_mul_of_nonneg_left hs.1 hw,
      mul_le_mul_of_nonneg_left hs.2 hw⟩
  by_cases hx : 0 ≤ Real.cos (y*Real.log n)
  · have hlo := mul_le_mul_of_nonneg_right hh.1 hx
    have hhi := mul_le_mul_of_nonneg_right hh.2 hx
    simp only [floorCost,ceilingCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),
      mul_zero,add_zero]
    constructor <;> nlinarith only [hlo,hhi]
  · have hx' := le_of_not_ge hx
    have hlo := mul_le_mul_of_nonpos_right hh.2 hx'
    have hhi := mul_le_mul_of_nonpos_right hh.1 hx'
    simp only [floorCost,ceilingCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),
      mul_zero,zero_add]
    constructor <;> nlinarith only [hlo,hhi]

/-- All favorable selected observations remain on their original side
of the ledger; the scalar savings are not a second independent supply. -/
theorem residual_six_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : n.primeFactors.card = 6)
    (hcut : 2*Real.log n ≤ 3*L) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  dsimp only
  have hh := residual_six_bounds A hL y N hc hcut
  have hlo := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).1
  have hhi := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).2
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hlo]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hhi]

/-- The whole finite carrier receives both signed six-prime comparisons.
Every other prime count is left exactly in the same observed sum. -/
theorem sum_six_retained_bounds (S A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ)
    (hcut : ∀ n ∈ S, n.primeFactors.card = 6 → 2*Real.log n ≤ 3*L) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if n.primeFactors.card = 6 then
      max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        (∑ n ∈ S, f n).re ∧
      (∑ n ∈ S, f n).re ≤ ∑ n ∈ S, if n.primeFactors.card = 6 then
        min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re := by
  dsimp only
  rw [Complex.re_sum]
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_six_retained_bounds A hL y N hc (hcut n hn hc)).1
    · exact le_rfl
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_six_retained_bounds A hL y N hc (hcut n hn hc)).2
    · exact le_rfl

open Filter Topology
open ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- The actual moving length and unchanged core window eventually
supply the two-thirds cutoff uniformly in every label and count ceiling. -/
theorem eventually_core_cutoff_thirds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ K n : ℕ, n ∈ coreBand u N K →
      2*Real.log n ≤ 3*SquarefreeVaughanLogSource.length u N := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hL] with N hlow K n hn
  have hw := (Finset.mem_filter.mp hn).2.2
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Both source-normalized inequalities hold for every subset of the
original core, so they may be applied to an existing signed complement
without spending any earlier supply again. The other counts remain exact.
Neither independent numerical cofinal endgame bound is asserted here. -/
theorem eventually_core_subset_six_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if n.primeFactors.card = 6 then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
          ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
          u^(N+1)*(∑ n ∈ S, if n.primeFactors.card = 6 then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [eventually_core_cutoff_thirds hu hU] with N hcut K y S hS
  have hh := sum_six_retained_bounds S (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) y N (fun n hn _ => hcut K n (hS hn))
  have hlo := mul_le_mul_of_nonneg_left hh.1 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  have hhi := mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  dsimp only
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hlo hhi

end
end RiemannGaussian.ZetaRieszSixPrimeGeometry
