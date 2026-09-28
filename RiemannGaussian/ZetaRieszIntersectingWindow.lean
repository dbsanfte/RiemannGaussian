/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszComplementWindow
import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-!
# Intersecting complements reduce the odd-count signed costs

Two subsets in the reflected divisor window cannot cover the remaining
prime universe when one has at least two elements. Thus the complements
of an upper-rank layer are intersecting. Erdős--Ko--Rado bounds that layer;
the exact LYM budget then bounds its entire parity. The estimates apply
to the original Riesz coefficient and retain its observed complex phase.
-/

namespace RiemannGaussian.ZetaRieszIntersectingWindow
noncomputable section
open scoped BigOperators Classical
open Set MeasureTheory
open ZetaRieszSperner ZetaRieszSignedSperner ZetaSquarefreeRieszWindows

/-- Two surviving window subsets cannot cover the prime universe.
The strict upper endpoint supplies the contradiction, without any
assumption that the subsets are complements or have equal size. -/
theorem window_union_ne_univ {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {a b v : ℝ} (hb : 0 ≤ b) (hab : a ≤ b)
    (hw : ∀ i, b ≤ w i) (ht : 3*v ≤ a+b+∑ i, w i)
    {S T : Finset ι} (hc : 2 ≤ S.card)
    (hS : S ∈ subsetWindow w b v) (hT : T ∈ subsetWindow w b v) :
    S ∪ T ≠ Finset.univ := by
  intro he
  have hsum := Finset.sum_le_sum (s := S) (fun i _ => hw i)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hc' : (2 : ℝ) ≤ S.card := by exact_mod_cast hc
  have hu : (∑ i ∈ S ∪ T, w i) ≤ (∑ i ∈ S, w i)+(∑ i ∈ T, w i) := by
    rw [← Finset.sum_union_inter]
    have hpos : 0 ≤ ∑ i ∈ S ∩ T, w i :=
      Finset.sum_nonneg (fun i _ => hb.trans (hw i))
    linarith
  rw [he] at hu
  have h₁ := (Finset.mem_filter.mp hS).2.2
  have h₂ := (Finset.mem_filter.mp hT).2.2
  nlinarith [mul_le_mul_of_nonneg_right hc' hb]

/-- The checked Erdős--Ko--Rado theorem transported from `Fin n` to
an arbitrary finite prime universe. -/
theorem intersecting_layer_card_le {ι : Type*} [Fintype ι]
    (A : Finset (Finset ι)) {r : ℕ}
    (hi : (A : Set (Finset ι)).Intersecting)
    (hc : ∀ S ∈ A, S.card = r) (hr : r ≤ Fintype.card ι/2) :
    A.card ≤ (Fintype.card ι-1).choose (r-1) := by
  let e := (Fintype.equivFin ι).toEmbedding
  let B := A.image (fun S => S.map e)
  have hB : B.card = A.card := Finset.card_image_of_injective _ (Finset.map_injective e)
  have hiB : (B : Set (Finset (Fin (Fintype.card ι)))).Intersecting := by
    intro S hS T hT hd
    obtain ⟨S,hSA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨T,hTA,rfl⟩ := Finset.mem_image.mp hT
    exact hi hSA hTA ((Finset.disjoint_map e).mp hd)
  have hcB : (B : Set (Finset (Fin (Fintype.card ι)))).Sized r := by
    intro S hS
    obtain ⟨S,hSA,rfl⟩ := Finset.mem_image.mp hS
    simpa using hc S hSA
  rw [← hB]
  exact Finset.erdos_ko_rado hiB hcB hr

/-- A high-rank layer in the actual divisor window has intersecting
complements. The resulting quota is sharper than half the layer when
the original rank is strictly above half the prime count. -/
theorem window_layer_card_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {a b v : ℝ} (hb : 0 ≤ b) (hab : a ≤ b)
    (hw : ∀ i, b ≤ w i) (ht : 3*v ≤ a+b+∑ i, w i)
    (A : Finset (Finset ι)) (hA : A ⊆ subsetWindow w b v) {j : ℕ}
    (hj : 2 ≤ j) (hc : ∀ S ∈ A, S.card = j)
    (hr : Fintype.card ι-j ≤ Fintype.card ι/2) :
    A.card ≤ (Fintype.card ι-1).choose (Fintype.card ι-j-1) := by
  let B := A.image (fun S => Sᶜ)
  have hB : B.card = A.card := Finset.card_image_of_injective _ compl_injective
  have hi : (B : Set (Finset ι)).Intersecting := by
    intro S hS T hT hd
    obtain ⟨S,hSA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨T,hTA,rfl⟩ := Finset.mem_image.mp hT
    apply window_union_ne_univ w hb hab hw ht (by rw [hc S hSA]; exact hj) (hA hSA) (hA hTA)
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hn
    have hn' := Finset.notMem_union.mp hn
    exact Finset.disjoint_left.mp hd (Finset.mem_compl.mpr hn'.1) (Finset.mem_compl.mpr hn'.2)
  have hsize : ∀ S ∈ B, S.card = Fintype.card ι-j := by
    intro S hS
    obtain ⟨S,hSA,rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.card_compl,hc S hSA]
  rw [← hB]
  exact intersecting_layer_card_le B hi hsize hr

/-- The remaining largest binomial layer of a parity after one rank
has received an arithmetic quota. -/
def offRankCapacity (k b j : ℕ) : ℕ :=
  ((Finset.range (k+1)).filter (fun i => i % 2 = b ∧ i ≠ j)).sup (fun i => k.choose i)

/-- A quota on a largest binomial layer consumes the same LYM budget as
all other ranks. This is a joint bound, not a sum of unrelated maxima. -/
theorem antichain_quota_bound {ι : Type*} [Fintype ι] {b j : ℕ}
    {A : Finset (Finset ι)}
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι)))
    (hj : j ≤ Fintype.card ι)
    (hmax : offRankCapacity (Fintype.card ι) b j ≤ (Fintype.card ι).choose j)
    {Q : ℝ} (hquota : ((A.filter (fun S => S.card % 2 = b ∧ S.card = j)).card : ℝ) ≤ Q) :
    ((A.filter (fun S => S.card % 2 = b)).card : ℝ) ≤
      (offRankCapacity (Fintype.card ι) b j : ℝ)+
        (1-(offRankCapacity (Fintype.card ι) b j : ℝ)/((Fintype.card ι).choose j))*Q := by
  let k := Fintype.card ι
  let F := A.filter (fun S => S.card % 2 = b)
  let C := ((k.choose j : ℕ) : ℝ)
  let B := (offRankCapacity k b j : ℝ)
  have hC : 0 < C := by
    dsimp only [C,k]
    exact_mod_cast Nat.choose_pos hj
  have hB : 0 ≤ B := by positivity
  have hBC : B ≤ C := by
    dsimp only [B,C,k]
    exact_mod_cast hmax
  have hlym : (∑ S ∈ F, ((k.choose S.card : ℕ) : ℝ)⁻¹) ≤ 1 :=
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
      (hA.subset (Finset.filter_subset _ _))
  have hterm (S : Finset ι) (hS : S ∈ F) :
      (1 : ℝ) ≤ B*((k.choose S.card : ℕ) : ℝ)⁻¹+
        (if S.card = j then 1-B/C else 0) := by
    by_cases hm : S.card = j
    · rw [if_pos hm,hm]
      change 1 ≤ B*C⁻¹+(1-B/C)
      simp only [div_eq_mul_inv]
      linarith
    · rw [if_neg hm,add_zero]
      have hpos : (0 : ℝ) < k.choose S.card := by exact_mod_cast Nat.choose_pos S.card_le_univ
      have hle : k.choose S.card ≤ offRankCapacity k b j :=
        Finset.le_sup (f := fun i => k.choose i)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := S.card_le_univ; dsimp [k]; omega),
            (Finset.mem_filter.mp hS).2,hm⟩)
      rw [← div_eq_mul_inv,le_div_iff₀ hpos,one_mul]
      dsimp only [B]
      exact_mod_cast hle
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have he : F.filter (fun S => S.card = j) =
      A.filter (fun S => S.card % 2 = b ∧ S.card = j) := by simp [F,Finset.filter_filter]
  rw [he] at hs
  have hL := mul_le_mul_of_nonneg_left hlym hB
  have hcoef : 0 ≤ 1-B/C := sub_nonneg.mpr ((div_le_one hC).mpr hBC)
  have hQ := mul_le_mul_of_nonneg_right hquota hcoef
  dsimp only [B,C,k,F] at *
  nlinarith only [hs,hL,hQ]

/-- Both central binomial layers have the same size, including odd
prime universes where the upper layer is strictly above half. -/
theorem upper_middle_choose (k : ℕ) : k.choose ((k+1)/2) = k.choose (k/2) :=
  Nat.choose_symm_of_eq_add (by omega)

/-- Singletons consume coordinates that no higher member of an
antichain can use. For five coordinates this combines with the triple
quota four to give a sharp bound of five across both odd layers. -/
theorem five_coordinate_odd_card_le {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 5) (A : Finset (Finset ι))
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι)))
    (hrank : ∀ S ∈ A, S.card = 1 ∨ S.card = 3)
    (hquota : (A.filter (fun S => S.card = 3)).card ≤ 4) :
    A.card ≤ 5 := by
  let U : Finset ι := Finset.univ.filter (fun i => {i} ∈ A)
  let G := A.filter (fun S => S.card = 3)
  have hU : U.card ≤ 5 := hι ▸ U.card_le_univ
  have hsingle : A.filter (fun S => S.card = 1) = U.image (fun i => {i}) := by
    ext S
    constructor
    · intro hS
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hS).1⟩,rfl⟩
    · intro hS
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hS
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2,Finset.card_singleton i⟩
  have hsub : G ⊆ Uᶜ.powersetCard 3 := by
    intro S hS
    have hs := Finset.mem_filter.mp hS
    refine Finset.mem_powersetCard.mpr ⟨?_,hs.2⟩
    intro i hi
    apply Finset.mem_compl.mpr
    intro hiU
    have he := hA.eq (Finset.mem_filter.mp hiU).2 hs.1 (Finset.singleton_subset_iff.mpr hi)
    have hc := congrArg Finset.card he
    simp only [Finset.card_singleton,hs.2] at hc
    omega
  have hG := Finset.card_le_card hsub
  rw [Finset.card_powersetCard,Finset.card_compl,hι] at hG
  have hsplit : A = (A.filter (fun S => S.card = 1)) ∪ G := by
    ext S
    simp only [G,Finset.mem_union,Finset.mem_filter]
    exact ⟨fun h => (hrank S h).elim (fun h' => Or.inl ⟨h,h'⟩)
      (fun h' => Or.inr ⟨h,h'⟩),fun h => h.elim And.left And.left⟩
  have hdis : Disjoint (A.filter (fun S => S.card = 1)) G := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    have h₁ := (Finset.mem_filter.mp hS).2
    have h₃ := (Finset.mem_filter.mp hT).2
    omega
  have hcount : A.card = U.card+G.card := by
    conv_lhs => rw [hsplit,Finset.card_union_of_disjoint hdis,hsingle,
      Finset.card_image_of_injective _ Finset.singleton_injective]
  have hQ : G.card ≤ 4 := hquota
  rw [hcount]
  rcases Nat.eq_zero_or_pos U.card with hz | hp
  · omega
  · have hh : (5-U.card).choose 3 ≤ 5-U.card := by
      interval_cases h : U.card <;> norm_num [Nat.choose]
    omega

/-- In a five-coordinate reflected window, all odd ranks together
cost at most five. A triple quota alone would have left the weaker seven. -/
theorem five_window_odd_card_le {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 5) (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) :
    (A.filter (fun S => S.card % 2 = 1)).card ≤ 5 := by
  let F := A.filter (fun S => S.card % 2 = 1)
  have hsub : F ⊆ subsetWindow w b v := fun _ hs => hA (Finset.mem_filter.mp hs).1
  apply five_coordinate_odd_card_le hι F ((subsetWindow_antichain w hb hw v).subset hsub)
  · intro S hS
    have hp := (Finset.mem_filter.mp hS).2
    have hc : S.card ≤ 5 := hι ▸ S.card_le_univ
    have hne : S.card ≠ 5 := by
      intro he
      have hsu : S = Finset.univ := Finset.eq_univ_of_card S (he.trans hι.symm)
      exact window_union_ne_univ w hb.le hab hw ht (by omega) (hsub hS) (hsub hS)
        (by rw [Finset.union_self,hsu])
    omega
  · have hh := window_layer_card_le w hb.le hab hw ht
      (F.filter (fun S => S.card = 3)) (fun _ hs => hsub (Finset.mem_filter.mp hs).1)
      (by norm_num : 2 ≤ 3) (fun _ hs => (Finset.mem_filter.mp hs).2)
      (by rw [hι])
    simpa [hι,Nat.choose] using hh

/-- Removing a layer cannot exceed the central binomial capacity. -/
theorem offRankCapacity_le_upper_middle (k b j : ℕ) :
    offRankCapacity k b j ≤ k.choose ((k+1)/2) := by
  rw [upper_middle_choose]
  exact Finset.sup_le (fun _ _ => Nat.choose_le_middle _ _)

/-- The quota and LYM bound for an odd residual prime count. The minimum
retains the old bound even when a quota provides no improvement. -/
def oddWindowCapacity (k b : ℕ) : ℝ :=
  if k = 5 ∧ b = 1 then 5 else
  if 5 ≤ k ∧ k % 2 = 1 ∧ ((k+1)/2) % 2 = b then
    min (parityCapacity k b : ℝ)
      ((offRankCapacity k b ((k+1)/2) : ℝ)+
        (1-(offRankCapacity k b ((k+1)/2) : ℝ)/(k.choose ((k+1)/2) : ℝ))*
          ((k-1).choose (k-(k+1)/2-1) : ℝ))
  else (parityCapacity k b : ℝ)

/-- Both signed capacities are nonnegative. -/
theorem oddWindowCapacity_nonneg (k b : ℕ) : 0 ≤ oddWindowCapacity k b := by
  unfold oddWindowCapacity
  split_ifs with hspecial h
  · norm_num
  · apply le_min (Nat.cast_nonneg _)
    have hc : (0 : ℝ) < k.choose ((k+1)/2) := by
      exact_mod_cast Nat.choose_pos (show (k+1)/2 ≤ k by omega)
    have hb : (offRankCapacity k b ((k+1)/2) : ℝ) ≤ k.choose ((k+1)/2) := by
      exact_mod_cast offRankCapacity_le_upper_middle k b ((k+1)/2)
    have hh : 0 ≤ 1-(offRankCapacity k b ((k+1)/2) : ℝ)/(k.choose ((k+1)/2) : ℝ) :=
      sub_nonneg.mpr ((div_le_one hc).mpr hb)
    positivity
  · positivity

/-- Neither quota-based signed cost exceeds its original parity cost. -/
theorem oddWindowCapacity_le_parity (k b : ℕ) :
    oddWindowCapacity k b ≤ (parityCapacity k b : ℝ) := by
  unfold oddWindowCapacity
  split_ifs with hspecial
  · obtain ⟨rfl,rfl⟩ := hspecial
    have h : parityCapacity 5 1 = 10 := by decide +kernel
    norm_num [h]
  · exact min_le_left _ _
  · rfl

/-- Erdős--Ko--Rado and LYM together control all ranks of a parity in
the literal window, with no deletion of boundary subsets. -/
theorem window_parity_card_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {a b v : ℝ} (hb : 0 < b) (hab : a ≤ b)
    (hw : ∀ i, b ≤ w i) (ht : 3*v ≤ a+b+∑ i, w i)
    {A : Finset (Finset ι)} (hA : A ⊆ subsetWindow w b v) (e : ℕ) :
    ((A.filter (fun S => S.card % 2 = e)).card : ℝ) ≤
      oddWindowCapacity (Fintype.card ι) e := by
  have hold := (ZetaRieszComplementWindow.window_parity_card_le w hb hab hw ht hA e).trans
    (ZetaRieszComplementWindow.shortWindowCapacity_le_parity _ _)
  unfold oddWindowCapacity
  split_ifs with hspecial h
  · obtain ⟨hι,rfl⟩ := hspecial
    exact_mod_cast five_window_odd_card_le hι w hb hab hw ht hA
  · refine le_min hold ?_
    apply antichain_quota_bound ((subsetWindow_antichain w hb hw v).subset hA)
      (by omega) (offRankCapacity_le_upper_middle _ _ _)
    exact_mod_cast window_layer_card_le w hb.le hab hw ht
      (A.filter (fun S => S.card % 2 = e ∧ S.card = (Fintype.card ι+1)/2))
      (fun _ hs => hA (Finset.mem_filter.mp hs).1) (by omega)
      (fun _ hs => (Finset.mem_filter.mp hs).2.2) (by omega)
  · exact hold

/-- The original signed window uses the separate even and odd capacities,
including every negative term until the one-sided inequality. -/
theorem window_signed_bounds {ι : Type*} [Fintype ι] (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) :
    -oddWindowCapacity (Fintype.card ι) 1 ≤ (∑ S ∈ A, (-1 : ℝ)^S.card) ∧
      (∑ S ∈ A, (-1 : ℝ)^S.card) ≤ oddWindowCapacity (Fintype.card ι) 0 := by
  have hlo (S : Finset ι) : (if S.card % 2 = 1 then (-1 : ℝ) else 0) ≤ (-1 : ℝ)^S.card := by
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h <;>
      rw [neg_one_pow_eq_pow_mod_two,h] <;> norm_num
  have hhi (S : Finset ι) : (-1 : ℝ)^S.card ≤ if S.card % 2 = 0 then (1 : ℝ) else 0 := by
    rcases Nat.mod_two_eq_zero_or_one S.card with h | h <;>
      rw [neg_one_pow_eq_pow_mod_two,h] <;> norm_num
  have hl := Finset.sum_le_sum (fun S (_ : S ∈ A) => hlo S)
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ A) => hhi S)
  rw [← Finset.sum_filter] at hl hh
  simp only [Finset.sum_const,nsmul_eq_mul,mul_neg,mul_one] at hl hh
  exact ⟨(neg_le_neg (window_parity_card_le w hb hab hw ht hA 1)).trans hl,
    hh.trans (window_parity_card_le w hb hab hw ht hA 0)⟩

/-- Actual squarefree divisors inherit the complement-aware signed
window bound, with strict endpoints and exact Mobius signs. -/
theorem signedDivisorWindow_bounds {m : ℕ} (hm : Squarefree m) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ p ∈ m.primeFactors, b ≤ Real.log p)
    (ht : 3*v ≤ a+b+Real.log m) :
    -oddWindowCapacity m.primeFactors.card 1 ≤ signedDivisorWindow b v m ∧
      signedDivisorWindow b v m ≤ oddWindowCapacity m.primeFactors.card 0 := by
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
    have hc : (divisorPrimeSet m d).card = d.primeFactors.card := by
      rw [← divisorPrimeSet_map hm hd',Finset.card_map]
    rw [hc]
    exact_mod_cast ZetaRieszReflectedLinear.moebius_eq_primeCount
      (hm.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd'))
  rw [he]
  have hh := window_signed_bounds (fun p : m.primeFactors => Real.log (p.val : ℝ)) hb hab
    (fun p => hw p.val p.property) (by
      rw [Finset.sum_coe_sort m.primeFactors (fun p : ℕ => Real.log p),
        ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hm]
      exact ht) hsub
  simpa only [Fintype.card_coe] using hh

/-- The exact two-smallest-prime integral propagates both improved
capacities into the original Riesz coefficient at its reflected cutoff. -/
theorem riesz_lower_third_bounds {n : ℕ} (hn : Squarefree n)
    (hc : 2 ≤ n.primeFactors.card) {D : ℝ} (hD : 3*D ≤ Real.log n) :
    -(Real.log n.minFac*oddWindowCapacity (n.primeFactors.card-2) 1) ≤
        VaughanLogAverage.riesz D n ∧
      VaughanLogAverage.riesz D n ≤
        Real.log n.minFac*oddWindowCapacity (n.primeFactors.card-2) 0 := by
  obtain ⟨p,q,m,hp,hq,hpq,he,hm,hpm,hqm,hpmin,hqmin,hcount⟩ :=
    exists_two_smallest_factorization hn hc
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hpd : p ∣ n := he ▸ dvd_mul_right p (q*m)
  have hqd : q ∣ n := by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right q m) p
  have hep : p = n.minFac := le_antisymm
    (hpmin n.minFac ((Nat.minFac_prime hn1).mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero))
    (Nat.minFac_le_of_dvd hp.two_le hpd)
  have hlogpq : Real.log p ≤ Real.log q := Real.log_le_log
    (by exact_mod_cast hp.pos) (by exact_mod_cast hpmin q (hq.mem_primeFactors hqd hn.ne_zero))
  have hlog : Real.log n = Real.log p+Real.log q+Real.log m := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero hq.ne_zero hm.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hm.ne_zero)]
    ring
  have hi := integrableOn_signedDivisorWindow D (Real.log p) (Real.log q) m
  have hw (s : ℝ) (hs : s ∈ Ioo 0 (Real.log p)) := signedDivisorWindow_bounds hm
    (Real.log_pos (by exact_mod_cast hq.one_lt)) hlogpq
    (fun r hr => Real.log_le_log (by exact_mod_cast hq.pos) (by exact_mod_cast hqmin r hr))
    (show 3*(D-s) ≤ Real.log p+Real.log q+Real.log m by linarith [hs.1])
  have hlo := setIntegral_ge_of_const_le_real measurableSet_Ioo (by simp)
    (fun s hs => (hw s hs).1) hi
  have hhi := setIntegral_mono_on hi (integrableOn_const (hs := by simp)) measurableSet_Ioo
    (fun s hs => (hw s hs).2)
  rw [← riesz_two_primes_eq_window_integral D hp hq hpq hpm hqm,← he] at hlo hhi
  simp only [setIntegral_const,Real.volume_real_Ioo,sub_zero,
    max_eq_left (Real.log_natCast_nonneg p),smul_eq_mul] at hlo hhi
  rw [hep,hcount] at hlo hhi
  exact ⟨by nlinarith only [hlo],by nlinarith only [hhi]⟩

/-- Every odd-count squarefree coefficient receives the reflected
signed improvement without losing its actual least-prime logarithm. -/
theorem coefficient_odd_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card)
    (hodd : n.primeFactors.card % 2 = 1) (hcut : 2*Real.log n ≤ 3*L) :
    -(Real.log n/L*Real.log n.minFac*oddWindowCapacity (n.primeFactors.card-2) 1) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        Real.log n/L*Real.log n.minFac*oddWindowCapacity (n.primeFactors.card-2) 0 := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hr := VaughanLogAverage.riesz_reflection L hn hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hn] at hr
  simp only [neg_one_pow_eq_pow_mod_two,hodd,pow_one,Int.cast_neg,Int.cast_one,neg_one_mul] at hr
  have hh := riesz_lower_third_bounds hn hc (show 3*(Real.log n-L) ≤ Real.log n by linarith)
  rw [hr] at hh
  have hscale := div_nonneg (Real.log_natCast_nonneg n) hL.le
  have hlo := mul_le_mul_of_nonneg_left hh.1 hscale
  have hhi := mul_le_mul_of_nonneg_left hh.2 hscale
  have hsupport : Squarefree n ∧ ¬ n.Prime := ⟨hn,hnp⟩
  simp only [SquarefreeVaughanLogSource.coefficient,if_pos hsupport,Complex.ofReal_re]
  have he : -Real.log n*VaughanLogAverage.riesz L n/L =
      -(Real.log n/L)*VaughanLogAverage.riesz L n := by ring
  rw [he]
  constructor <;> nlinarith only [hlo,hhi]


/-- Seven-prime coefficient capacities: the dangerous negative side
falls from ten to five in units `(log n/L)*log(minFac n)`. -/
theorem oddWindowCapacity_five :
    oddWindowCapacity 5 0 = 10 ∧ oddWindowCapacity 5 1 = 5 := by
  have h₀ : parityCapacity 5 0 = 10 := by decide +kernel
  have h₁ : parityCapacity 5 1 = 10 := by decide +kernel
  have hB : offRankCapacity 5 1 3 = 5 := by decide +kernel
  norm_num [oddWindowCapacity,h₀,h₁,hB,Nat.choose]

/-- Nine-prime coefficient capacities: the positive side falls from
thirty-five to twenty-seven before applying the original phase. -/
theorem oddWindowCapacity_seven :
    oddWindowCapacity 7 0 = 27 ∧ oddWindowCapacity 7 1 = 35 := by
  have h₀ : parityCapacity 7 0 = 35 := by decide +kernel
  have h₁ : parityCapacity 7 1 = 35 := by decide +kernel
  have hB : offRankCapacity 7 0 4 = 21 := by decide +kernel
  norm_num [oddWindowCapacity,h₀,h₁,hB,Nat.choose]

/-- Eleven-prime capacities, checked by exact rational arithmetic. -/
theorem oddWindowCapacity_nine :
    oddWindowCapacity 9 0 = 126 ∧ oddWindowCapacity 9 1 = 308/3 := by
  have h₀ : parityCapacity 9 0 = 126 := by decide +kernel
  have h₁ : parityCapacity 9 1 = 126 := by decide +kernel
  have hB : offRankCapacity 9 1 5 = 84 := by decide +kernel
  norm_num [oddWindowCapacity,h₀,h₁,hB,Nat.choose]

/-- The original seven-prime coefficient has the improved reflected
interval, with its actual least prime and every divisor sign retained. -/
theorem coefficient_seven_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7) (hcut : 2*Real.log n ≤ 3*L) :
    -(5*(Real.log n/L)*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        10*(Real.log n/L)*Real.log n.minFac := by
  have hh := coefficient_odd_bounds hL hn (by omega) (by omega) hcut
  rw [hc,show 7-2 = (5 : ℕ) by decide,oddWindowCapacity_five.1,oddWindowCapacity_five.2] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

/-- The original nine-prime coefficient has the improved reflected
interval, independently of any zeta zero or prime-density approximation. -/
theorem coefficient_nine_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 9) (hcut : 2*Real.log n ≤ 3*L) :
    -(35*(Real.log n/L)*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        27*(Real.log n/L)*Real.log n.minFac := by
  have hh := coefficient_odd_bounds hL hn (by omega) (by omega) hcut
  rw [hc,show 9-2 = (7 : ℕ) by decide,oddWindowCapacity_seven.1,oddWindowCapacity_seven.2] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

/-- For an odd residual count, complementary central ranks have opposite
parities and equal size. Both old parity capacities equal that size. -/
theorem parityCapacity_odd_eq_middle {k b : ℕ} (hk : k % 2 = 1) (hb : b ≤ 1) :
    parityCapacity k b = k.choose (k/2) := by
  apply le_antisymm (parityCapacity_le_middle k b)
  by_cases hm : (k/2) % 2 = b
  · exact choose_le_parityCapacity (Nat.div_le_self k 2) hm
  · rw [← upper_middle_choose]
    apply choose_le_parityCapacity (by omega)
    omega

/-- The actual least-prime coefficient allowance after the complement
restriction. Absent arithmetic support has zero cost. -/
def allowance (L : ℝ) (n b : ℕ) : ℝ :=
  if Squarefree n ∧ 2 ≤ n.primeFactors.card then
    Real.log n/L*Real.log n.minFac*oddWindowCapacity (n.primeFactors.card-2) (1-b)
  else 0

/-- Both one-sided coefficient allowances are nonnegative. -/
theorem allowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) : 0 ≤ allowance L n b := by
  unfold allowance
  split_ifs
  · positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac,
      oddWindowCapacity_nonneg (n.primeFactors.card-2) (1-b)]
  · rfl

/-- The new allowance is never larger than the earlier parity-sensitive
mean-prime allowance; it also retains the exact least prime. -/
theorem allowance_le_signed {L : ℝ} (hL : 0 < L) (n b : ℕ)
    (hc : n.primeFactors.card % 2 = 1) (hb : b ≤ 1) :
    allowance L n b ≤ signedAllowance L n b := by
  unfold allowance signedAllowance
  split_ifs with h
  · have hn1 : n ≠ 1 := by intro he; simp [he] at h
    have hp := Nat.minFac_prime hn1
    have hm := smallest_prime_log_le_mean h.1 (by omega) hp
      (fun p hp => Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
        (Nat.dvd_of_mem_primeFactors hp))
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hm (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    · have hk : (n.primeFactors.card-2) % 2 = 1 := by omega
      have hh := oddWindowCapacity_le_parity (n.primeFactors.card-2) (1-b)
      rw [parityCapacity_odd_eq_middle hk (show 1-b ≤ 1 by omega)] at hh
      rw [parityCapacity_odd_eq_middle hk hb]
      exact hh
    · exact oddWindowCapacity_nonneg _ _
    · positivity [Real.log_natCast_nonneg n]
  · rfl

/-- At every odd prime count, the original coefficient has the new
signed interval throughout the actual reflected-cutoff geometry. -/
theorem coefficient_allowance_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 2 ≤ n.primeFactors.card) (hodd : n.primeFactors.card % 2 = 1)
    (hcut : 2*Real.log n ≤ 3*L) :
    -allowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ allowance L n 1 := by
  by_cases hn : Squarefree n
  · have hs : Squarefree n ∧ 2 ≤ n.primeFactors.card := ⟨hn,hc⟩
    simpa only [allowance,if_pos hs,Nat.sub_zero,Nat.sub_self] using coefficient_odd_bounds hL hn hc hodd hcut
  · simp only [allowance,SquarefreeVaughanLogSource.coefficient,hn,false_and,if_false,
      Complex.zero_re,neg_zero,le_refl,and_self]

/-- The lower charge assigns the two improved capacities to the two
original cosine orientations. The phase itself is never replaced. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  allowance L n 0*max (Real.cos (y*Real.log n)) 0+
    allowance L n 1*max (-Real.cos (y*Real.log n)) 0

/-- The upper charge exchanges the original phase orientations. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  allowance L n 1*max (Real.cos (y*Real.log n)) 0+
    allowance L n 0*max (-Real.cos (y*Real.log n)) 0

/-- Nonnegative comparator costs for both sides of the joint endgame. -/
theorem costs_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ floorCost L y n ∧ 0 ≤ ceilingCost L y n := by
  have h₀ := allowance_nonneg hL n 0
  have h₁ := allowance_nonneg hL n 1
  constructor <;> dsimp only [floorCost,ceilingCost] <;> positivity

/-- Every original phase has no larger cost than before. This comparison
spends no prime supply and does not take an absolute cosine. -/
theorem costs_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ)
    (hc : n.primeFactors.card % 2 = 1) :
    floorCost L y n ≤ lowerCost L y n ∧ ceilingCost L y n ≤ upperCost L y n := by
  have h₀ := allowance_le_signed hL n 0 hc (by omega)
  have h₁ := allowance_le_signed hL n 1 hc (by omega)
  constructor <;> dsimp only [floorCost,ceilingCost,lowerCost,upperCost] <;> gcongr

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- The complete original atom retains its factorial, allocation and
complex phase, with both improved one-sided estimates. -/
theorem residual_odd_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 2 ≤ n.primeFactors.card)
    (hodd : n.primeFactors.card % 2 = 1) (hcut : 2*Real.log n ≤ 3*L) :
    -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*ceilingCost L y n := by
  have hh := coefficient_allowance_bounds hL hc hodd hcut
  rw [re_residual_atom]
  have hw := weight_nonneg A N n
  suffices hs : -floorCost L y n ≤
        (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤
        ceilingCost L y n by
    exact ⟨by simpa only [mul_neg] using mul_le_mul_of_nonneg_left hs.1 hw,
      mul_le_mul_of_nonneg_left hs.2 hw⟩
  by_cases hx : 0 ≤ Real.cos (y*Real.log n)
  · have hlo := mul_le_mul_of_nonneg_right hh.1 hx
    have hhi := mul_le_mul_of_nonneg_right hh.2 hx
    simp only [floorCost,ceilingCost,max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),mul_zero,add_zero]
    constructor <;> nlinarith only [hlo,hhi]
  · have hx' := le_of_not_ge hx
    have hlo := mul_le_mul_of_nonpos_right hh.2 hx'
    have hhi := mul_le_mul_of_nonpos_right hh.1 hx'
    simp only [floorCost,ceilingCost,max_eq_right hx',max_eq_left (neg_nonneg.mpr hx'),mul_zero,zero_add]
    constructor <;> nlinarith only [hlo,hhi]

/-- Keep every favorable selected observation in both alternatives; the
coefficient reduction is not an additional signed supply. -/
theorem residual_odd_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 2 ≤ n.primeFactors.card)
    (hodd : n.primeFactors.card % 2 = 1) (hcut : 2*Real.log n ≤ 3*L) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  dsimp only
  have hh := residual_odd_bounds A hL y N hc hodd hcut
  have hlo := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).1
  have hhi := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).2
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hlo]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hhi]

/-- The whole selected finite sum inherits all higher odd-count savings
at once. Other counts stay exactly in the same signed observation. -/
theorem sum_higher_odd_bounds (S A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) (hcut : ∀ n ∈ S, 2*Real.log n ≤ 3*L) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if 7 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 1 then
      max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        (∑ n ∈ S, f n).re ∧
      (∑ n ∈ S, f n).re ≤ ∑ n ∈ S, if 7 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 1 then
        min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re := by
  dsimp only
  rw [Complex.re_sum]
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_odd_retained_bounds A hL y N (by omega) hc.2 (hcut n hn)).1
    · exact le_rfl
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_odd_retained_bounds A hL y N (by omega) hc.2 (hcut n hn)).2
    · exact le_rfl

open Filter Topology ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- On every subset of the actual core, both source-normalized inequalities
hold uniformly in height and count ceiling. The existing six-prime bound
and every other count remain intact. The signed complement is not bounded. -/
theorem eventually_core_subset_higher_odd_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 1 then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
          ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
          u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 1 then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU]
    with N hcut K y S hS
  have hh := sum_higher_odd_bounds S (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) y N (fun n hn => hcut K n (hS hn))
  have hlo := mul_le_mul_of_nonneg_left hh.1 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  have hhi := mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  dsimp only
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hlo hhi


end
end RiemannGaussian.ZetaRieszIntersectingWindow
