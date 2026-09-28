/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSixPrimeGeometry

/-!
# Complementary divisor subsets sharpen the signed higher-count costs

At the reflected one-third cutoff, complementary middle-rank subsets
cannot both survive. Their occupancy is at most half a binomial layer.
Combining that restriction with the parity-specific LYM budget bounds the
original signed coefficient, before applying its unchanged phase and
factorial/allocation weight. No new carrier or prime supply is introduced.
-/

namespace RiemannGaussian.ZetaRieszComplementWindow
noncomputable section
open scoped BigOperators Classical
open Set MeasureTheory
open ZetaRieszSperner ZetaRieszSignedSperner ZetaSquarefreeRieszWindows

/-- Largest layer of one parity after the middle rank is excluded. -/
def offMiddleCapacity (k b : ℕ) : ℕ :=
  ((Finset.range (k+1)).filter (fun j => j % 2 = b ∧ j ≠ k/2)).sup (fun j => k.choose j)

/-- The off-middle capacity is bounded by the old parity capacity. -/
theorem offMiddleCapacity_le_parity (k b : ℕ) :
    offMiddleCapacity k b ≤ parityCapacity k b := by
  apply Finset.sup_le
  intro j hj
  obtain ⟨hj,hb,_⟩ := Finset.mem_filter.mp hj
  exact choose_le_parityCapacity (by have := Finset.mem_range.mp hj; omega) hb

/-- The actual short-window capacity combines the half-filled central
layer with the unchanged parity capacity on all other ranks. -/
def shortWindowCapacity (k b : ℕ) : ℝ :=
  if 4 ≤ k ∧ k % 2 = 0 ∧ (k/2) % 2 = b then
    ((k.choose (k/2) : ℝ)+(offMiddleCapacity k b : ℝ))/2
  else (parityCapacity k b : ℝ)

/-- Every short-window charge is nonnegative. -/
theorem shortWindowCapacity_nonneg (k b : ℕ) : 0 ≤ shortWindowCapacity k b := by
  unfold shortWindowCapacity
  split_ifs <;> positivity

/-- The complement restriction never increases either old signed cost. -/
theorem shortWindowCapacity_le_parity (k b : ℕ) :
    shortWindowCapacity k b ≤ (parityCapacity k b : ℝ) := by
  unfold shortWindowCapacity
  split_ifs with h
  · have hmid := choose_le_parityCapacity (Nat.div_le_self k 2) h.2.2
    have hoff := offMiddleCapacity_le_parity k b
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact_mod_cast (show k.choose (k/2)+offMiddleCapacity k b ≤ parityCapacity k b*2 by omega)
  · rfl

/-- Complementation doubles a middle-rank family with no antipodal pair.
This statement is finite and keeps every boundary subset. -/
theorem middle_layer_twice_card_le {ι : Type*} [Fintype ι] {j : ℕ}
    (hι : Fintype.card ι = 2*j) (A : Finset (Finset ι))
    (hc : ∀ S ∈ A, S.card = j) (hopp : ∀ S ∈ A, Sᶜ ∉ A) :
    2*A.card ≤ (2*j).choose j := by
  let B := A.image (fun S => Sᶜ)
  have hdis : Disjoint A B := Finset.disjoint_left.mpr (by
    intro S hS hB
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hB
    exact hopp T hT hS)
  have hB : B.card = A.card := Finset.card_image_of_injective _ compl_injective
  have hsub : A ∪ B ⊆ (Finset.univ : Finset ι).powersetCard j := by
    intro S hS
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · exact hc S hS
    · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
      rw [Finset.card_compl,hι,hc T hT]
      omega
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hB,Finset.card_powersetCard,Finset.card_univ,hι] at hh
  omega

/-- The one-third window cannot contain both a subset with at least two
coordinates and its complement. Strict endpoints eliminate equality. -/
theorem window_compl_notMem {ι : Type*} [Fintype ι] (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 ≤ b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {S : Finset ι}
    (hc : 2 ≤ S.card) (hS : S ∈ subsetWindow w b v) :
    Sᶜ ∉ subsetWindow w b v := by
  intro hSc
  have hsum := Finset.sum_le_sum (s := S) (fun i _ => hw i)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  have hc' : (2 : ℝ) ≤ S.card := by exact_mod_cast hc
  have h₁ := (Finset.mem_filter.mp hS).2.2
  have h₂ := (Finset.mem_filter.mp hSc).2.2
  have he := Finset.sum_add_sum_compl S w
  nlinarith [mul_le_mul_of_nonneg_right hc' hb]

/-- Half of the central binomial layer plus the off-middle LYM budget
bounds one parity of any complement-free middle-rank antichain. -/
theorem antichain_parity_card_bound {ι : Type*} [Fintype ι] {b : ℕ}
    {A : Finset (Finset ι)} (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι)))
    (heven : Fintype.card ι % 2 = 0)
    (hopp : ∀ S ∈ A, S.card = Fintype.card ι/2 → Sᶜ ∉ A) :
    ((A.filter (fun S => S.card % 2 = b)).card : ℝ) ≤
      ((Fintype.card ι).choose (Fintype.card ι/2) +
        (offMiddleCapacity (Fintype.card ι) b : ℝ))/2 := by
  let k := Fintype.card ι
  let F := A.filter (fun S => S.card % 2 = b)
  let C := ((k.choose (k/2) : ℕ) : ℝ)
  let B := (offMiddleCapacity k b : ℝ)
  let M := F.filter (fun S => S.card = k/2)
  have hC : 0 < C := by
    dsimp only [C]
    exact_mod_cast Nat.choose_pos (Nat.div_le_self k 2)
  have hB : 0 ≤ B := by positivity
  have hBC : B ≤ C := by
    dsimp only [B,C]
    exact_mod_cast (offMiddleCapacity_le_parity k b).trans (parityCapacity_le_middle k b)
  have hmid : 2*M.card ≤ k.choose (k/2) := by
    have hk : k = 2*(k/2) := by dsimp [k]; omega
    have h := middle_layer_twice_card_le (ι := ι) (j := k/2) hk M
      (fun _ hs => (Finset.mem_filter.mp hs).2) (by
        intro S hS hSc
        have hs := Finset.mem_filter.mp hS
        exact hopp S (Finset.mem_filter.mp hs.1).1 hs.2
          (Finset.mem_filter.mp (Finset.mem_filter.mp hSc).1).1)
    simpa only [← hk] using h
  have hlym : (∑ S ∈ F, ((Fintype.card ι).choose S.card : ℝ)⁻¹) ≤ 1 :=
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (hA.subset (Finset.filter_subset (fun S : Finset ι => S.card % 2 = b) A))
  change (∑ S ∈ F, ((k.choose S.card : ℕ) : ℝ)⁻¹) ≤ 1 at hlym
  have hterm (S : Finset ι) (hS : S ∈ F) :
      (1 : ℝ) ≤ B*((k.choose S.card : ℕ) : ℝ)⁻¹ +
        (if S.card = k/2 then 1-B/C else 0) := by
    by_cases hm : S.card = k/2
    · rw [if_pos hm,hm]
      change 1 ≤ B*C⁻¹+(1-B/C)
      simp only [div_eq_mul_inv]
      linarith
    · rw [if_neg hm,add_zero]
      have hc : (0 : ℝ) < k.choose S.card := by exact_mod_cast Nat.choose_pos S.card_le_univ
      have hp := (Finset.mem_filter.mp hS).2
      have hle : k.choose S.card ≤ offMiddleCapacity k b :=
        Finset.le_sup (f := fun j => k.choose j)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := S.card_le_univ; dsimp [k]; omega),hp,hm⟩)
      rw [← div_eq_mul_inv,le_div_iff₀ hc,one_mul]
      dsimp only [B]
      exact_mod_cast hle
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hL := mul_le_mul_of_nonneg_left hlym hB
  have hmid' : (M.card : ℝ) ≤ C/2 := by
    have hh : 2*(M.card : ℝ) ≤ C := by dsimp only [C]; exact_mod_cast hmid
    linarith
  have hcoef : 0 ≤ 1-B/C := sub_nonneg.mpr ((div_le_one hC).mpr hBC)
  have hM := mul_le_mul_of_nonneg_right hmid' hcoef
  have he : (C/2)*(1-B/C) = (C-B)/2 := by field_simp
  rw [he] at hM
  change (F.card : ℝ) ≤ _
  change (F.card : ℝ) ≤ B*(∑ S ∈ F, ((k.choose S.card : ℕ) : ℝ)⁻¹)+
    (M.card : ℝ)*(1-B/C) at hs
  dsimp only [B,C,k] at *
  nlinarith only [hs,hL,hM]


private theorem parity_card_le {ι : Type*} [Fintype ι] {A : Finset (Finset ι)}
    (hA : IsAntichain (· ⊆ ·) (A : Set (Finset ι))) (b : ℕ) :
    ((A.filter (fun S => S.card % 2 = b)).card : ℝ) ≤ (parityCapacity (Fintype.card ι) b : ℝ) := by
  let F := A.filter (fun S => S.card % 2 = b)
  have hlym : (∑ S ∈ F, ((Fintype.card ι).choose S.card : ℝ)⁻¹) ≤ 1 :=
    Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (hA.subset (Finset.filter_subset (fun S : Finset ι => S.card % 2 = b) A))
  have hpoint (S : Finset ι) (hS : S ∈ F) :
      (1 : ℝ) ≤ (parityCapacity (Fintype.card ι) b : ℝ)*
        ((Fintype.card ι).choose S.card : ℝ)⁻¹ := by
    have hc : (0 : ℝ) < (Fintype.card ι).choose S.card := by
      exact_mod_cast Nat.choose_pos S.card_le_univ
    rw [← div_eq_mul_inv,le_div_iff₀ hc,one_mul]
    exact_mod_cast choose_le_parityCapacity S.card_le_univ (Finset.mem_filter.mp hS).2
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left hlym (by positivity)).trans_eq (mul_one _))

/-- Both parity populations in the literal reflected window obey the
sharper scalar capacities. No signed observation is changed. -/
theorem window_parity_card_le {ι : Type*} [Fintype ι] (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) (e : ℕ) :
    ((A.filter (fun S => S.card % 2 = e)).card : ℝ) ≤
      shortWindowCapacity (Fintype.card ι) e := by
  have ha := (subsetWindow_antichain w hb hw v).subset hA
  unfold shortWindowCapacity
  split_ifs with h
  · apply antichain_parity_card_bound ha h.2.1
    intro S hS hSc
    exact fun hcomp => window_compl_notMem w hb.le hab hw ht
      (by rw [hSc]; omega) (hA hS) (hA hcomp)
  · exact parity_card_le ha e

/-- The original signed window uses the separate even and odd capacities,
including every negative term until the one-sided inequality. -/
theorem window_signed_bounds {ι : Type*} [Fintype ι] (w : ι → ℝ) {a b v : ℝ}
    (hb : 0 < b) (hab : a ≤ b) (hw : ∀ i, b ≤ w i)
    (ht : 3*v ≤ a+b+∑ i, w i) {A : Finset (Finset ι)}
    (hA : A ⊆ subsetWindow w b v) :
    -shortWindowCapacity (Fintype.card ι) 1 ≤ (∑ S ∈ A, (-1 : ℝ)^S.card) ∧
      (∑ S ∈ A, (-1 : ℝ)^S.card) ≤ shortWindowCapacity (Fintype.card ι) 0 := by
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
    -shortWindowCapacity m.primeFactors.card 1 ≤ signedDivisorWindow b v m ∧
      signedDivisorWindow b v m ≤ shortWindowCapacity m.primeFactors.card 0 := by
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
    -(Real.log n.minFac*shortWindowCapacity (n.primeFactors.card-2) 1) ≤
        VaughanLogAverage.riesz D n ∧
      VaughanLogAverage.riesz D n ≤
        Real.log n.minFac*shortWindowCapacity (n.primeFactors.card-2) 0 := by
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

/-- Every even-count squarefree coefficient receives the reflected
signed improvement without losing its actual least-prime logarithm. -/
theorem coefficient_even_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : 2 ≤ n.primeFactors.card)
    (heven : n.primeFactors.card % 2 = 0) (hcut : 2*Real.log n ≤ 3*L) :
    -(Real.log n/L*Real.log n.minFac*shortWindowCapacity (n.primeFactors.card-2) 0) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        Real.log n/L*Real.log n.minFac*shortWindowCapacity (n.primeFactors.card-2) 1 := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hr := VaughanLogAverage.riesz_reflection L hn hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hn] at hr
  simp only [neg_one_pow_eq_pow_mod_two,heven,pow_zero,Int.cast_one,one_mul] at hr
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


/-- Six residual coordinates have improved signed capacities 15 and 13;
the latter was 20 before using complementary-subset exclusion. -/
theorem shortWindowCapacity_six :
    shortWindowCapacity 6 0 = 15 ∧ shortWindowCapacity 6 1 = 13 := by
  have h : offMiddleCapacity 6 1 = 6 := by decide +kernel
  norm_num [shortWindowCapacity,h,parityCapacity_six.1,Nat.choose]

/-- Eight residual coordinates reduce the even capacity from 70 to 49,
while retaining the odd capacity 56. -/
theorem shortWindowCapacity_eight :
    shortWindowCapacity 8 0 = 49 ∧ shortWindowCapacity 8 1 = 56 := by
  have h : offMiddleCapacity 8 0 = 28 := by decide +kernel
  have h' : parityCapacity 8 1 = 56 := by decide +kernel
  norm_num [shortWindowCapacity,h,h',Nat.choose]

/-- Ten residual coordinates reduce the odd capacity from 252 to 186,
while retaining the even capacity 210. -/
theorem shortWindowCapacity_ten :
    shortWindowCapacity 10 0 = 210 ∧ shortWindowCapacity 10 1 = 186 := by
  have h : offMiddleCapacity 10 1 = 120 := by decide +kernel
  have h' : parityCapacity 10 0 = 210 := by decide +kernel
  norm_num [shortWindowCapacity,h,h',Nat.choose]

/-- The literal eight-prime coefficient interval is [-15,13] in units
of (log n/L)*log(minFac n), throughout the reflected core geometry. -/
theorem coefficient_eight_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 8) (hcut : 2*Real.log n ≤ 3*L) :
    -(15*(Real.log n/L)*Real.log n.minFac) ≤
        (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤
        13*(Real.log n/L)*Real.log n.minFac := by
  have hh := coefficient_even_bounds hL hn (by omega) (by omega) hcut
  rw [hc,show 8-2 = (6 : ℕ) by decide,shortWindowCapacity_six.1,shortWindowCapacity_six.2] at hh
  constructor <;> nlinarith only [hh.1,hh.2]

/-- The actual least-prime coefficient allowance after the complement
restriction. Absent arithmetic support has zero cost. -/
def allowance (L : ℝ) (n b : ℕ) : ℝ :=
  if Squarefree n ∧ 2 ≤ n.primeFactors.card then
    Real.log n/L*Real.log n.minFac*shortWindowCapacity (n.primeFactors.card-2) b
  else 0

/-- Both one-sided coefficient allowances are nonnegative. -/
theorem allowance_nonneg {L : ℝ} (hL : 0 < L) (n b : ℕ) : 0 ≤ allowance L n b := by
  unfold allowance
  split_ifs
  · positivity [Real.log_natCast_nonneg n,Real.log_natCast_nonneg n.minFac,
      shortWindowCapacity_nonneg (n.primeFactors.card-2) b]
  · rfl

/-- The new allowance is never larger than the earlier parity-sensitive
mean-prime allowance; it also retains the exact least prime. -/
theorem allowance_le_signed {L : ℝ} (hL : 0 < L) (n b : ℕ) :
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
    · exact shortWindowCapacity_le_parity _ _
    · exact shortWindowCapacity_nonneg _ _
    · positivity [Real.log_natCast_nonneg n]
  · rfl

/-- At every even prime count, the original coefficient has the new
signed interval throughout the actual reflected-cutoff geometry. -/
theorem coefficient_allowance_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 2 ≤ n.primeFactors.card) (heven : n.primeFactors.card % 2 = 0)
    (hcut : 2*Real.log n ≤ 3*L) :
    -allowance L n 0 ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ allowance L n 1 := by
  by_cases hn : Squarefree n
  · have hs : Squarefree n ∧ 2 ≤ n.primeFactors.card := ⟨hn,hc⟩
    simpa only [allowance,if_pos hs] using coefficient_even_bounds hL hn hc heven hcut
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
theorem costs_le_previous {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    floorCost L y n ≤ lowerCost L y n ∧ ceilingCost L y n ≤ upperCost L y n := by
  have h₀ := allowance_le_signed hL n 0
  have h₁ := allowance_le_signed hL n 1
  constructor <;> dsimp only [floorCost,ceilingCost,lowerCost,upperCost] <;> gcongr

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- The complete original atom retains its factorial, allocation and
complex phase, with both improved one-sided estimates. -/
theorem residual_even_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 2 ≤ n.primeFactors.card)
    (heven : n.primeFactors.card % 2 = 0) (hcut : 2*Real.log n ≤ 3*L) :
    -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*ceilingCost L y n := by
  have hh := coefficient_allowance_bounds hL hc heven hcut
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
theorem residual_even_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) {n : ℕ} (hc : 2 ≤ n.primeFactors.card)
    (heven : n.primeFactors.card % 2 = 0) (hcut : 2*Real.log n ≤ 3*L) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  dsimp only
  have hh := residual_even_bounds A hL y N hc heven hcut
  have hlo := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).1
  have hhi := mul_nonneg (weight_nonneg A N n) (costs_nonneg hL y n).2
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hlo]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hhi]

/-- The whole selected finite sum inherits all higher even-count savings
at once. Other counts stay exactly in the same signed observation. -/
theorem sum_higher_even_bounds (S A : Finset ℕ) {L : ℝ} (hL : 0 < L)
    (y : ℝ) (N : ℕ) (hcut : ∀ n ∈ S, 2*Real.log n ≤ 3*L) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if 8 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 0 then
      max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        (∑ n ∈ S, f n).re ∧
      (∑ n ∈ S, f n).re ≤ ∑ n ∈ S, if 8 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 0 then
        min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re := by
  dsimp only
  rw [Complex.re_sum]
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_even_retained_bounds A hL y N (by omega) hc.2 (hcut n hn)).1
    · exact le_rfl
  · apply Finset.sum_le_sum
    intro n hn
    split_ifs with hc
    · exact (residual_even_retained_bounds A hL y N (by omega) hc.2 (hcut n hn)).2
    · exact le_rfl

open Filter Topology ZetaRieszParityPacket ZetaRieszAnnulusJoint

/-- On every subset of the actual core, both source-normalized inequalities
hold uniformly in height and count ceiling. The existing six-prime bound
and every other count remain intact. The signed complement is not bounded. -/
theorem eventually_core_subset_higher_even_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if 8 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 0 then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
          ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
          u^(N+1)*(∑ n ∈ S, if 8 ≤ n.primeFactors.card ∧ n.primeFactors.card % 2 = 0 then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU]
    with N hcut K y S hS
  have hh := sum_higher_even_bounds S (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length_pos u N) y N (fun n hn => hcut K n (hS hn))
  have hlo := mul_le_mul_of_nonneg_left hh.1 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  have hhi := mul_le_mul_of_nonneg_left hh.2 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  dsimp only
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hlo hhi

end
end RiemannGaussian.ZetaRieszComplementWindow
