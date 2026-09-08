import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Exact cancellation inside a clipped coprime Moebius square

The full coprime divisor coefficient is evaluated before taking absolute
values. Below the product of the two omitted cutoffs, its value depends
only on the product of the eligible distinct primes and on the two exact
cutoff comparisons. The resulting coefficient bound is one, with no
divisor-count factor. No cancellation between different physical integers
is asserted here.
-/

open Finset Nat
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian.EtaCoprimeRadical

noncomputable section

private def sign (S : Finset ℕ) : ℤ := (-1) ^ S.card

private theorem sum_sign_powerset (S : Finset ℕ) :
    (∑ R ∈ S.powerset, sign R) = if S = ∅ then 1 else 0 := by
  have h := Finset.prod_one_add (R := ℤ) (f := fun _ : ℕ ↦ -1) S
  simp only [show (1 : ℤ) + -1 = 0 by norm_num, Finset.prod_const] at h
  simp only [sign]
  rw [← h]
  by_cases hS : S = ∅
  · simp [hS]
  · simp [hS, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)]

private theorem sum_disjoint_sign {S R : Finset ℕ} (hR : R ⊆ S) :
    (∑ T ∈ S.powerset, if Disjoint R T then sign T else 0) =
      if R = S then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hf : S.powerset.filter (fun T ↦ Disjoint R T) = (S \ R).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff,
      disjoint_comm]
  rw [hf, sum_sign_powerset]
  have he : S \ R = ∅ ↔ R = S := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h ↦ Finset.Subset.antisymm hR h, fun h ↦ h ▸ Finset.Subset.refl _⟩
  simp only [he]

private theorem sum_disjoint_weight (S : Finset ℕ) (f : Finset ℕ → ℤ) :
    (∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
      if Disjoint R T then sign R * sign T * f R else 0) = sign S * f S := by
  have he (R : Finset ℕ) (hR : R ∈ S.powerset) :
      (∑ T ∈ S.powerset, if Disjoint R T then sign R * sign T * f R else 0) =
        if R = S then sign R * f R else 0 := by
    calc
      _ = sign R * f R * ∑ T ∈ S.powerset, if Disjoint R T then sign T else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        split_ifs <;> ring
      _ = _ := by
        rw [sum_disjoint_sign (Finset.mem_powerset.mp hR)]
        split_ifs <;> ring
  rw [Finset.sum_congr rfl he]
  simp

private theorem sign_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    μ (∏ p ∈ S, p) = sign S := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime S hS]
  simp only [sign, ← Finset.prod_const]
  exact Finset.prod_congr rfl (fun p hp ↦ ArithmeticFunction.moebius_apply_prime (hS p hp))

/-- The distinct primes in the physical integer that do not divide the fixed gcd. -/
def eligiblePrimes (g n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p ↦ ¬p ∣ g)

/-- The squarefree product of the eligible primes, retaining the fixed gcd. -/
def eligibleRadical (g n : ℕ) : ℕ := ∏ p ∈ eligiblePrimes g n, p

/-- The actual rectangular coprime divisor coefficient, with both cutoffs retained. -/
def coefficient (g L V n : ℕ) : ℤ :=
  ∑ a ∈ Finset.Icc 1 L, ∑ b ∈ Finset.Icc 1 V,
    if a * b ∣ n ∧ a.Coprime b ∧ g.Coprime a ∧ g.Coprime b then μ a * μ b else 0

private theorem prime_of_eligible {g n p : ℕ} (hp : p ∈ eligiblePrimes g n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

private theorem prod_eligible_pos {g n : ℕ} {S : Finset ℕ} (hS : S ⊆ eligiblePrimes g n) :
    0 < ∏ p ∈ S, p :=
  Finset.prod_pos (fun _ hp ↦ (prime_of_eligible (hS hp)).pos)

private theorem coprime_prod_eligible {g n : ℕ} {S : Finset ℕ} (hS : S ⊆ eligiblePrimes g n) :
    g.Coprime (∏ p ∈ S, p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  exact ((prime_of_eligible (hS hp)).coprime_iff_not_dvd.mpr
    (Finset.mem_filter.mp (hS hp)).2).symm

private theorem primeFactors_subset_eligible {g n a : ℕ} (hn : n ≠ 0)
    (ha : a ∣ n) (hga : g.Coprime a) : a.primeFactors ⊆ eligiblePrimes g n := by
  intro p hp
  refine Finset.mem_filter.mpr ⟨Nat.primeFactors_mono ha hn hp, ?_⟩
  intro hpg
  have hpa := Nat.dvd_of_mem_primeFactors hp
  exact (Nat.prime_of_mem_primeFactors hp).ne_one (Nat.eq_one_of_dvd_coprimes hga hpg hpa)

private def subsetCoefficient (S : Finset ℕ) (L V : ℕ) : ℤ :=
  ∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
    if Disjoint R T ∧ (∏ p ∈ R, p) ≤ L ∧ (∏ p ∈ T, p) ≤ V then sign R * sign T else 0

private theorem prod_pair_dvd {g n : ℕ} {R T : Finset ℕ}
    (hR : R ⊆ eligiblePrimes g n) (hT : T ⊆ eligiblePrimes g n)
    (hRT : Disjoint R T) : (∏ p ∈ R, p) * (∏ p ∈ T, p) ∣ n := by
  rw [← Finset.prod_union hRT]
  apply dvd_trans _ (Nat.prod_primeFactors_dvd n)
  exact Finset.prod_dvd_prod_of_subset _ _ _ (fun p hp ↦
    (Finset.mem_filter.mp ((Finset.union_subset hR hT) hp)).1)

private theorem coefficient_eq_subsetCoefficient (g L V : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    coefficient g L V n = subsetCoefficient (eligiblePrimes g n) L V := by
  unfold coefficient subsetCoefficient
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_bij_ne_zero (fun x _ _ ↦ (x.1.primeFactors, x.2.primeFactors)) ?_ ?_ ?_ ?_
  · intro x hx hx0
    have hc : x.1 * x.2 ∣ n ∧ x.1.Coprime x.2 ∧ g.Coprime x.1 ∧ g.Coprime x.2 := by
      by_contra hc
      exact hx0 (if_neg hc)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (primeFactors_subset_eligible (by omega)
        (dvd_of_mul_right_dvd hc.1) hc.2.2.1),
       Finset.mem_powerset.mpr (primeFactors_subset_eligible (by omega)
        (dvd_of_mul_left_dvd hc.1) hc.2.2.2)⟩
  · intro x hx hx0 y hy hy0 hxy
    have hs (a b : ℕ)
        (hz : (if a * b ∣ n ∧ a.Coprime b ∧ g.Coprime a ∧ g.Coprime b
          then μ a * μ b else 0) ≠ 0) : Squarefree a ∧ Squarefree b := by
      split_ifs at hz with hc
      · exact ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (left_ne_zero_of_mul hz),
          ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (right_ne_zero_of_mul hz)⟩
      · exact (hz rfl).elim
    obtain ⟨hxa, hxb⟩ := hs x.1 x.2 hx0
    obtain ⟨hya, hyb⟩ := hs y.1 y.2 hy0
    obtain ⟨hxy1, hxy2⟩ := Prod.mk.inj hxy
    apply Prod.ext
    · rw [← Nat.prod_primeFactors_of_squarefree hxa, ← Nat.prod_primeFactors_of_squarefree hya,
        hxy1]
    · rw [← Nat.prod_primeFactors_of_squarefree hxb, ← Nat.prod_primeFactors_of_squarefree hyb,
        hxy2]
  · intro q hq hq0
    obtain ⟨hR, hT⟩ := Finset.mem_product.mp hq
    have hR := Finset.mem_powerset.mp hR
    have hT := Finset.mem_powerset.mp hT
    have hc : Disjoint q.1 q.2 ∧ (∏ p ∈ q.1, p) ≤ L ∧ (∏ p ∈ q.2, p) ≤ V := by
      by_contra hc
      exact hq0 (if_neg hc)
    have hRp (p : ℕ) (hp : p ∈ q.1) : p.Prime := prime_of_eligible (hR hp)
    have hTp (p : ℕ) (hp : p ∈ q.2) : p.Prime := prime_of_eligible (hT hp)
    have hRpF := Nat.primeFactors_prod hRp
    have hTpF := Nat.primeFactors_prod hTp
    have hab : (∏ p ∈ q.1, p).Coprime (∏ p ∈ q.2, p) := by
      apply (Nat.disjoint_primeFactors (prod_eligible_pos hR).ne' (prod_eligible_pos hT).ne').mp
      simpa only [hRpF, hTpF] using hc.1
    refine ⟨(∏ p ∈ q.1, p, ∏ p ∈ q.2, p), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨prod_eligible_pos hR, hc.2.1⟩,
       Finset.mem_Icc.mpr ⟨prod_eligible_pos hT, hc.2.2⟩⟩, ?_, Prod.ext hRpF hTpF⟩
    rw [if_pos ⟨prod_pair_dvd hR hT hc.1, hab,
      coprime_prod_eligible hR, coprime_prod_eligible hT⟩,
      sign_prod_primes hRp, sign_prod_primes hTp]
    simpa only [if_pos hc] using hq0
  · intro x hx hx0
    obtain ⟨hxa, hxb⟩ := Finset.mem_product.mp hx
    have hc : x.1 * x.2 ∣ n ∧ x.1.Coprime x.2 ∧ g.Coprime x.1 ∧ g.Coprime x.2 := by
      by_contra hc
      exact hx0 (if_neg hc)
    rw [if_pos hc] at hx0 ⊢
    have ha := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (left_ne_zero_of_mul hx0)
    have hb := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (right_ne_zero_of_mul hx0)
    rw [if_pos ⟨hc.2.1.disjoint_primeFactors,
      by simpa only [Nat.prod_primeFactors_of_squarefree ha] using (Finset.mem_Icc.mp hxa).2,
      by simpa only [Nat.prod_primeFactors_of_squarefree hb] using (Finset.mem_Icc.mp hxb).2⟩]
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree ha, ← Nat.prod_primeFactors_of_squarefree hb]
    rw [sign_prod_primes (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp),
      sign_prod_primes (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp)]

private theorem subsetCoefficient_eq_cutoffs {S : Finset ℕ} {L V : ℕ}
    (hLV : ∀ R ⊆ S, ∀ T ⊆ S, Disjoint R T →
      (∏ p ∈ R, p) ≤ L ∨ (∏ p ∈ T, p) ≤ V) :
    subsetCoefficient S L V = sign S *
      ((if (∏ p ∈ S, p) ≤ L then 1 else 0) +
       (if (∏ p ∈ S, p) ≤ V then 1 else 0) - 1) := by
  let f (R : Finset ℕ) : ℤ := if (∏ p ∈ R, p) ≤ L then 1 else 0
  let h (T : Finset ℕ) : ℤ := if (∏ p ∈ T, p) ≤ V then 1 else 0
  have hp (R : Finset ℕ) (hR : R ∈ S.powerset) (T : Finset ℕ) (hT : T ∈ S.powerset) :
      (if Disjoint R T ∧ (∏ p ∈ R, p) ≤ L ∧ (∏ p ∈ T, p) ≤ V then sign R * sign T else 0) =
        (if Disjoint R T then sign R * sign T * f R else 0) +
        (if Disjoint R T then sign R * sign T * h T else 0) -
        (if Disjoint R T then sign R * sign T * 1 else 0) := by
    by_cases hd : Disjoint R T
    · have hb := hLV R (Finset.mem_powerset.mp hR) T (Finset.mem_powerset.mp hT) hd
      dsimp [f, h]
      split_ifs <;> simp_all
    · simp [hd]
  have hswap : (∑ R ∈ S.powerset, ∑ T ∈ S.powerset,
        if Disjoint R T then sign R * sign T * h T else 0) = sign S * h S := by
    rw [Finset.sum_comm]
    convert sum_disjoint_weight S h using 1
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro R _
    simp only [disjoint_comm]
    split_ifs <;> ring
  unfold subsetCoefficient
  rw [Finset.sum_congr rfl (fun R hR ↦ Finset.sum_congr rfl (fun T hT ↦ hp R hR T hT))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_disjoint_weight, hswap, sum_disjoint_weight]
  dsimp [f, h]
  ring

/-- Below the omitted product range, all coprime divisor multiplicities cancel exactly; the two radical cutoff comparisons and the remaining sign are retained. -/
theorem coefficient_eq_radical_cutoffs (g : ℕ) {L V n : ℕ} (hn : 1 ≤ n) (hcut : n ≤ L * V) :
    coefficient g L V n = μ (eligibleRadical g n) *
      ((if eligibleRadical g n ≤ L then 1 else 0) +
       (if eligibleRadical g n ≤ V then 1 else 0) - 1) := by
  rw [coefficient_eq_subsetCoefficient g L V hn, subsetCoefficient_eq_cutoffs]
  · rw [eligibleRadical, sign_prod_primes (fun _ hp ↦ prime_of_eligible hp)]
  · intro R hR T hT hRT
    have hp := Nat.le_of_dvd hn (prod_pair_dvd hR hT hRT)
    by_contra hc
    push Not at hc
    nlinarith

/-- For equal cutoffs the surviving coefficient is precisely the eligible-radical Moebius sign, reversed outside that radical cutoff. -/
theorem coefficient_square_eq_signed_radical (g : ℕ) {N n : ℕ}
    (hn : 1 ≤ n) (hcut : n ≤ N ^ 2) :
    coefficient g N N n =
      if eligibleRadical g n ≤ N then μ (eligibleRadical g n) else -μ (eligibleRadical g n) := by
  rw [coefficient_eq_radical_cutoffs g hn (by simpa only [pow_two] using hcut)]
  split_ifs <;> ring

/-- The complete rectangular coprime divisor coefficient has absolute value at most one throughout the product bulk, independently of every cutoff and the gcd. -/
theorem abs_coefficient_le_one (g : ℕ) {L V n : ℕ} (hn : 1 ≤ n) (hcut : n ≤ L * V) :
    |coefficient g L V n| ≤ 1 := by
  rw [coefficient_eq_radical_cutoffs g hn hcut]
  have hm := ArithmeticFunction.abs_moebius_le_one (n := eligibleRadical g n)
  split_ifs <;> simp_all

/-- Outside the product bulk, the finite number of retained divisor pairs still supplies a uniform coefficient bound. -/
theorem abs_coefficient_le_cutoffs (g L V n : ℕ) :
    |coefficient g L V n| ≤ (L : ℤ) * V := by
  unfold coefficient
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 L, ∑ b ∈ Finset.Icc 1 V,
        |if a * b ∣ n ∧ a.Coprime b ∧ g.Coprime a ∧ g.Coprime b then μ a * μ b else 0| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a ∈ Finset.Icc 1 L, ∑ _b ∈ Finset.Icc 1 V, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · rw [abs_mul]
        exact mul_le_one₀ (ArithmeticFunction.abs_moebius_le_one (n := a))
          (abs_nonneg _) (ArithmeticFunction.abs_moebius_le_one (n := b))
      · norm_num
    _ = _ := by simp [Nat.card_Icc]

end

end RiemannGaussian.EtaCoprimeRadical
