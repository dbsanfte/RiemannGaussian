import CheckAlpogeCubicFourFactors
import Mathlib.NumberTheory.Bertrand

/-! # Cancellation by the squarefree product of the small prime divisors -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real ZetaVaughanReduction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta
  ArithmeticFunction.Omega

/-- The distinct primes dividing the tested integer that are at most n. -/
def smallPrimeFactors (n t : ℕ) := t.primeFactors.filter (· ≤ n)

/-- Product of the distinct small prime divisors, each taken once. -/
def smallPrimeRadical (n t : ℕ) := ∏ q ∈ smallPrimeFactors n t, q

private theorem smallPrimeRadical_pos (n t : ℕ) : 0 < smallPrimeRadical n t :=
  prod_pos fun _ h => Nat.pos_of_mem_primeFactors (mem_filter.mp h).1

private theorem smallPrimeRadical_dvd (n t : ℕ) : smallPrimeRadical n t ∣ t :=
  (prod_dvd_prod_of_subset _ _ id (filter_subset _ _)).trans t.prod_primeFactors_dvd

private theorem smallPrimeFactors_mono {n t u : ℕ} (htu : t ∣ u) (hu : u ≠ 0) :
    smallPrimeFactors n t ⊆ smallPrimeFactors n u := fun _ h =>
  mem_filter.mpr ⟨Nat.primeFactors_mono htu hu (mem_filter.mp h).1,(mem_filter.mp h).2⟩

private theorem smallPrimeRadical_le_of_dvd {n t u : ℕ} (htu : t ∣ u) (hu : u ≠ 0) :
    smallPrimeRadical n t ≤ smallPrimeRadical n u := Nat.le_of_dvd (smallPrimeRadical_pos _ _)
  (prod_dvd_prod_of_subset _ _ id (smallPrimeFactors_mono htu hu))

/-- Prime multiplicities and prime divisors above the cutoff do not change
the truncated Möbius sum. -/
theorem truncatedMoebiusSum_radical {n t : ℕ} (ht : 0<t) :
    truncatedMoebiusSum n t = truncatedMoebiusSum n (smallPrimeRadical n t) := by
  rw [truncatedMoebiusSum_apply,truncatedMoebiusSum_apply]
  symm
  apply sum_subset
  · intro d hd
    obtain ⟨hd,hn⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans
      (smallPrimeRadical_dvd n t),ht.ne'⟩,hn⟩
  · intro d hd hmiss
    obtain ⟨hd,hdn⟩ := mem_filter.mp hd
    by_cases hs : Squarefree d
    · exfalso
      apply hmiss
      have hsub : d.primeFactors ⊆ smallPrimeFactors n t := fun q h =>
        mem_filter.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) ht.ne' h,
          (Nat.le_of_mem_primeFactors h).trans hdn⟩
      have hv := prod_dvd_prod_of_subset _ _ id hsub
      change (∏ q ∈ d.primeFactors, q) ∣ smallPrimeRadical n t at hv
      rw [Nat.prod_primeFactors_of_squarefree hs] at hv
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hv,(smallPrimeRadical_pos _ _).ne'⟩,hdn⟩
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]

/-- Complete divisor cancellation whenever the squarefree product fits.
The only surviving value is one on the rough integers. -/
theorem truncatedMoebiusSum_of_radical_le {n t : ℕ} (ht : 0<t) (h : smallPrimeRadical n t ≤ n) :
    truncatedMoebiusSum n t = if smallPrimeFactors n t = ∅ then 1 else 0 := by
  let R := smallPrimeRadical n t
  have hR : 0 < R := smallPrimeRadical_pos _ _
  have hset : R.divisors.filter (· ≤ n) = R.divisors :=
    filter_eq_self.mpr fun _ hd => (Nat.le_of_dvd hR (Nat.dvd_of_mem_divisors hd)).trans h
  rw [truncatedMoebiusSum_radical ht,truncatedMoebiusSum_apply,hset]
  have he := congrArg (fun f : ArithmeticFunction ℝ => f R)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at he
  change (∑ d ∈ R.divisors, (μ d:ℝ)) = (1:ArithmeticFunction ℝ) R at he
  rw [he]
  by_cases hh : smallPrimeFactors n t = ∅
  · simp [hh,R,smallPrimeRadical]
  · have hne : R ≠ 1 := by
      obtain ⟨q,hq⟩ := Finset.nonempty_iff_ne_empty.mpr hh
      have hd : q ∣ R := dvd_prod_of_mem id hq
      have hp := Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1
      exact fun h1 => hp.ne_one (Nat.dvd_one.mp (h1 ▸ hd))
    simp [hh,ArithmeticFunction.one_apply_ne hne]

/-- With precisely two distinct small primes the remaining Möbius sign is
negative exactly when their product crosses the cutoff. -/
theorem truncatedMoebiusSum_of_pair {n t a b : ℕ} (ht : 0<t) (hab : a ≠ b)
    (hS : smallPrimeFactors n t = {a,b}) :
    truncatedMoebiusSum n t = if n<a*b then -1 else 0 := by
  have ha : a ∈ smallPrimeFactors n t := by simp [hS]
  have hb : b ∈ smallPrimeFactors n t := by simp [hS]
  have hpa := Nat.prime_of_mem_primeFactors (mem_filter.mp ha).1
  have hpb := Nat.prime_of_mem_primeFactors (mem_filter.mp hb).1
  have han := (mem_filter.mp ha).2
  have hbn := (mem_filter.mp hb).2
  have hR : smallPrimeRadical n t = a*b := by simp [smallPrimeRadical,hS,hab]
  by_cases h : n<a*b
  · rw [ite_eq_left h,truncatedMoebiusSum_radical ht,hR,truncatedMoebiusSum_apply]
    have hdiv : (a*b).divisors.filter (· ≤ n) = {1,a,b} := by
      ext d
      rw [Nat.divisors_mul,hpa.divisors,hpb.divisors]
      simp [Finset.mem_mul]
      grind [hpa.one_le]
    rw [hdiv]
    simp [hab,hpa.ne_one.symm,hpb.ne_one.symm,ArithmeticFunction.moebius_apply_prime hpa,
      ArithmeticFunction.moebius_apply_prime hpb]
  · rw [ite_eq_right h,truncatedMoebiusSum_of_radical_le ht (hR.le.trans (Nat.le_of_not_gt h))]
    simp [hS]

private theorem smallPrimeFactors_nonempty_iff {n t : ℕ} (ht : 0<t) :
    (smallPrimeFactors n t).Nonempty ↔ ¬t.Coprime n.factorial := by
  rw [Nat.Prime.not_coprime_iff_dvd]
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨hqt,hqn⟩ := mem_filter.mp hq
    have hp := Nat.prime_of_mem_primeFactors hqt
    exact ⟨q,hp,Nat.dvd_of_mem_primeFactors hqt,hp.dvd_factorial.mpr hqn⟩
  · rintro ⟨q,hq,hd,hf⟩
    exact ⟨q,mem_filter.mpr ⟨hq.mem_primeFactors hd ht.ne',hq.dvd_factorial.mp hf⟩⟩

private theorem radical_le_of_card_le_one {n t : ℕ} (hn : 1 ≤ n)
    (h : (smallPrimeFactors n t).card ≤ 1) : smallPrimeRadical n t ≤ n := by
  by_cases hz : smallPrimeFactors n t = ∅
  · simpa [smallPrimeRadical,hz] using hn
  obtain ⟨a,ha⟩ := card_eq_one.mp (show (smallPrimeFactors n t).card=1 by
    have := card_pos.mpr (nonempty_iff_ne_empty.mpr hz); omega)
  have ham : a ∈ smallPrimeFactors n t := by simp [ha]
  simpa [smallPrimeRadical,ha] using (mem_filter.mp ham).2

private theorem smallPrimeFactors_card_of_mangoldt {v : ℕ} (n : ℕ) (h : Λ v ≠ 0) :
    (smallPrimeFactors n v).card ≤ 1 := by
  obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff _).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
  exact (card_filter_le _ _).trans_eq (by rw [Nat.primeFactors_prime_pow hk.ne' hq,card_singleton])

/-- A single Mangoldt divisor can remove at most one distinct small prime. -/
private theorem quotient_smallPrimeFactors_nonempty {n t v : ℕ}
    (hS : 2 ≤ (smallPrimeFactors n t).card) (hv : v ∈ t.divisors) (hw : Λ v ≠ 0) :
    (smallPrimeFactors n (t/v)).Nonempty := by
  obtain ⟨hd,ht⟩ := Nat.mem_divisors.mp hv
  have ht0 := Nat.pos_of_ne_zero ht
  have hv0 := Nat.pos_of_dvd_of_pos hd ht0
  have hq := Nat.div_pos (Nat.le_of_dvd ht0 hd) hv0
  by_contra! hz
  have he : smallPrimeFactors n t = smallPrimeFactors n v ∪ smallPrimeFactors n (t/v) := by
    unfold smallPrimeFactors
    conv_lhs => rw [← Nat.mul_div_cancel' hd,Nat.primeFactors_mul hv0.ne' hq.ne',filter_union]
  rw [hz,union_empty] at he
  have := smallPrimeFactors_card_of_mangoldt n hw
  rw [he] at hS
  omega

/-- The direct Mangoldt head on integers with a small prime divisor. -/
def cubicSmallPowerHead (n t : ℕ) : ℝ :=
  if ¬t.Coprime n.factorial ∧ ¬HasFourLargeFactors n t then Λ t-head n Λ t else 0

def cubicRadicalCoefficient (n t : ℕ) : ℝ :=
  cubicThreeFactorCoefficient n t - cubicSmallPowerHead n t

private theorem radicalCoefficient_on_small {n t : ℕ} (ht : 0<t)
    (hS : (smallPrimeFactors n t).Nonempty) (h4 : ¬HasFourLargeFactors n t) :
    cubicRadicalCoefficient n t = -truncatedMoebiusSum n t * roughPrimeLog n t -
      ∑ v ∈ t.divisors, if n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial
        then Λ v*truncatedMoebiusSum n (t/v) else 0 := by
  rw [cubicRadicalCoefficient,cubicSmallPowerHead,ite_eq_left
    ⟨(smallPrimeFactors_nonempty_iff ht).mp hS,h4⟩,cubicThreeFactorCoefficient,
    ite_eq_right h4,cubicRoughCoefficient]
  ring

private theorem radicalCoefficient_of_four {n t : ℕ} (h : HasFourLargeFactors n t) :
    cubicRadicalCoefficient n t=0 := by
  simp [cubicRadicalCoefficient,cubicThreeFactorCoefficient,cubicSmallPowerHead,h]

/-- For a nonempty small-prime radical below the cutoff the sole possible
loss comes from a power whose removal leaves a rough quotient. -/
theorem cubicRadicalCoefficient_of_radical_le {n t : ℕ} (ht : 0<t)
    (hS : (smallPrimeFactors n t).Nonempty) (hR : smallPrimeRadical n t ≤ n) :
    cubicRadicalCoefficient n t = if HasFourLargeFactors n t then 0 else
      -(∑ v ∈ t.divisors, if n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial ∧
        (t/v).Coprime n.factorial then Λ v else 0) := by
  by_cases h4 : HasFourLargeFactors n t
  · simp [h4,radicalCoefficient_of_four h4]
  rw [ite_eq_right h4,radicalCoefficient_on_small ht hS h4,truncatedMoebiusSum_of_radical_le ht hR,
    ite_eq_right hS.ne_empty,neg_zero,zero_mul,zero_sub]
  congr 1
  apply sum_congr rfl
  intro v hv
  have hd := Nat.dvd_of_mem_divisors hv
  have hq := Nat.div_pos (Nat.le_of_dvd ht hd) (Nat.pos_of_dvd_of_pos hd ht)
  have hr := (smallPrimeRadical_le_of_dvd (Nat.div_dvd_of_dvd hd) ht.ne').trans hR
  have he : smallPrimeFactors n (t/v)=∅ ↔ (t/v).Coprime n.factorial := by
    exact not_iff_not.mp (nonempty_iff_ne_empty.symm.trans (smallPrimeFactors_nonempty_iff hq))
  simp only [truncatedMoebiusSum_of_radical_le hq hr,he]
  split_ifs <;> simp_all

/-- Complete cancellation also holds for arbitrarily high prime exponents
when at least two small primes are present and their radical fits. -/
theorem cubicRadicalCoefficient_eq_zero_of_radical_le {n t : ℕ} (ht : 0<t)
    (hS : 2 ≤ (smallPrimeFactors n t).card) (hR : smallPrimeRadical n t ≤ n) :
    cubicRadicalCoefficient n t = 0 := by
  rw [cubicRadicalCoefficient_of_radical_le ht (card_pos.mp (by omega)) hR]
  split_ifs
  · rfl
  rw [neg_eq_zero]
  apply sum_eq_zero
  intro v hv
  split_ifs with h
  · by_contra hw
    have hd := Nat.dvd_of_mem_divisors hv
    have hq := Nat.div_pos (Nat.le_of_dvd ht hd) (Nat.pos_of_dvd_of_pos hd ht)
    exact (smallPrimeFactors_nonempty_iff hq).mp
      (quotient_smallPrimeFactors_nonempty hS hv hw) h.2.2.2
  · rfl

/-- With exactly two small primes the surviving coefficient is nonnegative.
The additional prime-power weight counts only powers whose
removal preserves both small primes. -/
theorem cubicRadicalCoefficient_of_pair {n t a b : ℕ} (hn : 1 ≤ n) (ht : 0<t)
    (hab : a ≠ b) (hS : smallPrimeFactors n t = {a,b}) :
    cubicRadicalCoefficient n t = if ¬HasFourLargeFactors n t ∧ n<a*b then
      roughPrimeLog n t + ∑ v ∈ t.divisors,
        if n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial ∧ smallPrimeFactors n (t/v)={a,b}
        then Λ v else 0 else 0 := by
  have hcard : (smallPrimeFactors n t).card=2 := by simp [hS,hab]
  by_cases h4 : HasFourLargeFactors n t
  · simp [h4,radicalCoefficient_of_four h4]
  by_cases hp : n<a*b
  · rw [ite_eq_left ⟨h4,hp⟩,radicalCoefficient_on_small ht (card_pos.mp (by omega)) h4,
      truncatedMoebiusSum_of_pair ht hab hS,ite_eq_left hp,neg_neg,one_mul,sub_eq_add_neg]
    congr 1
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro v hv
    by_cases hw : Λ v=0
    · simp [hw,ite_self]
    have hd := Nat.dvd_of_mem_divisors hv
    have hq := Nat.div_pos (Nat.le_of_dvd ht hd) (Nat.pos_of_dvd_of_pos hd ht)
    by_cases hqS : smallPrimeFactors n (t/v)={a,b}
    · rw [truncatedMoebiusSum_of_pair hq hab hqS,ite_eq_left hp]
      by_cases hh : n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial <;> simp [hqS,hh]
    · have hsub := smallPrimeFactors_mono (n := n) (Nat.div_dvd_of_dvd hd) ht.ne'
      have hlt := card_lt_card (ssubset_of_subset_of_ne hsub (by simpa only [hS] using hqS))
      have hr := radical_le_of_card_le_one (t := t/v) hn (by omega)
      have hpos := quotient_smallPrimeFactors_nonempty (hcard.ge) hv hw
      rw [truncatedMoebiusSum_of_radical_le hq hr,ite_eq_right hpos.ne_empty]
      simp [hqS]
  · have hr : smallPrimeRadical n t ≤ n := by
      simpa [smallPrimeRadical,hS,hab] using Nat.le_of_not_gt hp
    simp [hp,cubicRadicalCoefficient_eq_zero_of_radical_le ht hcard.ge hr]


theorem cubicRadicalCoefficient_pos_requires_radical {n t : ℕ} (hn : 1 ≤ n) (ht : 0<t)
    (hp : 0 < cubicRadicalCoefficient n t) :
    n < smallPrimeRadical n t ∧ 2 ≤ (smallPrimeFactors n t).card := by
  have hlarge : n < smallPrimeRadical n t := by
    by_contra! hR
    by_cases hS : (smallPrimeFactors n t).Nonempty
    · rw [cubicRadicalCoefficient_of_radical_le ht hS hR] at hp
      split_ifs at hp
      · exact (lt_irrefl _ hp)
      have hsum : 0 ≤ ∑ v ∈ t.divisors, if n<v ∧ v≤n^3 ∧ ¬v.Coprime n.factorial ∧
          (t/v).Coprime n.factorial then Λ v else 0 := sum_nonneg fun v _ => by
        split_ifs <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := v)]
      linarith only [hp,hsum]
    · have hc : t.Coprime n.factorial := by
        by_contra h
        exact hS ((smallPrimeFactors_nonempty_iff ht).mpr h)
      by_cases hnt : n<t
      · rw [cubicRadicalCoefficient,cubicSmallPowerHead,ite_eq_right (fun h => h.1 hc),sub_zero,
          cubicThreeFactorCoefficient_rough_eq hn hnt hc] at hp
        split_ifs at hp <;> linarith only [hp,ArithmeticFunction.vonMangoldt_le_log (n := t)]
      have h1 := Nat.eq_one_of_dvd_coprimes hc dvd_rfl (Nat.dvd_factorial ht (Nat.le_of_not_gt hnt))
      subst t
      by_cases h4 : HasFourLargeFactors n 1 <;>
        simp [cubicRadicalCoefficient,cubicSmallPowerHead,cubicThreeFactorCoefficient,
          cubicRoughCoefficient,roughPrimeLog,head,h4,hn] at hp
  exact ⟨hlarge,by
    by_contra! h
    exact (not_le.mpr hlarge) (radical_le_of_card_le_one hn (by omega))⟩

theorem smallPowerHead_response_bound {n : ℕ} (hn : 8 ≤ n) :
    |cubicWeightedResponse n (cubicSmallPowerHead n)| ≤ 2*((n:ℝ)*log (cubicSampleEnd n)) := by
  apply (cubicWeightedResponse_abs hn _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  have hz : cubicSmallPowerHead n 0 = 0 := by
    unfold cubicSmallPowerHead
    split_ifs <;> simp [head]
  rw [hz,abs_zero,zero_add]
  apply le_trans _ (small_base_prime_power_mass n _ (by unfold cubicSampleEnd; positivity))
  rw [sum_filter]
  apply sum_le_sum
  intro t _
  by_cases hc : t.Coprime n.factorial
  · simp [cubicSmallPowerHead,hc]
  · simp only [cubicSmallPowerHead,hc,not_false_eq_true,true_and,ite_true]
    split_ifs <;> by_cases hs : t ≤ n <;>
      simp [head,hs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        ArithmeticFunction.vonMangoldt_nonneg]

theorem cubicThreeFactorCoefficient_crossing_pair {n r a b : ℕ} (hn : 1 ≤ n) (hr : 0<r)
    (hrough : r.Coprime n.factorial) (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (han : a ≤ n) (hbn : b ≤ n) (hcross : n<a*b) (h4 : ¬HasFourLargeFactors n (a*b*r)) :
    cubicThreeFactorCoefficient n (a*b*r) = log r := by
  have hs : 0<a*b := Nat.mul_pos ha.pos hb.pos
  have hS : smallPrimeFactors n (a*b) = {a,b} := by
    simp [smallPrimeFactors,Nat.primeFactors_mul ha.ne_zero hb.ne_zero,ha.primeFactors,hb.primeFactors,han,hbn]
  have hSr : smallPrimeFactors n (a*b*r) = {a,b} := by
    have he : smallPrimeFactors n r = ∅ := by
      by_contra h
      exact (smallPrimeFactors_nonempty_iff hr).mp (nonempty_iff_ne_empty.mpr h) hrough
    change (a*b*r).primeFactors.filter (· ≤ n) = _
    rw [Nat.primeFactors_mul hs.ne' hr.ne',filter_union]
    change smallPrimeFactors n (a*b) ∪ smallPrimeFactors n r = _
    rw [he,union_empty,hS]
  have hz {t : ℕ} (h : smallPrimeFactors n t = {a,b}) : Λ t=0 := by
    by_contra hw
    have := smallPrimeFactors_card_of_mangoldt n hw
    simp [h,hab] at this
  have hprod := Nat.mul_le_mul han hbn
  have hs3 : a*b ≤ n^3 := by
    rw [pow_succ, pow_two]
    exact hprod.trans (Nat.le_mul_of_pos_right _ hn)
  have hp : a*b < (n+1)^2 := by nlinarith only [hprod]
  rw [cubicThreeFactorCoefficient,ite_eq_right h4,cubicRoughCoefficient_eq_on_rough_progression
    hs hs3 hrough,bilinear_mul_rough_below_pair hcross hp hr hrough,hz hSr,hz hS,
    truncatedMoebiusSum_of_pair hs hab hS,ite_eq_left hcross]
  ring

theorem no_four_of_le_fourth {n t : ℕ} (ht : t ≤ n^4) :
    ¬HasFourLargeFactors n t := by
  rintro ⟨a,b,c,d,ha,hb,hc,hd,he⟩
  have h4 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc) hd
  have hpow : n^4 < (n+1)^4 := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by decide)
  rw [show (n+1)^4=n.succ*n.succ*n.succ*n.succ by change (n+1)^4=(n+1)*(n+1)*(n+1)*(n+1); ring] at hpow
  exact (not_lt.mpr ht) (hpow.trans_le (h4.trans_eq he))

/-- The least prime strictly above half the cutoff gives a fixed, injective
partner r ↦ 2qr throughout a single sample. -/
def crossingPrime (n : ℕ) := Nat.find (Nat.exists_infinite_primes (n/2+1))

theorem crossingPrime_spec {n : ℕ} (hn : 8 ≤ n) :
    (crossingPrime n).Prime ∧ 2 < crossingPrime n ∧ crossingPrime n ≤ n ∧ n < 2*crossingPrime n := by
  obtain ⟨q,hq,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (n/2) (by omega)
  have hfound := Nat.find_spec (Nat.exists_infinite_primes (n/2+1))
  have hmin := Nat.find_min' (Nat.exists_infinite_primes (n/2+1)) (show n/2+1 ≤ q ∧ q.Prime from ⟨hl,hq⟩)
  change n/2+1 ≤ crossingPrime n ∧ (crossingPrime n).Prime at hfound
  change crossingPrime n ≤ q at hmin
  exact ⟨hfound.2,by omega,by omega,by omega⟩

/-- Rough semiprimes for which both members of the pair receive exactly half weight. -/
def matchedSemiprimes (n : ℕ) := (Ioc n (3*n^3/(2*crossingPrime n))).filter
  (fun r => r.Coprime n.factorial ∧ Ω r=2)

theorem matchedSemiprime_bounds {n r : ℕ} (hn : 8 ≤ n) (hr : r ∈ matchedSemiprimes n) :
    r ≤ 3*n^3 ∧ 2*crossingPrime n*r ≤ 3*n^3 := by
  have hq := (crossingPrime_spec hn).2.1
  have he := (Nat.le_div_iff_mul_le (by omega : 0<2*crossingPrime n)).mp (mem_Ioc.mp (mem_filter.mp hr).1).2
  rw [Nat.mul_comm r] at he
  exact ⟨(Nat.le_mul_of_pos_left r (by omega : 0<2*crossingPrime n)).trans he,he⟩

/-- The positive partner cancels the full logarithmic rough loss. Only the
von Mangoldt diagonal survives, which is zero for two distinct primes. -/
theorem matchedSemiprime_pair_sum {n r : ℕ} (hn : 8 ≤ n) (hr : r ∈ matchedSemiprimes n) :
    cubicThreeFactorCoefficient n r +
      cubicThreeFactorCoefficient n (2*crossingPrime n*r) = Λ r := by
  obtain ⟨hq,h2,hqn,hcross⟩ := crossingPrime_spec hn
  obtain ⟨hi,hc,hΩ⟩ := mem_filter.mp hr
  have hnr := (mem_Ioc.mp hi).1
  rw [cubicThreeFactorCoefficient_crossing_pair (by omega) (by omega) hc Nat.prime_two hq
    (by omega) (by omega) hqn hcross (no_four_of_le_fourth ((matchedSemiprime_bounds hn hr).2.trans (by
      rw [show n^4=n*n^3 by ring]; exact Nat.mul_le_mul_right _ (by omega)))),
    cubicThreeFactorCoefficient_rough_eq (by omega) hnr hc,ite_eq_left (Or.inl hΩ)]
  ring

/-- The matching covers the entire range up to one and a half times n²
for every sample, regardless of the location of the Bertrand prime. -/
theorem mem_matchedSemiprimes_of_le {n r : ℕ} (hn : 8 ≤ n) (hnr : n<r)
    (hc : r.Coprime n.factorial) (hΩ : Ω r=2) (hr : 2*r ≤ 3*n^2) :
    r ∈ matchedSemiprimes n := by
  obtain ⟨_,hq,hqn,_⟩ := crossingPrime_spec hn
  refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnr,(Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩,hc,hΩ⟩
  calc
    r*(2*crossingPrime n) = (2*r)*crossingPrime n := by ring
    _ ≤ (3*n^2)*n := Nat.mul_le_mul hr hqn
    _ = _ := by ring

private def matchedPartners (n : ℕ) := (matchedSemiprimes n).image (fun r => 2*crossingPrime n*r)

private theorem partner_not_mem {n r : ℕ} (hn : 8 ≤ n) :
    2*crossingPrime n*r ∉ matchedSemiprimes n := by
  intro h
  have hc := (mem_filter.mp h).2.1
  have he := Nat.eq_one_of_dvd_coprimes hc (show 2 ∣ 2*crossingPrime n*r by
    exact ⟨crossingPrime n*r,by ring⟩) (Nat.dvd_factorial (by decide) (by omega))
  omega

/-- After pairing, only the diagonal Mangoldt weight is kept at r.
The corresponding positive partner is removed. -/
def cubicMatchedCoefficient (n t : ℕ) : ℝ :=
  if t ∈ matchedSemiprimes n then Λ t else
    if t ∈ matchedPartners n then 0 else cubicThreeFactorCoefficient n t

theorem cubicMatchedCoefficient_eq_outside {n t : ℕ} (hs : t ∉ matchedSemiprimes n)
    (hp : ∀ r ∈ matchedSemiprimes n, 2*crossingPrime n*r ≠ t) :
    cubicMatchedCoefficient n t = cubicThreeFactorCoefficient n t := by
  rw [cubicMatchedCoefficient,ite_eq_right hs]
  exact ite_eq_right (fun h => by obtain ⟨r,hr,he⟩ := mem_image.mp h; exact hp r hr he)

theorem cubicMatchedResponse_eq {n : ℕ} (hn : 8 ≤ n) :
    cubicWeightedResponse n (cubicMatchedCoefficient n) =
      cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  let S := matchedSemiprimes n
  let P := matchedPartners n
  let U := Icc 0 (3*n^3)
  let Δ := fun t => cubicMatchedCoefficient n t - cubicThreeFactorCoefficient n t
  have hpos : 0 < 2*crossingPrime n := by have := (crossingPrime_spec hn).2.1; omega
  have hdisj : Disjoint S P := by
    apply disjoint_left.mpr
    intro t hs hp
    obtain ⟨r,_,rfl⟩ := mem_image.mp hp
    exact partner_not_mem hn hs
  have hsub : S ∪ P ⊆ U := by
    intro t ht
    refine mem_Icc.mpr ⟨Nat.zero_le _,?_⟩
    rcases mem_union.mp ht with hs | hp
    · exact (matchedSemiprime_bounds hn hs).1
    · obtain ⟨r,hr,rfl⟩ := mem_image.mp hp
      exact (matchedSemiprime_bounds hn hr).2
  have hoff (t : ℕ) (ht : t ∉ S ∪ P) : cubicMatchedCoefficient n t = cubicThreeFactorCoefficient n t := by
    exact (ite_eq_right (fun hs => ht (mem_union_left _ hs))).trans
      (ite_eq_right (fun hp => ht (mem_union_right _ hp)))
  have hzero : ∑ t ∈ S ∪ P, Δ t=0 := by
    rw [sum_union hdisj]
    unfold P matchedPartners
    rw [sum_image (fun a _ b _ he => Nat.eq_of_mul_eq_mul_left hpos he),← sum_add_distrib]
    apply sum_eq_zero
    intro r hr
    have hp : 2*crossingPrime n*r ∈ matchedPartners n := mem_image_of_mem _ hr
    have hs : r ∈ matchedSemiprimes n := hr
    simp only [Δ,cubicMatchedCoefficient,ite_eq_left hs,ite_eq_right (partner_not_mem hn),
      ite_eq_left hp]
    linarith only [matchedSemiprime_pair_sum hn hs]
  have hlo : (∑ t ∈ U, cubicMatchedCoefficient n t) = ∑ t ∈ U, cubicThreeFactorCoefficient n t := by
    apply sub_eq_zero.mp
    rw [← sum_sub_distrib]
    exact (sum_subset (f := Δ) hsub (fun t _ ht => sub_eq_zero.mpr (hoff t ht))).symm.trans hzero
  unfold cubicWeightedResponse
  rw [hlo]
  congr 1
  apply congrArg (cubicMean n)
  funext M
  apply sum_congr rfl
  intro t ht
  rw [hoff t (fun h => (not_le.mpr (mem_Ioc.mp ht).1) (mem_Icc.mp (hsub h)).2)]

/-- The window mass with disjoint equal-weight pairs cancelled exactly. -/
def cubicMatchedMassOn (m b : ℕ) :=
  ∑ n ∈ Icc m b, max (cubicSmoothMoments n - cubicWeightedResponse n (cubicMatchedCoefficient n)) 0 /
    (n:ℝ)^3

theorem cubicMatchedMassOn_eq {m b : ℕ} (hm : 8 ≤ m) :
    cubicMatchedMassOn m b = cubicThreeFactorMassOn m b := by
  apply sum_congr rfl
  intro n hn
  rw [cubicMatchedResponse_eq (hm.trans (mem_Icc.mp hn).1)]

theorem rh_of_cubicMatchedMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicMatchedMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicThreeFactorMassOn_powerWindows
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max A 8)
  exact ⟨m,by omega,(cubicMatchedMassOn_eq (by omega : 8 ≤ m)).ge.trans he⟩

end
end RiemannGaussian.AlpogeMined
