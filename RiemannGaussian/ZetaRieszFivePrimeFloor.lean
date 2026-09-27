/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeFloor

/-!
# A two-largest-prime upper bound for the entire five-prime class

The signed divisor inequality bounds the positive coefficient by two
simultaneous logarithmic gaps. It is used on the actual residual atoms
without completing a cofactor or discarding favorable observations.
-/

namespace RiemannGaussian.ZetaRieszFivePrimeFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszCutoffProfile
open ZetaRieszReflectedLinear ZetaRieszPrimeEndpoint ZetaRieszFourPrimeFloor


set_option maxHeartbeats 8000000 in
/-- The six pair hinges share a single total-excess budget. -/
private theorem pair_four {a b c d D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (haD : a ≤ D) (hbD : b ≤ D) (hcD : c ≤ D) (hdD : d ≤ D)
    (hlo : D ≤ a+b+c+d) (hhi : a+b+c+d ≤ 2*D) :
    max 0 (a+b-D)+max 0 (a+c-D)+max 0 (a+d-D)+
    max 0 (b+c-D)+max 0 (b+d-D)+max 0 (c+d-D) ≤ a+b+c+d-D := by
  simp only [max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 16000000 in
/-- The ten pair hinges share a single total-excess budget. -/
private theorem pair_five {a b c d e D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (haD : a ≤ D) (hbD : b ≤ D) (hcD : c ≤ D) (hdD : d ≤ D) (heD : e ≤ D)
    (hlo : D ≤ a+b+c+d+e) (hhi : a+b+c+d+e ≤ 2*D) :
    max 0 (a+b-D)+max 0 (a+c-D)+max 0 (a+d-D)+max 0 (a+e-D)+
    max 0 (b+c-D)+max 0 (b+d-D)+max 0 (b+e-D)+
    max 0 (c+d-D)+max 0 (c+e-D)+max 0 (d+e-D) ≤ a+b+c+d+e-D := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The central four-prime chamber is nonpositive, including all pair
hinges. This is a signed inequality, not an absolute divisor estimate. -/
theorem four_difference_central {a b c p D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (haD : a ≤ D) (hbD : b ≤ D) (hcD : c ≤ D) (hpD : p ≤ D)
    (htlo : 2*D ≤ a+b+c+p) (hthi : a+b+c+p ≤ 3*D) :
    tripleDifference a b c D-tripleDifference a b c (D-p) ≤ 0 := by
  have hh := pair_four (a := D-a) (b := D-b) (c := D-c) (d := D-p) (D := D)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hD : 0 ≤ D := ha.trans haD
  simp only [tripleDifference,primePairTent]
  rw [max_eq_right (by linarith : 0 ≤ D),
    max_eq_right (by linarith : 0 ≤ D-a),
    max_eq_right (by linarith : 0 ≤ D-b),
    max_eq_right (by linarith : 0 ≤ D-c),
    max_eq_left (by linarith : D-c-a-b ≤ 0),
    max_eq_right (by linarith : 0 ≤ D-p),
    max_eq_left (by linarith : D-p-a-b ≤ 0),
    max_eq_left (by linarith : D-p-c-a ≤ 0),
    max_eq_left (by linarith : D-p-c-b ≤ 0),
    max_eq_left (by linarith : D-p-c-a-b ≤ 0)]
  ring_nf at hh ⊢
  linarith only [hh]

/-- With all five prime logs below the reflected cutoff, cancellation
of the singleton and pair divisors makes the response nonpositive. -/
theorem five_difference_small {a b c p q D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (haD : a ≤ D) (hbD : b ≤ D) (hcD : c ≤ D) (hpD : p ≤ D) (hqD : q ≤ D)
    (htlo : 3*D ≤ a+b+c+p+q) (hthi : a+b+c+p+q ≤ 4*D) :
    (tripleDifference a b c D-tripleDifference a b c (D-p))-
      (tripleDifference a b c (D-q)-tripleDifference a b c (D-q-p)) ≤ 0 := by
  have hh := pair_five (a := D-a) (b := D-b) (c := D-c) (d := D-p) (e := D-q) (D := D)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  have hD : 0 ≤ D := ha.trans haD
  simp only [tripleDifference,primePairTent]
  rw [max_eq_right (by linarith : 0 ≤ D),
    max_eq_right (by linarith : 0 ≤ D-a),
    max_eq_right (by linarith : 0 ≤ D-b),
    max_eq_right (by linarith : 0 ≤ D-c),
    max_eq_left (by linarith : D-c-a-b ≤ 0),
    max_eq_right (by linarith : 0 ≤ D-p),
    max_eq_left (by linarith : D-p-a-b ≤ 0),
    max_eq_left (by linarith : D-p-c-a ≤ 0),
    max_eq_left (by linarith : D-p-c-b ≤ 0),
    max_eq_left (by linarith : D-p-c-a-b ≤ 0),
    max_eq_right (by linarith : 0 ≤ D-q),
    max_eq_left (by linarith : D-q-a-b ≤ 0),
    max_eq_left (by linarith : D-q-c-a ≤ 0),
    max_eq_left (by linarith : D-q-c-b ≤ 0),
    max_eq_left (by linarith : D-q-c-a-b ≤ 0),
    max_eq_left (by linarith : D-q-p-a ≤ 0),
    max_eq_left (by linarith : D-q-p-b ≤ 0),
    max_eq_left (by linarith : D-q-p-a-b ≤ 0),
    max_eq_left (by linarith : D-q-p-c ≤ 0),
    max_eq_left (by linarith : D-q-p-c-a ≤ 0),
    max_eq_left (by linarith : D-q-p-c-b ≤ 0),
    max_eq_left (by linarith : D-q-p-c-a-b ≤ 0)]
  ring_nf at hh ⊢
  linarith only [hh]

/-- Removing an actual squarefree prime retains its exact cofactor
support and logarithm; no prime interval or density is substituted. -/
private theorem prime_cofactor {n P : ℕ} (hs : Squarefree n) (hP : P ∈ n.primeFactors) :
    ∃ a : ℕ, n = P*a ∧ Squarefree (P*a) ∧ a.primeFactors = n.primeFactors.erase P ∧
      Real.log n = Real.log P+Real.log a := by
  let a := ∏ p ∈ n.primeFactors.erase P, p
  have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
  have he : n = P*a := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Finset.mul_prod_erase _ _ hP).symm
  have hsp : Squarefree (P*a) := he ▸ hs
  refine ⟨a,he,hsp,hfa,?_⟩
  rw [he,Nat.cast_mul,Real.log_mul
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hP).ne_zero)
    (by exact_mod_cast hsp.of_mul_right.ne_zero)]

/-- Every four-prime response is nonpositive in the central third of
its physical logarithmic support. -/
theorem riesz_four_nonpos_central {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {D : ℝ} (hlo : Real.log n ≤ 3*D) (hhi : 3*D ≤ 2*Real.log n) :
    VaughanLogAverage.riesz D n ≤ 0 := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  suffices hm : ∀ E : ℝ, Real.log n ≤ 3*E → 2*E ≤ Real.log n →
      VaughanLogAverage.riesz E n ≤ 0 by
    by_cases hmid : 2*D ≤ Real.log n
    · exact hm D hlo hmid
    · have hr := VaughanLogAverage.riesz_reflection D hs hn1 hnp
      rw [moebius_eq_primeCount hs,hc] at hr
      norm_num at hr
      rw [← hr]
      exact hm (Real.log n-D) (by linarith) (by linarith)
  intro E hEl hEh
  obtain ⟨a,he,hsp,hfa,hlog⟩ := prime_cofactor hs hP
  have hac : a.primeFactors.card = 3 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
  have hp := Nat.prime_of_mem_primeFactors hP
  have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  by_cases hlarge : E ≤ Real.log P
  · have heq : VaughanLogAverage.riesz E n = VaughanLogAverage.riesz E a := by
      rw [he,riesz_prime_mul E hp hpn,
        ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith : E-Real.log P ≤ 0),sub_zero]
    rw [heq]
    exact (riesz_of_three_primeFactors_bounds hsp.of_mul_right hac (by linarith : Real.log a ≤ 2*E)).2
  · have hsmall : Real.log P ≤ E := le_of_lt (lt_of_not_ge hlarge)
    obtain ⟨b,c,d,hb,hc',hd,hbc,hbd,hcd,haeq⟩ := exists_three_primes hsp.of_mul_right hac
    have hlogs : Real.log a = Real.log b+Real.log c+Real.log d := by
      rw [haeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hc'.ne_zero hd.ne_zero)),Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hc'.ne_zero) (by exact_mod_cast hd.ne_zero)]
      ring
    have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ E := by
      have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv P
      exact (hmax p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)).trans hsmall
    have hbE := hbound b hb (by rw [haeq]; exact dvd_mul_right _ _)
    have hcE := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    have hdE := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
    rw [he,riesz_prime_mul E hp hpn,haeq,
      riesz_three_primes_eq_difference E hb hc' hd hbc hbd hcd,
      riesz_three_primes_eq_difference (E-Real.log P) hb hc' hd hbc hbd hcd]
    exact four_difference_central (Real.log_natCast_nonneg b) (Real.log_natCast_nonneg c)
      (Real.log_natCast_nonneg d) (Real.log_natCast_nonneg P) hbE hcE hdE hsmall
      (by linarith) (by linarith)

/-- When all four prime logs are below a cutoff at most a third of the
total log, only the singleton divisors survive. -/
theorem riesz_four_small_cutoff {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {E : ℝ} (hE : 0 ≤ E) (hsmall : Real.log P ≤ E) (hlog : 3*E ≤ Real.log n) :
    VaughanLogAverage.riesz E n = Real.log n-3*E := by
  obtain ⟨a,he,hsp,hfa,hln⟩ := prime_cofactor hs hP
  have hac : a.primeFactors.card = 3 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
  have hp := Nat.prime_of_mem_primeFactors hP
  have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  obtain ⟨b,c,d,hb,hc',hd,hbc,hbd,hcd,haeq⟩ := exists_three_primes hsp.of_mul_right hac
  have hlogs : Real.log a = Real.log b+Real.log c+Real.log d := by
    rw [haeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hc'.ne_zero hd.ne_zero)),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hc'.ne_zero) (by exact_mod_cast hd.ne_zero)]
    ring
  have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ E := by
    have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv P
    exact (hmax p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)).trans hsmall
  have hbE := hbound b hb (by rw [haeq]; exact dvd_mul_right _ _)
  have hcE := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hdE := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
  have heq : VaughanLogAverage.riesz E n = Real.log b+Real.log c+Real.log d+Real.log P-3*E := by
    rw [he,riesz_prime_mul E hp hpn,haeq,
      riesz_three_primes_eq_difference E hb hc' hd hbc hbd hcd,
      riesz_three_primes_eq_difference (E-Real.log P) hb hc' hd hbc hbd hcd,
      four_difference_singletons hE hbE hcE hdE hsmall (by linarith)]
  linarith

/-- The four-prime positive response above its first third is bounded
by both the radial and largest-prime gaps. -/
theorem riesz_four_upper_min_gap {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {D : ℝ} (hlo : Real.log n ≤ 3*D) :
    VaughanLogAverage.riesz D n ≤
      max 0 (min (3*D-2*Real.log n) (2*D-Real.log n-Real.log P)) := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  by_cases hhi : Real.log n ≤ D
  · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hs hn1 hnp hhi]
    exact le_max_left _ _
  by_cases hcentral : 3*D ≤ 2*Real.log n
  · exact (riesz_four_nonpos_central hs hc hP hmax hlo hcentral).trans (le_max_left _ _)
  have hgap := (riesz_four_signed_gap hs hc hP hmax (le_of_not_ge hhi)
    (le_of_not_ge hcentral)).2
  have hradial : VaughanLogAverage.riesz D n ≤ 3*D-2*Real.log n := by
    by_cases hlarge : Real.log n-D ≤ Real.log P
    · exact hgap.trans (max_le (by linarith) (by linarith))
    · have hr := VaughanLogAverage.riesz_reflection D hs hn1 hnp
      rw [moebius_eq_primeCount hs,hc] at hr
      norm_num at hr
      rw [← hr,riesz_four_small_cutoff hs hc hP hmax (by linarith)
        (le_of_not_ge hlarge) (by linarith)]
      linarith
  have hrmax : VaughanLogAverage.riesz D n ≤ max 0 (3*D-2*Real.log n) :=
    hradial.trans (le_max_right _ _)
  simpa only [max_min_distrib_left] using le_min hrmax hgap

/-- An upper bound for the complete five-prime divisor response after
reflection. Both large-prime gaps must be positive to permit a positive
coefficient. All small-prime and central-cutoff cases are included. -/
theorem riesz_five_upper_gap {n P Q : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    (hQ : Q ∈ (n/P).primeFactors)
    (hnext : ∀ p ∈ (n/P).primeFactors, Real.log p ≤ Real.log Q)
    {L : ℝ} (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    -VaughanLogAverage.riesz L n ≤
      max 0 (min (2*Real.log P+Real.log n-3*L)
        (Real.log P-Real.log Q+Real.log n-2*L)) := by
  obtain ⟨a,he,hsp,hfa,hlog⟩ := prime_cofactor hs hP
  have hp := Nat.prime_of_mem_primeFactors hP
  have hquot : n/P = a := by rw [he,Nat.mul_div_cancel_left a hp.pos]
  rw [hquot] at hQ hnext
  have hac : a.primeFactors.card = 4 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
  have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  let D := Real.log n-L
  have hD : 0 ≤ D := by dsimp [D]; linarith [Real.log_natCast_nonneg n]
  have hR : -VaughanLogAverage.riesz L n =
      VaughanLogAverage.riesz D a-VaughanLogAverage.riesz (D-Real.log P) a := by
    exact hr.symm.trans (by simpa only [← he] using riesz_prime_mul D hp hpn)
  by_cases hlarge : D ≤ Real.log P
  · rw [hR,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
      (by linarith : D-Real.log P ≤ 0),sub_zero]
    have hb := riesz_four_upper_min_gap hsp.of_mul_right hac hQ hnext
      (D := D) (by dsimp [D] at hlarge ⊢; linarith)
    have he1 : 3*D-2*Real.log a = 2*Real.log P+Real.log n-3*L := by dsimp [D]; linarith
    have he2 : 2*D-Real.log a-Real.log Q = Real.log P-Real.log Q+Real.log n-2*L := by
      dsimp [D]; linarith
    simpa only [he1,he2] using hb
  · have hsmall : Real.log P ≤ D := le_of_lt (lt_of_not_ge hlarge)
    obtain ⟨b,haeq,hsq,hfb,hloga⟩ := prime_cofactor hsp.of_mul_right hQ
    have hbcard : b.primeFactors.card = 3 := by rw [hfb,Finset.card_erase_of_mem hQ,hac]
    have hq := Nat.prime_of_mem_primeFactors hQ
    have hqn : ¬Q ∣ b := hq.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsq)
    obtain ⟨c,d,e,hc',hd,he',hcd,hce,hde,hbeq⟩ := exists_three_primes hsq.of_mul_right hbcard
    have hlogb : Real.log b = Real.log c+Real.log d+Real.log e := by
      rw [hbeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hc'.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hd.ne_zero he'.ne_zero)),Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hd.ne_zero) (by exact_mod_cast he'.ne_zero)]
      ring
    have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ D := by
      have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv P
      exact (hmax p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)).trans hsmall
    have hQD := hbound Q hq (by rw [haeq]; exact dvd_mul_right _ _)
    have hcb : c ∣ b := by rw [hbeq]; exact dvd_mul_right _ _
    have hdb : d ∣ b := by rw [hbeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    have heb : e ∣ b := by rw [hbeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    have hcD := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right hcb Q)
    have hdD := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right hdb Q)
    have heD := hbound e he' (by rw [haeq]; exact dvd_mul_of_dvd_right heb Q)
    have hbnd : -VaughanLogAverage.riesz L n ≤ 0 := by
      rw [hR,haeq,riesz_prime_mul D hq hqn,
        riesz_prime_mul (D-Real.log P) hq hqn,hbeq,
        riesz_three_primes_eq_difference D hc' hd he' hcd hce hde,
        riesz_three_primes_eq_difference (D-Real.log Q) hc' hd he' hcd hce hde,
        riesz_three_primes_eq_difference (D-Real.log P) hc' hd he' hcd hce hde,
        riesz_three_primes_eq_difference (D-Real.log P-Real.log Q) hc' hd he' hcd hce hde]
      exact five_difference_small (Real.log_natCast_nonneg c) (Real.log_natCast_nonneg d)
        (Real.log_natCast_nonneg e) (Real.log_natCast_nonneg Q) (Real.log_natCast_nonneg P)
        hcD hdD heD hQD hsmall (by dsimp [D]; linarith) (by dsimp [D]; linarith)
    exact hbnd.trans (le_max_left _ _)

/-- The independent arithmetic coefficient inequality for actual
squarefree five-prime labels, with the two largest factors specified. -/
theorem coefficient_five_upper_gap {n P Q : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    (hQ : Q ∈ (n/P).primeFactors)
    (hnext : ∀ p ∈ (n/P).primeFactors, Real.log p ≤ Real.log Q)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/L)*max 0 (min (2*Real.log P+Real.log n-3*L)
        (Real.log P-Real.log Q+Real.log n-2*L)) := by
  have hb := riesz_five_upper_gap hs hc hP hmax hQ hnext hLlo hLhi
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hgood : Squarefree n ∧ ¬n.Prime := ⟨hs,hnp⟩
  simp only [SquarefreeVaughanLogSource.coefficient,if_pos hgood,Complex.ofReal_re]
  convert mul_le_mul_of_nonneg_left hb (div_nonneg (Real.log_natCast_nonneg n) hL.le) using 1 <;> first | rfl | ring

/-- Canonical largest and second-largest factors discharge the ordering
premises. The original nonsquarefree coefficient is still exactly zero. -/
theorem actual_five_upper_gap {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/L)*max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
        (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)) := by
  by_cases hs : Squarefree n
  · have hn : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    have hP : largestPrime n ∈ n.primeFactors := by
      rw [largestPrime,dif_pos hn]
      exact Finset.max'_mem _ _
    have hmax (a p : ℕ) (hp : p ∈ a.primeFactors) : Real.log p ≤ Real.log (largestPrime a) := by
      have ha : a.primeFactors.Nonempty := ⟨p,hp⟩
      have hm : p ≤ largestPrime a := by
        rw [largestPrime,dif_pos ha]
        exact Finset.le_max' _ _ hp
      exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by exact_mod_cast hm)
    obtain ⟨a,he,_hsp,hfa,_hlog⟩ := prime_cofactor hs hP
    have hquot : n/largestPrime n = a := by
      calc
        n/largestPrime n = (largestPrime n*a)/largestPrime n := congrArg (fun k => k/largestPrime n) he
        _ = a := Nat.mul_div_cancel_left a (Nat.prime_of_mem_primeFactors hP).pos
    have hac : (n/largestPrime n).primeFactors.card = 4 := by
      rw [hquot,hfa,Finset.card_erase_of_mem hP,hc]
    have hQ := largestPrime_mem_of_four hac
    exact coefficient_five_upper_gap hs hc hP (hmax n) hQ (hmax _) hL hLlo hLhi
  · simp only [SquarefreeVaughanLogSource.coefficient,hs,false_and,if_false,Complex.zero_re]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _)

/-- Failure of either largest-prime gap makes the entire five-prime
arithmetic coefficient nonpositive, before applying phase or allocation. -/
theorem coefficient_five_nonpos {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n)
    (hgap : 2*Real.log (largestPrime n)+Real.log n ≤ 3*L ∨
      Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n ≤ 2*L) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ 0 := by
  have hb := actual_five_upper_gap hc hL hLlo hLhi
  have hm : min (2*Real.log (largestPrime n)+Real.log n-3*L)
      (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L) ≤ 0 := by
    rcases hgap with hgap | hgap
    · exact (min_le_left _ _).trans (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  simpa only [max_eq_left hm,mul_zero] using hb

/-- A positive five-prime coefficient requires both strict logarithmic
gaps. These are necessary conditions, not a converse sign assertion. -/
theorem coefficient_five_pos_gaps {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re) :
    3*L < 2*Real.log (largestPrime n)+Real.log n ∧
      2*L < Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n := by
  constructor
  · by_contra h
    exact (not_le_of_gt hpos) (coefficient_five_nonpos hc hL hLlo hLhi (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact (not_le_of_gt hpos) (coefficient_five_nonpos hc hL hLlo hLhi (Or.inr (le_of_not_gt h)))

/-- Uniform rational geometry of every positive five-prime coefficient
on the literal core. The moving length is not frozen at the saddle. -/
theorem positive_five_core_geometry {n N : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : (137/100 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    (hTlo : (39/20 : ℝ)*N ≤ Real.log n) (hThi : Real.log n ≤ (203/100 : ℝ)*N)
    (hpos : 0 < (SquarefreeVaughanLogSource.coefficient L n).re) :
    (104/203 : ℝ)*Real.log n < Real.log (largestPrime n) ∧
      (71/203 : ℝ)*Real.log n < Real.log (largestPrime n)-
        Real.log (largestPrime (n/largestPrime n)) := by
  have hg := coefficient_five_pos_gaps hc hL (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    (by nlinarith [Nat.cast_nonneg (α := ℝ) N]) hpos
  constructor <;> linarith

/-- Reuse the existing two-smallest-prime antichain estimate without
replacing the least prime log by its coarser mean-log bound. -/
theorem coefficient_five_le_three_least {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤ (Real.log n/L)*(3*Real.log n.minFac) := by
  by_cases hs : Squarefree n
  · have hn1 : n ≠ 1 := by intro he; simp [he] at hc
    have hnp : ¬n.Prime := by intro he; rw [he.primeFactors,Finset.card_singleton] at hc; omega
    obtain ⟨p,q,m,hp,hq,hpq,he,hm,hpm,hqm,hpmin,hqmin,hcount⟩ :=
      ZetaRieszSperner.exists_two_smallest_factorization hs (by omega)
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp,by rw [he]; exact dvd_mul_right _ _,hs.ne_zero⟩
    have hminmem : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime hn1,Nat.minFac_dvd n,hs.ne_zero⟩
    have hpmin_eq : p = n.minFac := le_antisymm (hpmin _ hminmem)
      (Nat.minFac_le_of_dvd hp.two_le (Nat.dvd_of_mem_primeFactors hpmem))
    have hr := ZetaRieszSperner.abs_riesz_two_primes_sperner L hp hq hpq hpm hqm hm hqmin
    rw [← he,hcount,hc,hpmin_eq] at hr
    norm_num at hr
    have hb : -VaughanLogAverage.riesz L n ≤ 3*Real.log n.minFac := by
      have hh := (neg_le_abs (VaughanLogAverage.riesz L n)).trans hr
      nlinarith only [hh]
    have hgood : Squarefree n ∧ ¬n.Prime := ⟨hs,hnp⟩
    simp only [SquarefreeVaughanLogSource.coefficient,if_pos hgood,Complex.ofReal_re]
    convert mul_le_mul_of_nonneg_left hb (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      using 1 <;> first | rfl | ring
  · simp only [SquarefreeVaughanLogSource.coefficient,hs,false_and,if_false,Complex.zero_re]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n.minFac))

/-- The positive five-prime debit is capped simultaneously by the
least prime and the two largest-prime gaps. The cap requires no additional
support, allocation, phase or prime-distribution assumption. -/
theorem actual_five_upper_clipped {n : ℕ} (hc : n.primeFactors.card = 5)
    {L : ℝ} (hL : 0 < L) (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) :
    (SquarefreeVaughanLogSource.coefficient L n).re ≤
      (Real.log n/L)*min (3*Real.log n.minFac)
        (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
          (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L))) := by
  rw [mul_min_of_nonneg _ _ (div_nonneg (Real.log_natCast_nonneg n) hL.le)]
  exact le_min (coefficient_five_le_three_least hc hL) (actual_five_upper_gap hc hL hLlo hLhi)

/-- An upper coefficient bound charges only its adverse observation;
all actual positive observations remain available as compensation. -/
private theorem real_upper_credit {c b x : ℝ} (hb : 0 ≤ b) (hc : c ≤ b) (hx : x ≤ 0) :
    max (c*x) 0-b*(-x) ≤ c*x := by
  have hm := mul_le_mul_of_nonpos_right hc hx
  have hs := mul_nonpos_of_nonneg_of_nonpos hb hx
  by_cases hp : 0 ≤ c*x
  · rw [max_eq_left hp]
    nlinarith only [hs]
  · rw [max_eq_right (le_of_not_ge hp)]
    nlinarith only [hm]

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- The full observed five-prime atom retains its actual positive credit.
Only the simultaneous-gap bound is paid on a negative cosine. The same
literal factorial, allocation and phase factors are kept. -/
theorem re_five_atom_ge_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) (y : ℝ)
    (hcos : Real.cos (y*Real.log n) ≤ 0) :
    max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
      weight A N n*(Real.log n/L)*
        min (3*Real.log n.minFac)
        (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
          (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)))*
        (-Real.cos (y*Real.log n)) ≤
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hb := actual_five_upper_clipped hc hL hLlo hLhi
  have hm := mul_le_mul_of_nonneg_left
    (real_upper_credit (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (le_min (mul_nonneg (by norm_num) (Real.log_natCast_nonneg n.minFac))
        (le_max_left _ _))) hb hcos) (weight_nonneg A N n)
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at hm
  simpa only [re_residual_atom,mul_assoc] using hm

/-- Every balanced five-prime label is favorable on negative cosine
observations in the original core length regime. -/
theorem re_five_atom_nonneg_of_gap (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 5) {L : ℝ} (hL : 0 < L)
    (hLlo : 2*Real.log n ≤ 3*L) (hLhi : 4*L ≤ 3*Real.log n) (y : ℝ)
    (hcos : Real.cos (y*Real.log n) ≤ 0)
    (hgap : 2*Real.log (largestPrime n)+Real.log n ≤ 3*L ∨
      Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n ≤ 2*L) :
    0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [re_residual_atom]
  exact mul_nonneg (weight_nonneg A N n)
    (mul_nonneg_of_nonpos_of_nonpos (coefficient_five_nonpos hc hL hLlo hLhi hgap) hcos)

/-- Four-prime terms and negative-cosine five-prime terms are bounded
in the SAME finite sum, preserving all other signed observations and
all actual positive credit. No population is removed or spent twice. -/
theorem re_sum_ge_four_five_credit (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 →
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if n.primeFactors.card = 4 then
      max (f n).re 0-weight A N n*(Real.log n/L)*
        max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n))
      else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
        max (f n).re 0-weight A N n*(Real.log n/L)*
          min (3*Real.log n.minFac)
          (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
            (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)))*
          (-Real.cos (y*Real.log n))
      else (f n).re) ≤ (∑ n ∈ S, f n).re := by
  dsimp only
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  split_ifs with hfour hfive
  · have hw := hwindow n hn (Or.inl hfour)
    exact re_four_atom_ge_keep_positive A N hfour hL hw.1 hw.2.1 y
  · have hw := hwindow n hn (Or.inr hfive.1)
    exact re_five_atom_ge_keep_positive A N hfive.1 hL hw.2.1 hw.2.2 y hfive.2
  · exact le_rfl

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint

/-- The original core satisfies every geometric premise of the joint
four/five-prime inequality eventually, uniformly in height and count
endpoint. The displayed signed budget is still an unpaid arithmetic
quantity, not a numerical floor for the entire carrier. -/
theorem eventually_re_core_ge_four_five_credit {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ),
      let L := SquarefreeVaughanLogSource.length u N
      let A := intermediatePrimes u N
      let S := coreBand u N K
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if n.primeFactors.card = 4 then
        max (f n).re 0-weight A N n*(Real.log n/L)*
          max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n))
        else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
          max (f n).re 0-weight A N n*(Real.log n/L)*
            min (3*Real.log n.minFac)
            (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
              (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)))*
            (-Real.cos (y*Real.log n))
        else (f n).re) ≤ ((u : ℂ)^(N+1)*coreResponse u y N K).re := by
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hL,eventually_ge_atTop (2 : ℕ)] with N hlow hN K y
  have hupp : SquarefreeVaughanLogSource.length u N ≤ (7/5 : ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) N]
  have hwindow (n : ℕ) (hn : n ∈ coreBand u N K)
      (_hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5) :
      SquarefreeVaughanLogSource.length u N ≤ Real.log n ∧
        2*Real.log n ≤ 3*SquarefreeVaughanLogSource.length u N ∧
          4*SquarefreeVaughanLogSource.length u N ≤ 3*Real.log n := by
    have hw := (Finset.mem_filter.mp hn).2
    constructor
    · nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := re_sum_ge_four_five_credit (coreBand u N K) (intermediatePrimes u N) N
    (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  simpa only [coreResponse,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using hm

end
end RiemannGaussian.ZetaRieszFivePrimeFloor
