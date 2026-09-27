/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFourPrimeFloor
import RiemannGaussian.ZetaRieszFivePrimeFloor
import RiemannGaussian.ZetaRieszRadialCompensation

/-!
# The exact negative coefficient of the entire four-prime class

The largest-prime sign bound loses the excess of additional large primes.
The clipped prime-log sum below gives the exact negative part and a sharper
signed floor for the original atoms. No carrier or prime completion is changed.
-/

namespace RiemannGaussian.ZetaRieszFourPrimeReserve
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszCutoffProfile
open ZetaRieszReflectedLinear ZetaRieszPrimeEndpoint ZetaRieszFourPrimeFloor

/-- The pair tent is a positive clipped singleton balance. -/
theorem pair_tent_clipped_sum {a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D) :
    primePairTent a b D = max 0 (min D a+min D b-D) := by
  simp only [primePairTent,min_def,max_def]
  split_ifs <;> linarith

private theorem triple_cycle (a b c D : ℝ) :
    tripleDifference a b c D = tripleDifference b c a D := by
  unfold tripleDifference primePairTent
  ring_nf

private theorem triple_drop {a b c D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : D ≤ c) :
    tripleDifference a b c D = primePairTent a b D := by
  unfold tripleDifference
  have hz : primePairTent a b (D-c) = 0 := by
    simp only [primePairTent]
    rw [max_eq_left (by linarith : D-c ≤ 0),
      max_eq_left (by linarith : D-c-a ≤ 0),
      max_eq_left (by linarith : D-c-b ≤ 0),
      max_eq_left (by linarith : D-c-a-b ≤ 0)]
    ring
  rw [hz,sub_zero]

/-- The positive part of the three-leg difference is exactly its clipped
singleton balance, including all pair cutoffs and boundary equalities. -/
theorem triple_clipped_sum {a b c D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hD : 0 ≤ D) :
    min D a+min D b+min D c-2*D ≤ tripleDifference a b c D ∧
      max 0 (tripleDifference a b c D) = max 0 (min D a+min D b+min D c-2*D) := by
  have hlarge (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : D ≤ z) :
      min D x+min D y+min D z-2*D ≤ tripleDifference x y z D ∧
        max 0 (tripleDifference x y z D) = max 0 (min D x+min D y+min D z-2*D) := by
    rw [triple_drop hx hy hz,pair_tent_clipped_sum hx hy hD,min_eq_left hz,
      show min D x+min D y+D-2*D = min D x+min D y-D by ring]
    exact ⟨le_max_right _ _,max_eq_right (le_max_left _ _)⟩
  by_cases hcD : D ≤ c
  · exact hlarge a b c ha hb hcD
  by_cases haD : D ≤ a
  · have h := hlarge b c a hb hc haD
    rw [← triple_cycle a b c D] at h
    simpa only [add_comm,add_left_comm,add_assoc] using h
  by_cases hbD : D ≤ b
  · have h := hlarge c a b hc ha hbD
    rw [← triple_cycle b c a D,← triple_cycle a b c D] at h
    simpa only [add_comm,add_left_comm,add_assoc] using h
  have ha' : a ≤ D := le_of_not_ge haD
  have hb' : b ≤ D := le_of_not_ge hbD
  have hc' : c ≤ D := le_of_not_ge hcD
  rw [min_eq_right ha',min_eq_right hb',min_eq_right hc']
  have hlo : a+b+c-2*D ≤ tripleDifference a b c D := by
    by_cases htotal : a+b+c ≤ D
    · have hz : tripleDifference a b c D = 0 := by
        simp only [tripleDifference,primePairTent]
        rw [max_eq_right hD,
          max_eq_right (by linarith : 0 ≤ D-a),max_eq_right (by linarith : 0 ≤ D-b),
          max_eq_right (by linarith : 0 ≤ D-a-b),max_eq_right (by linarith : 0 ≤ D-c),
          max_eq_right (by linarith : 0 ≤ D-c-a),max_eq_right (by linarith : 0 ≤ D-c-b),
          max_eq_right (by linarith : 0 ≤ D-c-a-b)]
        ring
      rw [hz]
      linarith
    · simp only [tripleDifference,primePairTent]
      rw [max_eq_right hD,max_eq_right (by linarith : 0 ≤ D-a),
        max_eq_right (by linarith : 0 ≤ D-b),max_eq_right (by linarith : 0 ≤ D-c),
        max_eq_left (by linarith : D-c-a-b ≤ 0)]
      linarith [le_max_left 0 (D-a-b),le_max_left 0 (D-c-a),le_max_left 0 (D-c-b)]
  refine ⟨hlo,?_⟩
  by_cases hmid : a+b+c ≤ 2*D
  · rw [max_eq_left ((tripleDifference_bounds ha hb hc hmid).2),
      max_eq_left (by linarith : a+b+c-2*D ≤ 0)]
  · have he : tripleDifference a b c D = a+b+c-2*D := by
      simp only [tripleDifference,primePairTent]
      rw [max_eq_right hD,max_eq_right (by linarith : 0 ≤ D-a),
        max_eq_right (by linarith : 0 ≤ D-b),max_eq_right (by linarith : 0 ≤ D-c),
        max_eq_left (by linarith : D-a-b ≤ 0),max_eq_left (by linarith : D-c-a ≤ 0),
        max_eq_left (by linarith : D-c-b ≤ 0),max_eq_left (by linarith : D-c-a-b ≤ 0)]
      ring
    rw [he]

/-- Transfer the clipped singleton inequality to the literal squarefree
three-prime divisor sum, before multiplying by any carrier weight. -/
theorem riesz_three_clipped_sum {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 3) {D : ℝ} (hD : 0 ≤ D) :
    (∑ p ∈ n.primeFactors, min D (Real.log p))-2*D ≤ VaughanLogAverage.riesz D n ∧
      max 0 (VaughanLogAverage.riesz D n) =
        max 0 ((∑ p ∈ n.primeFactors, min D (Real.log p))-2*D) := by
  obtain ⟨p,q,r,hpq,hpr,hqr,he⟩ := Finset.card_eq_three.mp hc
  have hp : p ∈ n.primeFactors := by simp [he]
  have hq : q ∈ n.primeFactors := by simp [he]
  have hr : r ∈ n.primeFactors := by simp [he]
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hn : n = p*(q*r) := by
    simpa [he,hpq,hpr,hqr,mul_assoc] using (Nat.prod_primeFactors_of_squarefree hs).symm
  rw [show VaughanLogAverage.riesz D n = tripleDifference (Real.log p) (Real.log q) (Real.log r) D by
    rw [hn,riesz_three_primes_eq_difference D hp' hq' hr' hpq hpr hqr],he]
  simpa [hpq,hpr,hqr,add_assoc] using triple_clipped_sum
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) (Real.log_natCast_nonneg r) hD

/-- The entire positive Riesz response in the four-prime class is the
clipped singleton balance. The remaining subset hinges never enlarge its
positive part; this is an exact identity, not a triangle estimate. -/
theorem riesz_four_clipped_sum {n P : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 4) (hP : P ∈ n.primeFactors)
    (hmax : ∀ p ∈ n.primeFactors, Real.log p ≤ Real.log P)
    {L : ℝ} (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    let D := Real.log n-L
    (∑ p ∈ n.primeFactors, min D (Real.log p))-3*D ≤ VaughanLogAverage.riesz L n ∧
      max 0 (VaughanLogAverage.riesz L n) =
        max 0 ((∑ p ∈ n.primeFactors, min D (Real.log p))-3*D) := by
  dsimp only
  let a := ∏ p ∈ n.primeFactors.erase P, p
  have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
  have hac : a.primeFactors.card = 3 := by
    rw [hfa,Finset.card_erase_of_mem hP,hc]
  have he : n = P*a := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact (Finset.mul_prod_erase _ _ hP).symm
  have hsp : Squarefree (P*a) := he ▸ hs
  have hp := Nat.prime_of_mem_primeFactors hP
  have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  have hlog : Real.log n = Real.log P+Real.log a := by
    rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hsp.of_mul_right.ne_zero)]
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
  have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
  rw [moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  let D := Real.log n-L
  change (∑ p ∈ n.primeFactors, min D (Real.log p))-3*D ≤ VaughanLogAverage.riesz L n ∧ _
  have hD : 0 ≤ D := sub_nonneg.mpr hLhi
  have hR : VaughanLogAverage.riesz L n =
      VaughanLogAverage.riesz D a-VaughanLogAverage.riesz (D-Real.log P) a := by
    exact hr.symm.trans (by simpa only [← he] using riesz_prime_mul D hp hpn)
  by_cases hlarge : D ≤ Real.log P
  · have hsum := Finset.sum_erase_add n.primeFactors (fun p : ℕ => min D (Real.log p)) hP
    rw [← hfa,min_eq_left hlarge] at hsum
    have hbal : (∑ p ∈ n.primeFactors, min D (Real.log p))-3*D =
        (∑ p ∈ a.primeFactors, min D (Real.log p))-2*D := by linarith
    rw [hR,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
      (by linarith : D-Real.log P ≤ 0),sub_zero,hbal]
    exact riesz_three_clipped_sum hsp.of_mul_right hac hD
  · have hsmall : Real.log P ≤ D := le_of_lt (lt_of_not_ge hlarge)
    have hall (p : ℕ) (hp' : p ∈ n.primeFactors) : Real.log p ≤ D :=
      (hmax p hp').trans hsmall
    have hsum : (∑ p ∈ n.primeFactors, min D (Real.log p)) = Real.log n := by
      rw [Finset.sum_congr rfl (fun p hp' => min_eq_right (hall p hp'))]
      exact (CoprimeEulerPhase.squarefree_log_eq_prime_sum hs).symm
    obtain ⟨b,c,d,hb,hc',hd,hbc,hbd,hcd,haeq⟩ := exists_three_primes hsp.of_mul_right hac
    have hlogs : Real.log a = Real.log b+Real.log c+Real.log d := by
      rw [haeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne_zero)
        (by exact_mod_cast (Nat.mul_ne_zero hc'.ne_zero hd.ne_zero)),Nat.cast_mul,
        Real.log_mul (by exact_mod_cast hc'.ne_zero) (by exact_mod_cast hd.ne_zero)]
      ring
    have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ D := by
      have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv P
      exact hall p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)
    have hbD := hbound b hb (by rw [haeq]; exact dvd_mul_right _ _)
    have hcD := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    have hdD := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
    have heq : VaughanLogAverage.riesz L n = Real.log n-3*D := by
      rw [hR,haeq,
        riesz_three_primes_eq_difference D hb hc' hd hbc hbd hcd,
        riesz_three_primes_eq_difference (D-Real.log P) hb hc' hd hbc hbd hcd,
        four_difference_singletons hD hbD hcD hdD hsmall (by dsimp [D]; linarith)]
      linarith
    rw [heq,hsum]
    exact ⟨le_rfl,rfl⟩

/-- Retain the excess logarithm of every prime beyond the reflected
cutoff, rather than retaining only the largest prime's excess. -/
theorem clipped_sum_eq_excess {n : ℕ} (hs : Squarefree n) (L : ℝ) :
    (∑ p ∈ n.primeFactors, min (Real.log n-L) (Real.log p))-3*(Real.log n-L) =
      3*L-2*Real.log n-
        ∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L)) := by
  have hm (p : ℕ) : min (Real.log n-L) (Real.log p) =
      Real.log p-max 0 (Real.log p-(Real.log n-L)) := by
    by_cases h : Real.log p ≤ Real.log n-L
    · rw [min_eq_right h,max_eq_left (by linarith)]
      ring
    · rw [min_eq_left (le_of_not_ge h),max_eq_right (by linarith)]
      ring
  simp_rw [hm]
  rw [Finset.sum_sub_distrib,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs]
  ring

/-- A closed arithmetic allowance for the negative four-prime coefficient.
This is an allowance for the existing carrier, not a new carrier. -/
def negativeAllowance (L : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then (Real.log n/L)*max 0
    (3*L-2*Real.log n-∑ p ∈ n.primeFactors, max 0 (Real.log p-(Real.log n-L))) else 0

/-- The negative-part allowance is nonnegative at a positive length. -/
theorem negativeAllowance_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ negativeAllowance L n := by
  unfold negativeAllowance
  split_ifs
  · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _)
  · rfl

/-- The allowance is exactly the negative part, for every actual integer
with four distinct prime factors. Nonsquarefree coefficients are zero. -/
theorem negativeAllowance_eq {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    negativeAllowance L n = max 0 (-(SquarefreeVaughanLogSource.coefficient L n).re) := by
  by_cases hs : Squarefree n
  · have hP := largestPrime_mem_of_four hc
    have hmax (p : ℕ) (hp : p ∈ n.primeFactors) : Real.log p ≤ Real.log (largestPrime n) := by
      have hn : n.primeFactors.Nonempty := ⟨p,hp⟩
      have hle : p ≤ largestPrime n := by
        rw [largestPrime,dif_pos hn]
        exact Finset.le_max' _ _ hp
      exact Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
        (by exact_mod_cast hle)
    have he := (riesz_four_clipped_sum hs hc hP hmax hLhi hLlo).2
    rw [clipped_sum_eq_excess hs L] at he
    have hnp : ¬n.Prime := by intro h; rw [h.primeFactors,Finset.card_singleton] at hc; omega
    have hgood : Squarefree n ∧ ¬n.Prime := ⟨hs,hnp⟩
    simp only [negativeAllowance,if_pos hs,SquarefreeVaughanLogSource.coefficient,
      if_pos hgood,Complex.ofReal_re]
    rw [show -(-Real.log n*VaughanLogAverage.riesz L n/L) =
      (Real.log n/L)*VaughanLogAverage.riesz L n by ring,
      ← mul_zero (Real.log n/L),← mul_max_of_nonneg _ _
        (div_nonneg (Real.log_natCast_nonneg n) hL.le),he]
    simp only [mul_zero]
  · simp [negativeAllowance,SquarefreeVaughanLogSource.coefficient,hs]

/-- This exact debit never exceeds the old largest-prime allowance. -/
theorem negativeAllowance_le_gap {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    negativeAllowance L n ≤
      (Real.log n/L)*max 0 (2*L-Real.log n-Real.log (largestPrime n)) := by
  rw [negativeAllowance_eq hc hL hLhi hLlo]
  apply max_le
  · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _)
  · have hb := (actual_four_signed_gap hc hL hLhi hLlo).1
    linarith

/-- The phase debit uses the exact negative coefficient and the existing
positive-coefficient upper bound. Both original cosine signs remain. -/
def fourDebit (L y : ℝ) (n : ℕ) : ℝ :=
  negativeAllowance L n*max 0 (Real.cos (y*Real.log n))+
    (Real.log n/L)*max 0 (Real.log (largestPrime n)+Real.log n-2*L)*
      max 0 (-Real.cos (y*Real.log n))

/-- Both observed adverse-sign charges are nonnegative. -/
theorem fourDebit_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ fourDebit L y n := by
  exact add_nonneg (mul_nonneg (negativeAllowance_nonneg hL n) (le_max_left _ _))
    (mul_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
      (le_max_left _ _)) (le_max_left _ _))

/-- The refined observed debit is never larger than the previous debit.
This comparison is pointwise and keeps the actual height and length. -/
theorem fourDebit_le_gap {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ) :
    fourDebit L y n ≤ (Real.log n/L)*
      max 0 (-(Real.log (largestPrime n)+Real.log n-2*L)*Real.cos (y*Real.log n)) := by
  have hb := negativeAllowance_le_gap hc hL hLhi hLlo
  let g := Real.log (largestPrime n)+Real.log n-2*L
  let x := Real.cos (y*Real.log n)
  change negativeAllowance L n*max 0 x+(Real.log n/L)*max 0 g*max 0 (-x) ≤
    (Real.log n/L)*max 0 (-g*x)
  have he : 2*L-Real.log n-Real.log (largestPrime n) = -g := by dsimp [g]; ring
  rw [he] at hb
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx,max_eq_left (by linarith : -x ≤ 0),mul_zero,add_zero,
      ← zero_mul x,← max_mul_of_nonneg _ _ hx]
    simpa only [zero_mul,mul_assoc] using mul_le_mul_of_nonneg_right hb hx
  · have hx' : 0 ≤ -x := by linarith
    rw [max_eq_left (le_of_not_ge hx),mul_zero,zero_add,
      max_eq_right hx',show -g*x = g*(-x) by ring,
      ← zero_mul (-x),← max_mul_of_nonneg _ _ hx']
    simp only [zero_mul,mul_assoc,le_refl]

private theorem real_two_sided_credit {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : -a ≤ c) (hhi : c ≤ b) (x : ℝ) :
    max (c*x) 0-(a*max 0 x+b*max 0 (-x)) ≤ c*x := by
  have hcost : -c*x ≤ a*max 0 x+b*max 0 (-x) := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_right hx,max_eq_left (by linarith : -x ≤ 0),mul_zero,add_zero]
      have hm := mul_le_mul_of_nonneg_right hlo hx
      nlinarith only [hm]
    · rw [max_eq_left (le_of_not_ge hx),mul_zero,zero_add,
        max_eq_right (by linarith : 0 ≤ -x)]
      have hm := mul_le_mul_of_nonpos_right hhi (le_of_not_ge hx)
      nlinarith only [hm]
  have hnonneg : 0 ≤ a*max 0 x+b*max 0 (-x) :=
    add_nonneg (mul_nonneg ha (le_max_left _ _)) (mul_nonneg hb (le_max_left _ _))
  by_cases hp : 0 ≤ c*x
  · rw [max_eq_left hp]
    linarith
  · rw [max_eq_right (le_of_not_ge hp)]
    nlinarith only [hcost]

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- The refined inequality for the original four-prime atom retains every
positive contribution and all original allocation and phase factors. -/
theorem re_four_atom_ge_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 4) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ) :
    max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
      weight A N n*fourDebit L y n ≤
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  have hn := negativeAllowance_eq hc hL hLhi hLlo
  have hlo : -negativeAllowance L n ≤ (SquarefreeVaughanLogSource.coefficient L n).re := by
    rw [hn]
    have hh := le_max_right 0 (-(SquarefreeVaughanLogSource.coefficient L n).re)
    linarith
  have hb := (actual_four_signed_gap hc hL hLhi hLlo).2
  have h := mul_le_mul_of_nonneg_left
    (real_two_sided_credit (negativeAllowance_nonneg hL n)
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _))
      hlo hb (Real.cos (y*Real.log n))) (weight_nonneg A N n)
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at h
  simpa only [re_residual_atom,fourDebit,mul_assoc] using h

/-- The refined inequality is exact on nonnegative cosines: its debit is
precisely the negative part of the observed original atom. -/
theorem re_four_atom_eq_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 4) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ)
    (hcos : 0 ≤ Real.cos (y*Real.log n)) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
        weight A N n*fourDebit L y n := by
  rw [fourDebit,max_eq_right hcos,max_eq_left (by linarith : -Real.cos (y*Real.log n) ≤ 0),
    mul_zero,add_zero,negativeAllowance_eq hc hL hLhi hLlo]
  have he (c : ℝ) : max (c*Real.cos (y*Real.log n)) 0-
      max 0 (-c)*Real.cos (y*Real.log n) = c*Real.cos (y*Real.log n) := by
    by_cases hc' : 0 ≤ c
    · rw [max_eq_left (mul_nonneg hc' hcos),max_eq_left (by linarith : -c ≤ 0)]
      ring
    · rw [max_eq_right (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc') hcos),
        max_eq_right (by linarith : 0 ≤ -c)]
      ring
  have hm := congrArg (fun z => weight A N n*z) (he (SquarefreeVaughanLogSource.coefficient L n).re)
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at hm
  simpa only [re_residual_atom,mul_assoc] using hm.symm

/-- Both count classes are handled in the same original finite sum. The
sharpened four-prime debit retains the five-prime credit theorem and every
other signed term; there is no separate complement estimate. -/
theorem re_sum_ge_four_five_credit (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 →
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, if n.primeFactors.card = 4 then
      max (f n).re 0-weight A N n*fourDebit L y n
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
    exact ZetaRieszFivePrimeFloor.re_five_atom_ge_keep_positive A N hfive.1 hL hw.2.1 hw.2.2 y hfive.2
  · exact le_rfl

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint

/-- The original core discharges the geometric premises eventually. The
whole signed complement stays inside this one lower comparison. Its
aggregate numerical floor remains open. -/
theorem eventually_re_core_ge_four_five_credit {u : ℝ}
    (hu : 1/2 < u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ),
      let L := SquarefreeVaughanLogSource.length u N
      let A := intermediatePrimes u N
      let S := coreBand u N K
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if n.primeFactors.card = 4 then
        max (f n).re 0-weight A N n*fourDebit L y n
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

open ZetaRieszRadialCompensation

/-- Combine the paid balanced triple band and its unspent supply with the
refined four/five-prime comparison on their untouched complement. Supply
labels are excluded before applying the debit, so no positive credit is
spent twice. This is one joint floor with only the already paid edge error. -/
theorem eventually_compensated_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let X := ∑ n ∈ radialTriples S N η, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η)
        let B := ∑ n ∈ W, if n.primeFactors.card = 4 then
          max (f n).re 0-weight A N n*fourDebit L y n
          else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
            max (f n).re 0-weight A N n*(Real.log n/L)*
              min (3*Real.log n.minFac)
              (max 0 (min (2*Real.log (largestPrime n)+Real.log n-3*L)
                (Real.log (largestPrime n)-Real.log (largestPrime (n/largestPrime n))+Real.log n-2*L)))*
              (-Real.cos (y*Real.log n))
          else (f n).re
        0 < Y.re ∧
          u^(N+1)*(B+max X.re 0+Y.re/2)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,hfloor⟩ := eventually_core_balanced_floor hu hU hy
  refine ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,?_⟩
  have hsource := hU.trans_lt ZetaRieszWideOwnerAudit.radius_lt_source
  have hL := ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (by linarith : 0 < u) (by norm_num : (0 : ℝ) ≤ 137/200)
    (hsource.trans (Real.exp_lt_exp.mpr (by norm_num : -(11/16 : ℝ) < -(137/200 : ℝ))))
  filter_upwards [hfloor,tendsto_dyadicMomentOrder.eventually hL,
    tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop (2 : ℕ))] with j hj hlow hN
  obtain ⟨v,hv,hY,hfloor⟩ := hj
  let N := dyadicMomentOrder j
  let L := SquarefreeVaughanLogSource.length u N
  let A := intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let W := S\(radialTriples S N η ∪ radialSupply N h v ∪ balancedTriples S N η)
  have hupp : L ≤ (7/5 : ℝ)*N := by
    have hl := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp [L,N]
    nlinarith [Real.log_two_lt_d9,Nat.cast_nonneg (α := ℝ) (dyadicMomentOrder j)]
  have hwindow (n : ℕ) (hn : n ∈ W)
      (_hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5) :
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n := by
    have hnS : n ∈ S := (Finset.mem_sdiff.mp hn).1
    have hw := (Finset.mem_filter.mp hnS).2
    change 2*(137/200 : ℝ)*N ≤ L at hlow
    constructor
    · nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
    constructor <;> nlinarith [hw.1,hw.2,Nat.cast_nonneg (α := ℝ) N]
  have hb := re_sum_ge_four_five_credit W A N (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  refine ⟨v,hv,hY,?_⟩
  apply le_trans _ hfloor
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  exact add_le_add (add_le_add hb le_rfl) le_rfl

end
end RiemannGaussian.ZetaRieszFourPrimeReserve
