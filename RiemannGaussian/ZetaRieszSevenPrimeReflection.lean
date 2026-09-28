/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedPrimeBounds
import RiemannGaussian.ZetaRieszFivePrimeFloor
import RiemannGaussian.ZetaRieszParityFirstInsertion

/-!
# A second reflection sharpens the actual seven-prime coefficient

The five-prime active cofactor is reflected before its signed response is
bounded. The original label, total-count parity and phase are unchanged.
-/

namespace RiemannGaussian.ZetaRieszSevenPrimeReflection
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime ZetaRieszReflectedLinear
open ZetaRieszSignedSperner ZetaRieszReflectedPrimeBounds

/-- Below the first quarter, five small logarithms leave only the unit
and singleton hinges. Their signed sum is affine. -/
theorem five_difference_singletons {a b c p q D : ℝ}
    (hD : 0 ≤ D) (ha : a ≤ D) (hb : b ≤ D) (hc : c ≤ D)
    (hp : p ≤ D) (hq : q ≤ D) (ht : 4*D ≤ a+b+c+p+q) :
    (tripleDifference a b c D-tripleDifference a b c (D-p))-
      (tripleDifference a b c (D-q)-tripleDifference a b c (D-q-p)) =
        a+b+c+p+q-4*D := by
  simp only [tripleDifference,primePairTent]
  repeat' first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
  ring

/-- The complete signed five-logarithm response below its first third
costs at most any one logarithm when every logarithm is below the cutoff. -/
theorem five_difference_le_last {a b c p q D : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (haD : a ≤ D) (hbD : b ≤ D) (hcD : c ≤ D) (hpD : p ≤ D) (hqD : q ≤ D)
    (ht : 3*D ≤ a+b+c+p+q) :
    (tripleDifference a b c D-tripleDifference a b c (D-p))-
      (tripleDifference a b c (D-q)-tripleDifference a b c (D-q-p)) ≤ q := by
  by_cases hquarter : 4*D ≤ a+b+c+p+q
  · rw [five_difference_singletons (ha.trans haD) haD hbD hcD hpD hqD hquarter]
    linarith
  · exact (ZetaRieszFivePrimeFloor.five_difference_small ha hb hc hp hq
      haD hbD hcD hpD hqD ht (le_of_not_ge hquarter)).trans hq

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

/-- The small-logarithm chamber retains the complete divisor sum and
its signed singleton/pair cancellation. -/
theorem riesz_five_small_logs_le {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) {D : ℝ}
    (hsmall : ∀ p ∈ n.primeFactors, Real.log p ≤ D)
    (hthird : 3*D ≤ Real.log n) :
    VaughanLogAverage.riesz D n ≤ Real.log n.minFac := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hp := Nat.minFac_prime hn1
  have hP := hp.mem_primeFactors (Nat.minFac_dvd n) hs.ne_zero
  obtain ⟨a,he,hsp,hfa,hlog⟩ := prime_cofactor hs hP
  have hac : a.primeFactors.card = 4 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
  have ha1 : a ≠ 1 := by intro h; simp [h] at hac
  have hq := Nat.minFac_prime ha1
  have hQ := hq.mem_primeFactors (Nat.minFac_dvd a) hsp.of_mul_right.ne_zero
  obtain ⟨b,haeq,hsq,hfb,hloga⟩ := prime_cofactor hsp.of_mul_right hQ
  have hbc : b.primeFactors.card = 3 := by rw [hfb,Finset.card_erase_of_mem hQ,hac]
  have hpn : ¬ n.minFac ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
  have hqn : ¬ a.minFac ∣ b := hq.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsq)
  obtain ⟨c,d,e,hc',hd,he',hcd,hce,hde,hbeq⟩ := exists_three_primes hsq.of_mul_right hbc
  have hlogb : Real.log b = Real.log c+Real.log d+Real.log e := by
    rw [hbeq,Nat.cast_mul,Real.log_mul (by exact_mod_cast hc'.ne_zero)
      (by exact_mod_cast (Nat.mul_ne_zero hd.ne_zero he'.ne_zero)),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hd.ne_zero) (by exact_mod_cast he'.ne_zero)]
    ring
  have hbound (p : ℕ) (hp' : p.Prime) (hpdiv : p ∣ a) : Real.log p ≤ D := by
    have hdvd : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpdiv n.minFac
    exact hsmall p (Nat.mem_primeFactors.mpr ⟨hp',hdvd,hs.ne_zero⟩)
  have hcb : c ∣ b := by rw [hbeq]; exact dvd_mul_right _ _
  have hdb : d ∣ b := by rw [hbeq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have heb : e ∣ b := by rw [hbeq]; exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hcD := hbound c hc' (by rw [haeq]; exact dvd_mul_of_dvd_right hcb a.minFac)
  have hdD := hbound d hd (by rw [haeq]; exact dvd_mul_of_dvd_right hdb a.minFac)
  have heD := hbound e he' (by rw [haeq]; exact dvd_mul_of_dvd_right heb a.minFac)
  have hQD := hbound a.minFac hq (Nat.minFac_dvd a)
  have hPD := hsmall n.minFac hP
  conv_lhs =>
    rw [he,riesz_prime_mul D hp hpn,haeq,riesz_prime_mul D hq hqn,
      riesz_prime_mul (D-Real.log n.minFac) hq hqn,hbeq,
      riesz_three_primes_eq_difference D hc' hd he' hcd hce hde,
      riesz_three_primes_eq_difference (D-Real.log a.minFac) hc' hd he' hcd hce hde,
      riesz_three_primes_eq_difference (D-Real.log n.minFac) hc' hd he' hcd hce hde,
      riesz_three_primes_eq_difference (D-Real.log n.minFac-Real.log a.minFac) hc' hd he' hcd hce hde]
  exact five_difference_le_last (Real.log_natCast_nonneg c) (Real.log_natCast_nonneg d)
    (Real.log_natCast_nonneg e) (Real.log_natCast_nonneg a.minFac)
    (Real.log_natCast_nonneg n.minFac) hcD hdD heD hQD hPD (by linarith)

/-- Every squarefree five-prime response below its first third is at
most the actual least-prime logarithm. All cutoff chambers are included. -/
theorem riesz_five_lower_third_le {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) {D : ℝ} (hthird : 3*D ≤ Real.log n) :
    VaughanLogAverage.riesz D n ≤ Real.log n.minFac := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hmin := Nat.minFac_prime hn1
  have hminmem := hmin.mem_primeFactors (Nat.minFac_dvd n) hs.ne_zero
  by_cases hbase : D ≤ Real.log n.minFac
  · have h := ZetaRieszExtremePrimeProfile.riesz_mul_eq_of_extreme_rough
      (a := 1) (b := n) (L := D) (by simpa using hs) (by
        intro p hp
        have hp' := Nat.prime_of_mem_primeFactors hp
        have hle := Nat.minFac_le_of_dvd hp'.two_le (Nat.dvd_of_mem_primeFactors hp)
        exact hbase.trans (Real.log_le_log (by exact_mod_cast hmin.pos) (by exact_mod_cast hle)))
    simp only [mul_one] at h
    rw [h]
    simpa [VaughanLogAverage.riesz] using max_le (Real.log_natCast_nonneg n.minFac) hbase
  by_cases hlarge : ∃ P ∈ n.primeFactors, D ≤ Real.log P
  · obtain ⟨P,hP,hPD⟩ := hlarge
    obtain ⟨a,he,hsp,hfa,hlog⟩ := prime_cofactor hs hP
    have hac : a.primeFactors.card = 4 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
    have hp := Nat.prime_of_mem_primeFactors hP
    have hpn : ¬ P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
    have hPmin : n.minFac ≠ P := by intro hh; rw [← hh] at hPD; exact hbase hPD
    have hmema : n.minFac ∈ a.primeFactors := by
      rw [hfa]
      exact Finset.mem_erase.mpr ⟨hPmin,hminmem⟩
    have ha1 : a ≠ 1 := by intro hh; simp [hh] at hac
    have hminEq : a.minFac = n.minFac := by
      apply le_antisymm
      · exact Nat.minFac_le_of_dvd hmin.two_le (Nat.dvd_of_mem_primeFactors hmema)
      · apply Nat.minFac_le_of_dvd (Nat.minFac_prime ha1).two_le
        rw [he]
        exact dvd_mul_of_dvd_right (Nat.minFac_dvd a) P
    have hb := (riesz_bounds_minFac D hsp.of_mul_right (by omega : 2 ≤ a.primeFactors.card)).2
    have hcap : parityCapacity 2 0 = 1 := by decide +kernel
    rw [hac,show 4-2 = 2 by rfl,hcap,hminEq] at hb
    norm_num only [Nat.cast_one,mul_one] at hb
    conv_lhs =>
      rw [he,riesz_prime_mul D hp hpn,
        ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (by linarith : D-Real.log P ≤ 0),sub_zero]
    exact hb
  · exact riesz_five_small_logs_le hs hc (fun p hp =>
      le_of_lt (lt_of_not_ge (fun h => hlarge ⟨p,hp,h⟩))) hthird

/-- Reflection of the complete five-prime divisor sum sharpens its
negative side once the cutoff reaches two thirds of the cofactor log. -/
theorem riesz_five_upper_two_thirds_ge {n : ℕ} (hs : Squarefree n)
    (hc : n.primeFactors.card = 5) {D : ℝ} (hthird : 2*Real.log n ≤ 3*D) :
    -Real.log n.minFac ≤ VaughanLogAverage.riesz D n := by
  have hn1 : n ≠ 1 := by intro h; simp [h] at hc
  have hnp : ¬ n.Prime := by intro h; simp [h.primeFactors] at hc
  have hb := riesz_five_lower_third_le hs hc (D := Real.log n-D) (by linarith)
  have hr := VaughanLogAverage.riesz_reflection D hs hn1 hnp
  rw [ZetaRieszReflectedLinear.moebius_eq_primeCount hs,hc] at hr
  norm_num at hr
  rw [hr] at hb
  linarith

/-- The literal two-large-prime seven-factor sector has signed
coefficient interval [-1,3], in least-prime logarithm units. The second
reflection is applied only inside the existing coefficient. -/
theorem coefficient_seven_two_outer_sharp {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (hD : 2*Real.log n ≤ 7*(Real.log n-L))
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    -(Real.log n/L*Real.log n.minFac) ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ 3*(Real.log n/L)*Real.log n.minFac := by
  let D := Real.log n-L
  have hs : Squarefree (outerPart D n * activePart D n) := by
    rw [factorization D hn]
    exact hn
  have hcount : (activePrimes D n).card = 5 := by
    have hh := count_split D n
    change (outerPrimes (Real.log n-L) n).card + (activePrimes D n).card = _ at hh
    omega
  have hlog : Real.log n = Real.log (outerPart D n)+Real.log (activePart D n) := by
    conv_lhs => rw [← factorization D hn]
    rw [Nat.cast_mul,Real.log_mul
      (by exact_mod_cast hs.of_mul_left.ne_zero) (by exact_mod_cast hs.of_mul_right.ne_zero)]
  have hsum := Finset.sum_le_sum (s := outerPrimes D n) (fun p hp => (Finset.mem_filter.mp hp).2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [← outerPart_primeFactors,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs.of_mul_left,
    outerPart_primeFactors] at hsum
  change (outerPrimes (Real.log n-L) n).card*D ≤ Real.log (outerPart D n) at hsum
  rw [ho] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have haD : 2*Real.log (activePart D n) ≤ 3*D := by dsimp only [D] at *; linarith
  have hb := riesz_five_upper_two_thirds_ge hs.of_mul_right
    (by rw [activePart_primeFactors]; exact hcount) haD
  rw [activePart_minFac hn (Finset.card_pos.mp (by omega : 0 < (activePrimes D n).card))] at hb
  have hlo := mul_le_mul_of_nonneg_left hb (div_nonneg (Real.log_natCast_nonneg n) hL.le)
  have ht : 0 < Real.log n := by
    have hn1 : n ≠ 1 := by intro h; simp [h] at hc
    exact Real.log_pos (by exact_mod_cast (show 1 < n by have := hn.ne_zero; omega))
  have hquarter : Real.log n < 4*(Real.log n-L) := by linarith
  refine ⟨?_,(coefficient_seven_two_outer hL hn hc hquarter ho).2⟩
  rw [coefficient_eq_active hn (by omega : 2 ≤ n.primeFactors.card),hc]
  norm_num only [show (-1 : ℝ)^7 = -1 by norm_num,mul_neg_one,neg_neg]
  simpa only [D,mul_neg] using hlo

open ZetaRieszParityPacket

/-- The actual moving core lies beyond the two-sevenths threshold
needed for the second reflection. No limiting length is substituted. -/
theorem core_cutoff_two_sevenths {u : ℝ} (hu : 1/2 ≤ u) {N K n : ℕ}
    (hN : 2 ≤ N) (hn : n ∈ coreBand u N K) :
    2*Real.log n < 7*(Real.log n-SquarefreeVaughanLogSource.length u N) := by
  have hg := ZetaRieszParityFirstInsertion.core_support_gap_sharp hu hN hn
  have hlo := (Finset.mem_filter.mp hn).2.1
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 0 < Real.log n := by linarith
  have hfrac : SquarefreeVaughanLogSource.length u N/Real.log n < (711/1000 : ℝ) := by linarith
  have hm := (div_lt_iff₀ ht).mp hfrac
  linarith

open ZetaRieszJointAllocation ZetaRieszOneSidedArithmetic

/-- Intersect only the negative coefficient charge on the exact
seven-prime/two-outer sector. All other earlier charges remain available. -/
def lowerAllowance (L : ℝ) (n : ℕ) : ℝ :=
  if n.primeFactors.card = 7 ∧ (outerPrimes (Real.log n-L) n).card = 2 then
    min (ZetaRieszReflectedPrimeBounds.allowance L n 0) (Real.log n/L*Real.log n.minFac)
  else ZetaRieszReflectedPrimeBounds.allowance L n 0

/-- The new charge cannot worsen the previous lower allowance. -/
theorem lowerAllowance_le_previous (L : ℝ) (n : ℕ) :
    lowerAllowance L n ≤ ZetaRieszReflectedPrimeBounds.allowance L n 0 := by
  unfold lowerAllowance
  split_ifs
  · exact min_le_left _ _
  · rfl

/-- Both candidates in the intersection are nonnegative. -/
theorem lowerAllowance_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ lowerAllowance L n := by
  unfold lowerAllowance
  split_ifs
  · exact le_min (ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 0)
      (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (Real.log_natCast_nonneg n.minFac))
  · exact ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 0

/-- Both actual coefficient signs, with the second reflection used
only on its proved support and the earlier interval elsewhere. -/
theorem coefficient_bounds {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hquarter : Real.log n < 4*(Real.log n-L)) (htwo : 2*Real.log n ≤ 7*(Real.log n-L)) :
    -lowerAllowance L n ≤ (SquarefreeVaughanLogSource.coefficient L n).re ∧
      (SquarefreeVaughanLogSource.coefficient L n).re ≤ ZetaRieszReflectedPrimeBounds.allowance L n 1 := by
  have hh := ZetaRieszReflectedPrimeBounds.coefficient_bounds hL hc hcut hquarter
  refine ⟨?_,hh.2⟩
  unfold lowerAllowance
  split_ifs with h
  · by_cases hle : ZetaRieszReflectedPrimeBounds.allowance L n 0 ≤ Real.log n/L*Real.log n.minFac
    · rw [min_eq_left hle]
      exact hh.1
    rw [min_eq_right (le_of_not_ge hle)]
    by_cases hs : Squarefree n
    · exact (coefficient_seven_two_outer_sharp hL hs h.1 htwo h.2).1
    · simp only [SquarefreeVaughanLogSource.coefficient,hs,false_and,if_false,Complex.zero_re]
      exact neg_nonpos.mpr (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
        (Real.log_natCast_nonneg n.minFac))
  · exact hh.1

/-- The actual cosine keeps the two coefficient signs distinct. -/
def floorCost (L y : ℝ) (n : ℕ) : ℝ :=
  lowerAllowance L n*max (Real.cos (y*Real.log n)) 0+
    ZetaRieszReflectedPrimeBounds.allowance L n 1*max (-Real.cos (y*Real.log n)) 0

/-- The same improvement enters the opposite phase of the ceiling. -/
def ceilingCost (L y : ℝ) (n : ℕ) : ℝ :=
  ZetaRieszReflectedPrimeBounds.allowance L n 1*max (Real.cos (y*Real.log n)) 0+
    lowerAllowance L n*max (-Real.cos (y*Real.log n)) 0

/-- Both signed costs improve monotonically, including nonsquarefree
labels and every height; no extra supply or discarded observation enters. -/
theorem costs_le_previous (L y : ℝ) (n : ℕ) :
    floorCost L y n ≤ ZetaRieszReflectedPrimeBounds.floorCost L y n ∧
      ceilingCost L y n ≤ ZetaRieszReflectedPrimeBounds.ceilingCost L y n := by
  have hh := lowerAllowance_le_previous L n
  unfold floorCost ceilingCost ZetaRieszReflectedPrimeBounds.floorCost ZetaRieszReflectedPrimeBounds.ceilingCost
  constructor <;> gcongr

/-- The earlier intersected allowance on this exact squarefree sector
is three least-prime units on each side. -/
theorem previous_seven_allowances {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    ZetaRieszReflectedPrimeBounds.allowance L n 0 = 3*(Real.log n/L*Real.log n.minFac) ∧
      ZetaRieszReflectedPrimeBounds.allowance L n 1 = 3*(Real.log n/L*Real.log n.minFac) := by
  have hb : 0 ≤ Real.log n/L*Real.log n.minFac :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (Real.log_natCast_nonneg n.minFac)
  have h₀ : activeCapacity 7 2 0 = 3 := congrArg Prod.fst activeCapacity_table.2.1
  have h₁ : activeCapacity 7 2 1 = 3 := congrArg Prod.snd activeCapacity_table.2.1
  have hodd := ZetaRieszIntersectingWindow.oddWindowCapacity_five
  norm_num [ZetaRieszReflectedPrimeBounds.allowance,previousAllowance,
    activeAllowance,ZetaRieszIntersectingWindow.allowance,hn,hc,ho,h₀,h₁,
    hodd.1,hodd.2]
  constructor <;> rw [min_eq_right (by nlinarith only [hb])] <;> ring

/-- The negative charge is exactly one least-prime unit in this
sector; its reduction is not merely an existential smaller allowance. -/
theorem seven_lowerAllowance_eq {L : ℝ} (hL : 0 < L) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    lowerAllowance L n = Real.log n/L*Real.log n.minFac := by
  have hb : 0 ≤ Real.log n/L*Real.log n.minFac :=
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (Real.log_natCast_nonneg n.minFac)
  rw [lowerAllowance,if_pos ⟨hc,ho⟩,(previous_seven_allowances hL hn hc ho).1]
  exact min_eq_right (by linarith)

/-- Exact savings on each of the two original cosine orientations.
These are reductions in alternative charges, not additional signed supply. -/
theorem seven_cost_savings {L : ℝ} (hL : 0 < L) (y : ℝ) {n : ℕ}
    (hn : Squarefree n) (hc : n.primeFactors.card = 7)
    (ho : (outerPrimes (Real.log n-L) n).card = 2) :
    ZetaRieszReflectedPrimeBounds.floorCost L y n-floorCost L y n =
        2*(Real.log n/L*Real.log n.minFac)*max (Real.cos (y*Real.log n)) 0 ∧
      ZetaRieszReflectedPrimeBounds.ceilingCost L y n-ceilingCost L y n =
        2*(Real.log n/L*Real.log n.minFac)*max (-Real.cos (y*Real.log n)) 0 := by
  have hh := previous_seven_allowances hL hn hc ho
  simp only [floorCost,ceilingCost,ZetaRieszReflectedPrimeBounds.floorCost,
    ZetaRieszReflectedPrimeBounds.ceilingCost,seven_lowerAllowance_eq hL hn hc ho,hh.1,hh.2]
  constructor <;> ring

/-- Pointwise signed bounds with the exact residual allocation,
factorial kernel, original integer label and full product phase. -/
theorem residual_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hquarter : Real.log n < 4*(Real.log n-L)) (htwo : 2*Real.log n ≤ 7*(Real.log n-L)) :
    -(weight A N n*floorCost L y n) ≤
        (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ∧
      (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re ≤
        weight A N n*ceilingCost L y n := by
  have hh := coefficient_bounds hL hc hcut hquarter htwo
  rw [re_residual_atom]
  have hw := weight_nonneg A N n
  suffices hs : -floorCost L y n ≤
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ∧
      (SquarefreeVaughanLogSource.coefficient L n).re*Real.cos (y*Real.log n) ≤ ceilingCost L y n by
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

/-- Favorable observations are retained in both one-sided comparisons. -/
theorem residual_retained_bounds (A : Finset ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ) (N : ℕ)
    {n : ℕ} (hc : 5 ≤ n.primeFactors.card) (hcut : 2*Real.log n ≤ 3*L)
    (hquarter : Real.log n < 4*(Real.log n-L)) (htwo : 2*Real.log n ≤ 7*(Real.log n-L)) :
    let v := (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    max v 0-weight A N n*floorCost L y n ≤ v ∧
      v ≤ min v 0+weight A N n*ceilingCost L y n := by
  dsimp only
  have hh := residual_bounds A hL y N hc hcut hquarter htwo
  have hl : 0 ≤ weight A N n*floorCost L y n := by
    unfold floorCost
    positivity [weight_nonneg A N n,lowerAllowance_nonneg hL n,
      ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 1]
  have hu : 0 ≤ weight A N n*ceilingCost L y n := by
    unfold ceilingCost
    positivity [weight_nonneg A N n,lowerAllowance_nonneg hL n,
      ZetaRieszReflectedPrimeBounds.allowance_nonneg hL n 1]
  by_cases hv : 0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
  · rw [max_eq_left hv,min_eq_right hv]
    constructor <;> linarith only [hh.2,hl]
  · have hv' := le_of_not_ge hv
    rw [max_eq_right hv',min_eq_left hv']
    constructor <;> linarith only [hh.1,hu]

open Filter Topology ZetaRieszAnnulusJoint

/-- Every selected subset of the literal core inherits both refined
signed comparisons. Counts below seven and the signed complement remain
unchanged; the two comparisons are alternatives, not additive credits. -/
theorem eventually_core_subset_bounds {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : ℕ) (y : ℝ) (S : Finset ℕ), S ⊆ coreBand u N K →
      let A := intermediatePrimes u N
      let L := SquarefreeVaughanLogSource.length u N
      let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
      u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card then
        max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
          ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ∧
        ((u : ℂ)^(N+1)*∑ n ∈ S, f n).re ≤
          u^(N+1)*(∑ n ∈ S, if 7 ≤ n.primeFactors.card then
            min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re) := by
  filter_upwards [ZetaRieszSixPrimeGeometry.eventually_core_cutoff_thirds hu hU,
    eventually_ge_atTop (2 : ℕ)] with N hcut hN K y S hS
  let A := intermediatePrimes u N
  let L := SquarefreeVaughanLogSource.length u N
  let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
  have hsum :
      (∑ n ∈ S, if 7 ≤ n.primeFactors.card then max (f n).re 0-weight A N n*floorCost L y n else (f n).re) ≤
        (∑ n ∈ S, f n).re ∧
      (∑ n ∈ S, f n).re ≤
        ∑ n ∈ S, if 7 ≤ n.primeFactors.card then min (f n).re 0+weight A N n*ceilingCost L y n else (f n).re := by
    rw [Complex.re_sum]
    constructor
    · apply Finset.sum_le_sum
      intro n hn
      split_ifs with hc
      · exact (residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N
          (by omega) (hcut K n (hS hn)) (core_cutoff_quarter hu.le hN (hS hn))
          (core_cutoff_two_sevenths hu.le hN (hS hn)).le).1
      · exact le_rfl
    · apply Finset.sum_le_sum
      intro n hn
      split_ifs with hc
      · exact (residual_retained_bounds A (SquarefreeVaughanLogSource.length_pos u N) y N
          (by omega) (hcut K n (hS hn)) (core_cutoff_quarter hu.le hN (hS hn))
          (core_cutoff_two_sevenths hu.le hN (hS hn)).le).2
      · exact le_rfl
  have hlo := mul_le_mul_of_nonneg_left hsum.1 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  have hhi := mul_le_mul_of_nonneg_left hsum.2 (pow_nonneg (show 0 ≤ u by linarith) (N+1))
  dsimp only
  simpa only [f,A,L,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using And.intro hlo hhi

end
end RiemannGaussian.ZetaRieszSevenPrimeReflection
