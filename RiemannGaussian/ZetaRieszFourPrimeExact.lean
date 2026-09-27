/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmallPrimeCompensation

/-!
# Both observed four-prime debits, without coefficient slack

The positive coefficient must pay every cofactor-prime excess after
largest-prime deletion. This sharpens the negative-cosine side of the
existing signed floor; the negative coefficient was already evaluated.
All original weights and the unused complementary sum are retained.
-/

namespace RiemannGaussian.ZetaRieszFourPrimeExact
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaRieszReflectedLinear ZetaRieszPrimeEndpoint
open ZetaRieszFourPrimeFloor ZetaRieszFourPrimeReserve

/-- Exact positive-part candidate for the original four-prime coefficient.
Every cofactor prime's excess is subtracted before taking the positive part. -/
def positiveAllowance (L : ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then (Real.log n/L)*max 0
    (Real.log (largestPrime n)+Real.log n-2*L-
      ∑ p ∈ n.primeFactors.erase (largestPrime n),
        max 0 (Real.log p-(L-Real.log (largestPrime n)))) else 0

theorem positiveAllowance_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ positiveAllowance L n := by
  unfold positiveAllowance
  split_ifs
  · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (le_max_left _ _)
  · rfl

/-- Reflection and genuine prime deletion evaluate the entire positive
coefficient, including all saturation and zero chambers. -/
theorem positiveAllowance_eq {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    positiveAllowance L n = max 0 (SquarefreeVaughanLogSource.coefficient L n).re := by
  by_cases hs : Squarefree n
  · let P := largestPrime n
    let F := Real.log P+Real.log n-2*L-
      ∑ p ∈ n.primeFactors.erase P, max 0 (Real.log p-(L-Real.log P))
    have hsum0 : 0 ≤ ∑ p ∈ n.primeFactors.erase P,
        max 0 (Real.log p-(L-Real.log P)) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
    have hnp : ¬n.Prime := by intro hp; rw [hp.primeFactors,Finset.card_singleton] at hc; omega
    have hn1 : n ≠ 1 := by intro hn; simp [hn] at hc
    have hscale : 0 ≤ Real.log n/L := div_nonneg (Real.log_natCast_nonneg n) hL.le
    change (if Squarefree n then (Real.log n/L)*max 0 F else 0) = _
    rw [if_pos hs]
    by_cases hgate : Real.log P+Real.log n ≤ 2*L
    · have hnonpos := (actual_four_signed_gap hc hL hLhi hLlo).2
      have hgap : max 0 (Real.log (largestPrime n)+Real.log n-2*L) = 0 :=
        max_eq_left (by change Real.log P+Real.log n-2*L ≤ 0; linarith)
      rw [hgap,mul_zero] at hnonpos
      have hF : F ≤ 0 := by dsimp [F]; linarith
      rw [max_eq_left hF,mul_zero,max_eq_left hnonpos]
    have hP : P ∈ n.primeFactors := largestPrime_mem_of_four hc
    let a := ∏ p ∈ n.primeFactors.erase P, p
    have hpa (p : ℕ) (hp : p ∈ n.primeFactors.erase P) : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hfa : a.primeFactors = n.primeFactors.erase P := Nat.primeFactors_prod hpa
    have hac : a.primeFactors.card = 3 := by rw [hfa,Finset.card_erase_of_mem hP,hc]
    have he : n = P*a := by
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      exact (Finset.mul_prod_erase _ _ hP).symm
    have hsp : Squarefree (P*a) := he ▸ hs
    have hp := Nat.prime_of_mem_primeFactors hP
    have hpn : ¬P ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsp)
    have hlog : Real.log n = Real.log P+Real.log a := by
      rw [he,Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
        (by exact_mod_cast hsp.of_mul_right.ne_zero)]
    let D := Real.log n-L
    have hlarge : D ≤ Real.log P := by dsimp [D]; linarith
    have hr := VaughanLogAverage.riesz_reflection L hs hn1 hnp
    rw [moebius_eq_primeCount hs,hc] at hr
    norm_num at hr
    have ha1 : a ≠ 1 := by intro ha; simp [ha] at hac
    have hap : ¬a.Prime := by intro ha; rw [ha.primeFactors,Finset.card_singleton] at hac; omega
    have hr' := VaughanLogAverage.riesz_reflection D hsp.of_mul_right ha1 hap
    rw [moebius_eq_primeCount hsp.of_mul_right,hac] at hr'
    norm_num at hr'
    have hR : -VaughanLogAverage.riesz L n = VaughanLogAverage.riesz (L-Real.log P) a := by
      have hdel : VaughanLogAverage.riesz L n = VaughanLogAverage.riesz D a := by
        calc
          _ = VaughanLogAverage.riesz D n := hr.symm
          _ = VaughanLogAverage.riesz D a-VaughanLogAverage.riesz (D-Real.log P) a := by
            simpa only [← he] using riesz_prime_mul D hp hpn
          _ = _ := by rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
            (by linarith : D-Real.log P ≤ 0),sub_zero]
      rw [hdel]
      have hcut : Real.log a-D = L-Real.log P := by dsimp [D]; linarith
      simpa only [hcut] using hr'.symm
    have hcR : (SquarefreeVaughanLogSource.coefficient L n).re =
        (Real.log n/L)*VaughanLogAverage.riesz (L-Real.log P) a := by
      simp only [SquarefreeVaughanLogSource.coefficient,
        if_pos (show Squarefree n ∧ ¬n.Prime from ⟨hs,hnp⟩),Complex.ofReal_re]
      rw [show -Real.log n*VaughanLogAverage.riesz L n/L =
        (Real.log n/L)*(-VaughanLogAverage.riesz L n) by ring,hR]
    have hpos : max 0 (VaughanLogAverage.riesz (L-Real.log P) a) = max 0 F := by
      by_cases hsat : L ≤ Real.log P
      · rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos (sub_nonpos.mpr hsat),max_self]
        have hsum : (∑ p ∈ n.primeFactors.erase P, max 0 (Real.log p-(L-Real.log P))) =
            Real.log a-3*(L-Real.log P) := by
          rw [← hfa]
          have hterm (p : ℕ) (_hp : p ∈ a.primeFactors) :
              max 0 (Real.log p-(L-Real.log P)) = Real.log p-(L-Real.log P) :=
            max_eq_right (by linarith [Real.log_natCast_nonneg p])
          rw [Finset.sum_congr rfl hterm,Finset.sum_sub_distrib,
            ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hsp.of_mul_right,
            Finset.sum_const,nsmul_eq_mul,hac]
          norm_num
        have hF : F = L-Real.log P := by dsimp [F]; rw [hsum]; linarith
        rw [hF,max_eq_left (sub_nonpos.mpr hsat)]
      · have hh := (riesz_three_clipped_sum hsp.of_mul_right hac
          (by linarith : 0 ≤ L-Real.log P)).2
        have hmin (p : ℕ) : min (L-Real.log P) (Real.log p) =
            Real.log p-max 0 (Real.log p-(L-Real.log P)) := by
          simp only [min_def,max_def]
          split_ifs <;> linarith
        simp_rw [hmin] at hh
        rw [Finset.sum_sub_distrib,← CoprimeEulerPhase.squarefree_log_eq_prime_sum hsp.of_mul_right,
          hfa] at hh
        have hbase : Real.log a-2*(L-Real.log P) = Real.log P+Real.log n-2*L := by linarith
        convert hh using 2
        dsimp [F]
        linarith
    rw [hcR,show max 0 ((Real.log n/L)*VaughanLogAverage.riesz (L-Real.log P) a) =
      (Real.log n/L)*max 0 (VaughanLogAverage.riesz (L-Real.log P) a) by
        rw [mul_max_of_nonneg _ _ hscale,mul_zero],hpos]
  · simp [positiveAllowance,SquarefreeVaughanLogSource.coefficient,hs]

/-- The old largest-prime upper bound never improves the exact allowance. -/
theorem positiveAllowance_le_gap {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    positiveAllowance L n ≤
      (Real.log n/L)*max 0 (Real.log (largestPrime n)+Real.log n-2*L) := by
  rw [positiveAllowance_eq hc hL hLhi hLlo]
  exact max_le (by positivity) (actual_four_signed_gap hc hL hLhi hLlo).2

/-- Every cofactor prime supplies an additional reflected-cutoff bound.
In particular a second reflected-large prime makes this debit vanish. -/
theorem positiveAllowance_le_cofactor_gap {n q : ℕ}
    (hq : q ∈ n.primeFactors.erase (largestPrime n)) {L : ℝ} (hL : 0 < L) :
    positiveAllowance L n ≤ (Real.log n/L)*max 0 (Real.log n-L-Real.log q) := by
  by_cases hs : Squarefree n
  · have hsingle := Finset.single_le_sum (s := n.primeFactors.erase (largestPrime n))
      (f := fun p : ℕ => max 0 (Real.log p-(L-Real.log (largestPrime n))))
      (fun _ _ => le_max_left _ _) hq
    have hterm := le_max_right 0 (Real.log q-(L-Real.log (largestPrime n)))
    unfold positiveAllowance
    rw [if_pos hs]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    exact max_le_max le_rfl (by linarith)
  · simp only [positiveAllowance,if_neg hs]
    positivity

/-- No adverse negative-cosine charge remains on the entire two
reflected-large-prime sector, not just on a sampled log-share box. -/
theorem positiveAllowance_eq_zero_of_second_large {n q : ℕ}
    (hq : q ∈ n.primeFactors.erase (largestPrime n)) {L : ℝ} (hL : 0 < L)
    (hlarge : Real.log n-L ≤ Real.log q) : positiveAllowance L n = 0 := by
  have h := positiveAllowance_le_cofactor_gap hq hL
  rw [max_eq_left (by linarith : Real.log n-L-Real.log q ≤ 0),mul_zero] at h
  exact le_antisymm h (positiveAllowance_nonneg hL n)

private theorem min_sum_bound {S : Finset ℕ} {r : ℕ} (hr : r ∈ S) (D : ℝ) :
    (∑ p ∈ S, min D (Real.log p)) ≤
      ((S.erase r).card : ℝ)*D+Real.log r := by
  have he := Finset.sum_erase_add S (fun p : ℕ => min D (Real.log p)) hr
  have hb := Finset.sum_le_sum (s := S.erase r) (fun p _ => min_le_left D (Real.log p))
  simp only [Finset.sum_const,nsmul_eq_mul] at hb
  linarith [min_le_right D (Real.log r)]

private theorem positive_balance_eq_clipped {n : ℕ} (hs : Squarefree n)
    (hP : largestPrime n ∈ n.primeFactors) (L : ℝ) :
    Real.log (largestPrime n)+Real.log n-2*L-
        (∑ p ∈ n.primeFactors.erase (largestPrime n),
          max 0 (Real.log p-(L-Real.log (largestPrime n)))) =
      (∑ p ∈ n.primeFactors.erase (largestPrime n),
        min (L-Real.log (largestPrime n)) (Real.log p))-2*(L-Real.log (largestPrime n)) := by
  have hm (p : ℕ) : min (L-Real.log (largestPrime n)) (Real.log p) =
      Real.log p-max 0 (Real.log p-(L-Real.log (largestPrime n))) := by
    simp only [min_def,max_def]
    split_ifs <;> linarith
  simp_rw [hm]
  rw [Finset.sum_sub_distrib]
  have hslog := Finset.sum_erase_add n.primeFactors (fun p : ℕ => Real.log p) hP
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hslog
  linarith

/-- The four-prime positive coefficient costs at most one logarithm of
ANY cofactor prime. This removes the spurious small-prime singular cost. -/
theorem positiveAllowance_le_cofactor_log {n r : ℕ} (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors.erase (largestPrime n)) {L : ℝ} (hL : 0 < L) :
    positiveAllowance L n ≤ (Real.log n/L)*Real.log r := by
  by_cases hs : Squarefree n
  · have hP := largestPrime_mem_of_four hc
    have hb := min_sum_bound hr (L-Real.log (largestPrime n))
    have hcard : ((n.primeFactors.erase (largestPrime n)).erase r).card = 2 := by
      rw [Finset.card_erase_of_mem hr,Finset.card_erase_of_mem hP,hc]
    rw [hcard] at hb
    norm_num at hb
    unfold positiveAllowance
    rw [if_pos hs,positive_balance_eq_clipped hs hP L]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    exact max_le (Real.log_natCast_nonneg r) (by linarith)
  · simp only [positiveAllowance,if_neg hs]
    positivity

/-- The marked-prime bound also includes the largest prime. -/
theorem positiveAllowance_le_marked_log {n r : ℕ} (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors) {L : ℝ} (hL : 0 < L) :
    positiveAllowance L n ≤ (Real.log n/L)*Real.log r := by
  by_cases hrP : r = largestPrime n
  · have hP := largestPrime_mem_of_four hc
    have hcard : (n.primeFactors.erase (largestPrime n)).card = 3 := by
      rw [Finset.card_erase_of_mem hP,hc]
    obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0 < (n.primeFactors.erase (largestPrime n)).card by omega)
    have hq' := Finset.mem_of_mem_erase hq
    have hne : n.primeFactors.Nonempty := ⟨q,hq'⟩
    have hqp : q ≤ largestPrime n := by
      rw [largestPrime,dif_pos hne]
      exact Finset.le_max' _ _ hq'
    have hlog : Real.log q ≤ Real.log (largestPrime n) :=
      Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq').pos)
      (by exact_mod_cast hqp)
    rw [hrP]
    exact (positiveAllowance_le_cofactor_log hc hq hL).trans
      (mul_le_mul_of_nonneg_left hlog (div_nonneg (Real.log_natCast_nonneg n) hL.le))
  · exact positiveAllowance_le_cofactor_log hc (Finset.mem_erase.mpr ⟨hrP,hr⟩) hL

/-- The previously evaluated negative coefficient has the same marked
logarithm budget; no factorial or phase factor has been changed. -/
theorem negativeAllowance_le_marked_log {n r : ℕ} (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors) {L : ℝ} (hL : 0 < L) :
    negativeAllowance L n ≤ (Real.log n/L)*Real.log r := by
  by_cases hs : Squarefree n
  · have hb := min_sum_bound hr (Real.log n-L)
    rw [Finset.card_erase_of_mem hr,hc] at hb
    norm_num at hb
    unfold negativeAllowance
    rw [if_pos hs,← clipped_sum_eq_excess hs L]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    exact max_le (Real.log_natCast_nonneg r) (by linarith)
  · simp only [negativeAllowance,if_neg hs]
    positivity

/-- A uniform norm budget for every original four-prime coefficient, in
the actual core length range. It uses any marked prime, including small ones. -/
theorem norm_coefficient_le_marked_log {n r : ℕ} (hc : n.primeFactors.card = 4)
    (hr : r ∈ n.primeFactors) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤ (Real.log n/L)*Real.log r := by
  have hp := positiveAllowance_le_marked_log hc hr hL
  have hn := negativeAllowance_le_marked_log hc hr hL
  rw [positiveAllowance_eq hc hL hLhi hLlo] at hp
  rw [negativeAllowance_eq hc hL hLhi hLlo] at hn
  have hp' := (le_max_right 0 (SquarefreeVaughanLogSource.coefficient L n).re).trans hp
  have hn' := (le_max_right 0 (-(SquarefreeVaughanLogSource.coefficient L n).re)).trans hn
  have hi : (SquarefreeVaughanLogSource.coefficient L n).im = 0 := by
    unfold SquarefreeVaughanLogSource.coefficient
    split_ifs <;> rfl
  have he := Complex.re_add_im (SquarefreeVaughanLogSource.coefficient L n)
  rw [hi,Complex.ofReal_zero,zero_mul,add_zero] at he
  rw [← he,Complex.norm_real,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith,hp'⟩

/-- The exact negative part of an observed four-prime coefficient, on
both cosine signs. This replaces neither the carrier nor its phase. -/
def exactDebit (L y : ℝ) (n : ℕ) : ℝ :=
  negativeAllowance L n*max 0 (Real.cos (y*Real.log n))+
    positiveAllowance L n*max 0 (-Real.cos (y*Real.log n))

theorem exactDebit_nonneg {L : ℝ} (hL : 0 < L) (y : ℝ) (n : ℕ) :
    0 ≤ exactDebit L y n := by
  exact add_nonneg (mul_nonneg (negativeAllowance_nonneg hL n) (le_max_left _ _))
    (mul_nonneg (positiveAllowance_nonneg hL n) (le_max_left _ _))

/-- Pointwise improvement over the current four-prime debit, with all
finite masks and the observed cosine retained. -/
theorem exactDebit_le_fourDebit {n : ℕ} (hc : n.primeFactors.card = 4)
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ) :
    exactDebit L y n ≤ fourDebit L y n := by
  unfold exactDebit fourDebit
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (positiveAllowance_le_gap hc hL hLhi hLlo) (le_max_left _ _))

open ZetaRieszOneSidedArithmetic ZetaRieszJointAllocation

/-- No coefficient slack remains on either phase side. The right-hand
side is the full original observed atom, not a surrogate completion. -/
theorem re_four_atom_eq_keep_positive (A : Finset ℕ) (N : ℕ) {n : ℕ}
    (hc : n.primeFactors.card = 4) {L : ℝ} (hL : 0 < L)
    (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L) (y : ℝ) :
    (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      max (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re 0-
        weight A N n*exactDebit L y n := by
  rw [exactDebit,negativeAllowance_eq hc hL hLhi hLlo,positiveAllowance_eq hc hL hLhi hLlo]
  have he (c x : ℝ) : max (c*x) 0-(max 0 (-c)*max 0 x+max 0 c*max 0 (-x)) = c*x := by
    rcases le_total c 0 with hc | hc <;> rcases le_total x 0 with hx | hx
    · rw [max_eq_left hc,max_eq_left hx,max_eq_right (neg_nonneg.mpr hc),
        max_eq_right (neg_nonneg.mpr hx),max_eq_left (mul_nonneg_of_nonpos_of_nonpos hc hx)]
      ring
    · rw [max_eq_left hc,max_eq_right hx,max_eq_right (neg_nonneg.mpr hc),
        max_eq_left (neg_nonpos.mpr hx),max_eq_right (mul_nonpos_of_nonpos_of_nonneg hc hx)]
      ring
    · rw [max_eq_right hc,max_eq_left hx,max_eq_left (neg_nonpos.mpr hc),
        max_eq_right (neg_nonneg.mpr hx),max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hx)]
      ring
    · rw [max_eq_right hc,max_eq_right hx,max_eq_left (neg_nonpos.mpr hc),
        max_eq_left (neg_nonpos.mpr hx),max_eq_left (mul_nonneg hc hx)]
      ring
  have hm := congrArg (fun z => weight A N n*z)
    (he (SquarefreeVaughanLogSource.coefficient L n).re (Real.cos (y*Real.log n)))
  rw [mul_sub,mul_max_of_nonneg _ _ (weight_nonneg A N n),mul_zero] at hm
  simpa only [re_residual_atom,mul_assoc] using hm.symm

/-- An entire previously overcharged phase sector is independently
nonnegative: a second reflected-large prime kills its positive coefficient. -/
theorem re_four_atom_nonneg_of_second_large (A : Finset ℕ) (N : ℕ) {n q : ℕ}
    (hc : n.primeFactors.card = 4) (hq : q ∈ n.primeFactors.erase (largestPrime n))
    {L : ℝ} (hL : 0 < L) (hLhi : L ≤ Real.log n) (hLlo : 2*Real.log n ≤ 3*L)
    (hlarge : Real.log n-L ≤ Real.log q) (y : ℝ)
    (hcos : Real.cos (y*Real.log n) ≤ 0) :
    0 ≤ (residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n).re := by
  rw [re_four_atom_eq_keep_positive A N hc hL hLhi hLlo y,exactDebit,
    positiveAllowance_eq_zero_of_second_large hq hL hlarge,
    max_eq_left hcos,mul_zero,zero_mul,add_zero,mul_zero,sub_zero]
  exact le_max_right _ _

/-- A stronger signed comparison on the original finite sum. Four-prime
debits are now exact on both phase sides; all other terms stay unchanged. -/
theorem re_sum_eq_four_five_credit (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 →
      L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L ∧ 4*L ≤ 3*Real.log n) :
    let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
    (∑ n ∈ S, f n).re = ∑ n ∈ S, if n.primeFactors.card = 4 then
      max (f n).re 0-weight A N n*exactDebit L y n
      else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
        max (f n).re 0-weight A N n*ZetaRieszFivePrimeReserve.positiveAllowance L n*(-Real.cos (y*Real.log n))
      else (f n).re := by
  dsimp only
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hfour hfive
  · have hw := hwindow n hn (Or.inl hfour)
    exact re_four_atom_eq_keep_positive A N hfour hL hw.1 hw.2.1 y
  · have hw := hwindow n hn (Or.inr hfive.1)
    exact ZetaRieszFivePrimeReserve.re_five_atom_eq_keep_positive A N hfive.1 hL hw.2.1 hw.2.2 y hfive.2
  · rfl

/-- The exact observed debit raises the old lower comparison, pointwise
and after arbitrary finite selection, without deleting any signed credit. -/
theorem signed_floor_improves_previous (S A : Finset ℕ) (N : ℕ) {L : ℝ} (hL : 0 < L) (y : ℝ)
    (hwindow : ∀ n ∈ S, n.primeFactors.card = 4 → L ≤ Real.log n ∧ 2*Real.log n ≤ 3*L)
    (credit rest : ℕ → ℝ) :
    (∑ n ∈ S, if n.primeFactors.card = 4 then credit n-weight A N n*fourDebit L y n else rest n) ≤
      ∑ n ∈ S, if n.primeFactors.card = 4 then credit n-weight A N n*exactDebit L y n else rest n := by
  apply Finset.sum_le_sum
  intro n hn
  split_ifs with hc
  · have hw := hwindow n hn hc
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (exactDebit_le_fourDebit hc hL hw.1 hw.2 y) (weight_nonneg A N n)) _
  · exact le_rfl

open ZetaRieszParityPacket ZetaRieszPrimeCountFrequency ZetaRieszRadialCompensation
open ZetaRieszSmallPrimeCompensation

/-- Both paid triple populations and the one unspent supply remain in
the same joint floor. The exact four-prime debit is applied only to the
untouched complement, so no supply or overlap is spent twice. -/
theorem eventually_compensated_core_floor {u y : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hy : 16 ≤ |y|) :
    ∃ η h r C : ℝ, 0 < η ∧ η ≤ 1/1000 ∧ 0 < h ∧ h ≤ 1/20 ∧
      0 ≤ r ∧ r < 1 ∧ 0 ≤ C ∧
      ∀ᶠ j : ℕ in atTop, ∃ v : ℕ → ℝ,
        (∀ M ∈ radialIndices (dyadicMomentOrder j), 0 ≤ v M ∧ v M ≤ 1/2) ∧
        let N := dyadicMomentOrder j
        let L := SquarefreeVaughanLogSource.length u N
        let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
        let S := coreBand u N (dyadicPrimeCount j)
        let f := fun n => residualCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n
        let Xs := radialTriples S N η
        let Zs := radialSmallTriples (S\Xs) N
        let X := ∑ n ∈ Xs, f n
        let Z := ∑ n ∈ Zs, f n
        let Y := ∑ n ∈ radialSupply N h v, f n
        let W := S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N)
        let B := ∑ n ∈ W, if n.primeFactors.card = 4 then
          max (f n).re 0-weight A N n*exactDebit L y n
          else if n.primeFactors.card = 5 ∧ Real.cos (y*Real.log n) ≤ 0 then
            max (f n).re 0-weight A N n*ZetaRieszFivePrimeReserve.positiveAllowance L n*(-Real.cos (y*Real.log n))
          else (f n).re
        0 < Y.re ∧
          u^(N+1)*(B+max X.re 0+max Z.re 0+Y.re/4)-r^N*C ≤
            ((u : ℂ)^(N+1)*coreResponse u y N (dyadicPrimeCount j)).re := by
  obtain ⟨η,h,r,C,hη,hηu,hh,hhu,hr,hr1,hC,hfloor⟩ := eventually_core_small_balanced_floor hu hU hy
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
  let A := ZetaRieszAnnulusJoint.intermediatePrimes u N
  let S := coreBand u N (dyadicPrimeCount j)
  let Xs := radialTriples S N η
  let Zs := radialSmallTriples (S\Xs) N
  let W := S\(Xs ∪ Zs ∪ radialSupply N h v ∪ balancedTriples S N η ∪ smallHead S N)
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
  have hb := re_sum_eq_four_five_credit W A N
    (SquarefreeVaughanLogSource.length_pos u N) y hwindow
  refine ⟨v,hv,hY,?_⟩
  apply le_trans _ hfloor
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ u) (N+1))
  exact add_le_add (add_le_add (add_le_add hb.symm.le le_rfl) le_rfl) le_rfl

end
end RiemannGaussian.ZetaRieszFourPrimeExact
