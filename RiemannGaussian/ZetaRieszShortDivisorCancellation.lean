/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerGapRows

/-!
# Exact cancellation in the unpaid short-divisor boundary

A complete composite divisor block cancels both affine hinge channels
before the common allocation, factorial weight or phase is estimated.
The block is a literal suballocation of the current owner convolution.
Its geometry keeps every member outside the already paid closed rows.
No estimate for the remaining clipped crossings is inferred.
-/

noncomputable section
open Filter Topology Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszShortDivisorCancellation
open ZetaRieszSignedConvolution ZetaRieszPrimeEndpoint ZetaRieszParityPacket
open ZetaRieszOwnerGapRows

private theorem cofactor_log {a p d : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hd : d ∣ a) :
    log p+log (a/d : ℕ) = log (p*a : ℕ)-log d := by
  have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero ha.ne_zero)).ne'
  have hb0 : a/d ≠ 0 := by
    intro hz
    have hh := Nat.mul_div_cancel' hd
    rw [hz,mul_zero] at hh
    exact ha.ne_zero hh.symm
  have he : log a = log d+log (a/d : ℕ) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hd]
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hd0) (by exact_mod_cast hb0)]
  rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero),he]
  ring

/-- On a complete divisor block, the original two-hinge coefficient is
affine when neither hinge crosses the block. All endpoint cases are kept. -/
theorem block_hinge_affine {a p R d : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hd : d ∈ R.divisors) {L : ℝ}
    (hR : log R ≤ log (p*a : ℕ)-L)
    (hside : log (p*a : ℕ)-L ≤ log p ∨
      log p+log R ≤ log (p*a : ℕ)-L) :
    pairHinge L p (a/d) =
      if log (p*a : ℕ)-L ≤ log p then log (p*a : ℕ)-L-log d else log p := by
  have hdR := Nat.dvd_of_mem_divisors hd
  have hda := hdR.trans hRa
  have hd0 : (0 : ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hR0 : 0 < R := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
  have hle : log d ≤ log R := log_le_log hd0 (by
    exact_mod_cast Nat.le_of_dvd hR0 hdR)
  have hl := cofactor_log ha hp hda
  unfold pairHinge
  by_cases hs : log (p*a : ℕ)-L ≤ log p
  · rw [if_pos hs,max_eq_right (by linarith : 0 ≤ log p+log (a/d : ℕ)-L),
      max_eq_left (by linarith [log_natCast_nonneg d] : log (a/d : ℕ)-L ≤ 0)]
    linarith
  · have hh := hside.resolve_left hs
    rw [if_neg hs,max_eq_right (by linarith : 0 ≤ log p+log (a/d : ℕ)-L),
      max_eq_right (by linarith : 0 ≤ log (a/d : ℕ)-L)]
    ring

/-- A composite squarefree block cancels the constant and first log
moment jointly. This is an exact signed equality, not a norm allowance. -/
theorem signed_block_eq_zero {a p R : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hcount : 2 ≤ R.primeFactors.card) {L : ℝ}
    (hR : log R ≤ log (p*a : ℕ)-L)
    (hside : log (p*a : ℕ)-L ≤ log p ∨
      log p+log R ≤ log (p*a : ℕ)-L) :
    (∑ d ∈ R.divisors, (μ (a/d) : ℝ)*pairHinge L p (a/d)) = 0 := by
  have hs : Squarefree R := ha.squarefree_of_dvd hRa
  have hne : R ≠ 1 := by intro h; simp [h] at hcount
  have hsum : (∑ d ∈ R.divisors, (μ d : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hne
  have hlogsum : (∑ d ∈ R.divisors, (μ d : ℝ)*log d) = 0 := by
    simpa only [ArithmeticFunction.log_apply,
      vonMangoldt_zero_of_squarefree_count hs hcount,neg_zero] using
      (ArithmeticFunction.sum_moebius_mul_log_eq (n := R))
  calc
    _ = ∑ d ∈ R.divisors, (μ a : ℝ)*(μ d : ℝ)*
        (if log (p*a : ℕ)-L ≤ log p then log (p*a : ℕ)-L-log d else log p) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [moebius_cofactor_real ha ((Nat.dvd_of_mem_divisors hd).trans hRa),
        block_hinge_affine ha hp hRa hd hR hside]
    _ = 0 := by
      split_ifs
      · calc
          _ = (μ a : ℝ)*(∑ d ∈ R.divisors,
              (μ d : ℝ)*(log (p*a : ℕ)-L-log d)) := by
            simp only [Finset.mul_sum,mul_assoc]
          _ = (μ a : ℝ)*((log (p*a : ℕ)-L)*(∑ d ∈ R.divisors, (μ d : ℝ))-
              ∑ d ∈ R.divisors, (μ d : ℝ)*log d) := by
            congr 1
            rw [Finset.mul_sum,← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro d _
            ring
          _ = 0 := by rw [hsum,hlogsum]; ring
      · rw [← Finset.sum_mul,← Finset.mul_sum,hsum]
        ring

/-- The original complex observation is common to every incidence in
the block. It may contain every original mask and allocation unchanged. -/
theorem weighted_block_eq_zero {a p R : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hcount : 2 ≤ R.primeFactors.card) {L : ℝ}
    (hR : log R ≤ log (p*a : ℕ)-L)
    (hside : log (p*a : ℕ)-L ≤ log p ∨
      log p+log R ≤ log (p*a : ℕ)-L) (w : ℂ) :
    (∑ d ∈ R.divisors, w*(μ (a/d) : ℂ)*(pairHinge L p (a/d) : ℂ)) = 0 := by
  have h := congrArg (fun x : ℝ => w*(x : ℂ))
    (signed_block_eq_zero ha hp hRa hcount hR hside)
  push_cast at h
  simpa only [Finset.mul_sum,mul_assoc,mul_zero] using h

/-- The block uses actual original divisor incidences, once each. -/
def blockDivisors (a R : ℕ) : Finset (ℕ×ℕ) :=
  R.divisors.image (fun d => (d,a/d))

theorem blockDivisors_subset {a R : ℕ} (ha : 0 < a) (hRa : R ∣ a) :
    blockDivisors a R ⊆ a.divisorsAntidiagonal := by
  intro db hdb
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hdb
  exact Nat.mem_divisorsAntidiagonal.mpr
    ⟨Nat.mul_div_cancel' ((Nat.dvd_of_mem_divisors hd).trans hRa),ha.ne'⟩

/-- A complete original block is removed with exactly zero error,
including its unsigned unit incidence and every low factorial order. -/
theorem literal_block_eq_zero {a p R : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (hcount : 2 ≤ R.primeFactors.card) {L : ℝ}
    (hR : log R ≤ log (p*a : ℕ)-L)
    (hside : log (p*a : ℕ)-L ≤ log p ∨
      log p+log R ≤ log (p*a : ℕ)-L) (A : Finset ℕ) (N : ℕ) (y : ℝ) :
    (∑ db ∈ blockDivisors a R,
      phaseWeight A L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) = 0 := by
  rw [blockDivisors,Finset.sum_image (by
    intro d _ e _ he
    exact congrArg Prod.fst he)]
  exact weighted_block_eq_zero ha hp hRa hcount hR hside _

/-- The full block retains both signed Riesz cutoffs. This equality is
used below to bound the joined block and identify its only surviving tent. -/
theorem signed_block_riesz_difference {a p R : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hRa : R ∣ a) (L : ℝ) :
    (∑ d ∈ R.divisors, (μ (a/d) : ℝ)*pairHinge L p (a/d)) =
      (μ a : ℝ)*(VaughanLogAverage.riesz (log (p*a : ℕ)-L) R-
        VaughanLogAverage.riesz (log a-L) R) := by
  unfold VaughanLogAverage.riesz
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hda := (Nat.dvd_of_mem_divisors hd).trans hRa
  have hl := cofactor_log ha hp hda
  have ht : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  rw [moebius_cofactor_real ha hda,pairHinge,
    show log p+log (a/d : ℕ)-L=log (p*a : ℕ)-L-log d by linarith,
    show log (a/d : ℕ)-L=log a-L-log d by linarith]
  ring

private theorem riesz_two_prime_value {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (D : ℝ) :
    VaughanLogAverage.riesz D (r*s) =
      ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) D := by
  have hh := ZetaSquarefreeRieszWindows.riesz_two_primes_eq_tent D hr hs hrs
    (show ¬r ∣ 1 from hr.not_dvd_one) (show ¬s ∣ 1 from hs.not_dvd_one)
  simpa only [mul_one,Nat.divisors_one,Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,log_one,sub_zero,one_mul] using hh

/-- Summing the unit and all three nonunit incidences first leaves ONE
signed cofactor tent. Its value is independent of the marked prime;
the original phase and owner weight remain in the common `w`. -/
theorem two_prime_block_eq_cofactor_tent {a p r s : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hRa : r*s ∣ a) {L : ℝ} (hR : log (r*s : ℕ) ≤ log (p*a : ℕ)-L) (w : ℂ) :
    (∑ db ∈ blockDivisors a (r*s),
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -w*(μ a : ℂ)*
        (ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) (log a-L) : ℂ) := by
  have hlog : log (r*s : ℕ)=log r+log s := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hr.ne_zero) (by exact_mod_cast hs.ne_zero)]
  have hzero := ZetaSquarefreeRieszWindows.primePairTent_eq_zero_of_outside
    (log_natCast_nonneg r) (log_natCast_nonneg s) (Or.inr (hlog ▸ hR))
  have he := signed_block_riesz_difference ha hp hRa L
  rw [riesz_two_prime_value hr hs hrs,riesz_two_prime_value hr hs hrs,hzero,zero_sub] at he
  have hh := congrArg (fun x : ℝ => w*(x : ℂ)) he
  push_cast at hh
  rw [blockDivisors,Finset.sum_image (by
    intro d _ e _ h
    exact congrArg Prod.fst h)]
  simpa only [Finset.mul_sum,mul_assoc,mul_neg,neg_mul] using hh

/-- The exact remaining block cost is a least-prime-width tent rather
than four independent full-length unit charges. No norm of the whole
carrier or decay of the reflected crossing is inferred. -/
theorem norm_two_prime_block_le {a p r s : ℕ} (ha : Squarefree a)
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hRa : r*s ∣ a) {L : ℝ} (hR : log (r*s : ℕ) ≤ log (p*a : ℕ)-L) (w : ℂ) :
    ‖∑ db ∈ blockDivisors a (r*s),
      w*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)‖ ≤ ‖w‖*min (log r) (log s) := by
  have ht := ZetaSquarefreeRieszWindows.primePairTent_bounds
    (log_natCast_nonneg r) (log_natCast_nonneg s) (log a-L)
  have hm : ‖(μ a : ℂ)‖ ≤ 1 := by
    have h : |(μ a : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h
  rw [two_prime_block_eq_cofactor_tent ha hp hr hs hrs hRa hR w,
    norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
  calc
    _ ≤ ‖w‖*ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) (log a-L) :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg w) hm) ht.1
    _ ≤ _ := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg w)

/-- Join every retained marked prime before observing the compact
cofactor tent. The finite set may retain all original period/count masks. -/
theorem prime_block_sum_eq (P : Finset ℕ) {a r s : ℕ} (ha : Squarefree a)
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (hRa : r*s ∣ a) {L : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (hR : ∀ p ∈ P, log (r*s : ℕ) ≤ log (p*a : ℕ)-L) (w : ℕ → ℂ) :
    (∑ p ∈ P, ∑ db ∈ blockDivisors a (r*s),
      w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)) =
      -(∑ p ∈ P, w p)*(μ a : ℂ)*
        (ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) (log a-L) : ℂ) := by
  calc
    _ = ∑ p ∈ P, -w p*(μ a : ℂ)*
        (ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) (log a-L) : ℂ) :=
      Finset.sum_congr rfl (fun p hp => two_prime_block_eq_cofactor_tent
        ha (hP p hp) hr hs hrs hRa (hR p hp) (w p))
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul,Finset.sum_neg_distrib]

/-- An independent signed floor for the joined four-incidence prime
row. Its cost uses the actual SIGNED constant prime moment after all
periods in `P` are joined, not a sum of absolute prime observations. -/
theorem re_prime_block_floor (P : Finset ℕ) {a r s : ℕ} (ha : Squarefree a)
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (hRa : r*s ∣ a) {L : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (hR : ∀ p ∈ P, log (r*s : ℕ) ≤ log (p*a : ℕ)-L) (w : ℕ → ℂ) :
    -min (log r) (log s)*|(∑ p ∈ P, w p).re| ≤
      (∑ p ∈ P, ∑ db ∈ blockDivisors a (r*s),
        w p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re := by
  have ht := ZetaSquarefreeRieszWindows.primePairTent_bounds
    (log_natCast_nonneg r) (log_natCast_nonneg s) (log a-L)
  have hm : |(μ a : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
  have he := prime_block_sum_eq P ha hr hs hrs hRa hP hR w
  rw [he,show (μ a : ℂ)=((μ a : ℝ) : ℂ) by push_cast; rfl]
  have hab : |-(μ a : ℝ)*
      ZetaSquarefreeRieszWindows.primePairTent (log r) (log s) (log a-L)*
        (∑ p ∈ P, w p).re| ≤ min (log r) (log s)*|(∑ p ∈ P, w p).re| := by
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left ht.1 hm).trans ht.2) (abs_nonneg _)
  have hlo := (abs_le.mp hab).1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.neg_im,mul_zero,sub_zero]
  convert hlo using 1 <;> first | rfl | ring

/-- The signed prime-row floor with the literal current factorial,
allocation, moving-length parameter and full complex phase. The caller's
finite prime set retains every original physical/core/count/owner mask. -/
theorem re_literal_prime_block_floor (P : Finset ℕ) (A : ℕ → Finset ℕ)
    {a r s : ℕ} (ha : Squarefree a) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hRa : r*s ∣ a) {L : ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (hR : ∀ p ∈ P, log (r*s : ℕ) ≤ log (p*a : ℕ)-L) (N : ℕ) (y : ℝ) :
    -min (log r) (log s)*|(∑ p ∈ P, phaseWeight (A (p*a)) L N y a p).re| ≤
      (∑ p ∈ P, ∑ db ∈ blockDivisors a (r*s),
        phaseWeight (A (p*a)) L N y a p*(μ db.2 : ℂ)*(pairHinge L p db.2 : ℂ)).re :=
  re_prime_block_floor P ha hr hs hrs hRa hP hR (fun p => phaseWeight (A (p*a)) L N y a p)

/-- The deterministic two-smallest-cofactor-prime candidate. Membership
below checks its literal divisibility and count, rather than assuming them. -/
def leastPairBlock (a : ℕ) : ℕ := a.minFac*(a/a.minFac).minFac

/-- The deterministic candidate consists of two distinct genuine
cofactor primes. Its divisibility and count follow from squarefreeness. -/
theorem leastPairBlock_data {a : ℕ} (ha : Squarefree a)
    (hc : 2 ≤ a.primeFactors.card) :
    leastPairBlock a ∣ a ∧ (leastPairBlock a).primeFactors.card = 2 := by
  have ha1 : a ≠ 1 := by intro h; simp [h] at hc
  have hr := Nat.minFac_prime ha1
  have hd := Nat.minFac_dvd a
  have he : a.minFac*(a/a.minFac)=a := Nat.mul_div_cancel' hd
  have hquot : a/a.minFac ≠ 1 := by
    intro h
    have hh : a=a.minFac := by rw [h,mul_one] at he; exact he.symm
    rw [hh,hr.primeFactors,Finset.card_singleton] at hc
    omega
  have hs := Nat.minFac_prime hquot
  have hcop := Nat.coprime_of_squarefree_mul (he.symm ▸ ha)
  have hrs : a.minFac ≠ (a/a.minFac).minFac := by
    intro h
    have hmin := Nat.minFac_dvd (a/a.minFac)
    rw [← h] at hmin
    exact (hr.coprime_iff_not_dvd.mp hcop) hmin
  constructor
  · unfold leastPairBlock
    exact (Nat.mul_dvd_mul_left a.minFac (Nat.minFac_dvd (a/a.minFac))).trans (dvd_of_eq he)
  · rw [leastPairBlock,Nat.primeFactors_mul hr.ne_zero hs.ne_zero,
      hr.primeFactors,hs.primeFactors]
    simp [hrs]

/-- Exact sufficient geometry for a zero-cost suballocation of the
CURRENT unpaid short boundary. This does not change the moving cutoff. -/
def ShortBlock (u : ℝ) (N n R : ℕ) : Prop :=
  let p := largestPrime n
  let a := n/p
  let T := log (p*a : ℕ)
  let L := SquarefreeVaughanLogSource.length u N
  R ∣ a ∧ 2 ≤ R.primeFactors.card ∧
    log R < T-(3899/2000 : ℝ)*N ∧ log R ≤ T-L ∧
    (T-L ≤ log p ∨ log p+log R ≤ T-L) ∧
    log p < (243/200 : ℝ)*N

/-- Only the cancelling divisor incidences of an original label are
selected; all remaining incidences keep their signs and full weights. -/
def cancelledDivisors (u : ℝ) (N n : ℕ) : Finset (ℕ×ℕ) :=
  let a := n/largestPrime n
  let R := leastPairBlock a
  if ShortBlock u N n R then blockDivisors a R else ∅

private theorem core_data {u : ℝ} {N K n : ℕ} (hn : n ∈ coreBand u N K)
    (hs : Squarefree n) :
    (largestPrime n).Prime ∧ Squarefree (n/largestPrime n) := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  exact ⟨Nat.prime_of_mem_primeFactors hp,
    (ZetaRieszMarkedSaturation.cofactor_data hs hc hp).1⟩

theorem cancelledDivisors_subset {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) :
    cancelledDivisors u N n ⊆ (n/largestPrime n).divisorsAntidiagonal := by
  unfold cancelledDivisors
  dsimp only
  split_ifs with h
  · exact blockDivisors_subset (Nat.pos_of_ne_zero (core_data hn hs).2.ne_zero) h.1
  · exact Finset.empty_subset _

/-- The unpaid unsigned unit is included in every selected cancelling
block. It is not discarded or estimated separately. -/
theorem unsigned_unit_mem_cancelled {u : ℝ} {N n : ℕ}
    (h : ShortBlock u N n (leastPairBlock (n/largestPrime n))) :
    (1,n/largestPrime n) ∈ cancelledDivisors u N n := by
  have hR0 : leastPairBlock (n/largestPrime n) ≠ 0 := by
    intro hz
    have hc := h.2.1
    simp [hz] at hc
  rw [cancelledDivisors,if_pos h,blockDivisors]
  apply Finset.mem_image.mpr
  exact ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hR0⟩,by simp⟩

/-- Every selected incidence lies on the originally unpaid outer-log
boundary, strictly beyond the paid full-window row cutoff. -/
theorem cancelled_outer_log_gt {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ cancelledDivisors u N n) :
    (3899/2000 : ℝ)*N < log (largestPrime n*b : ℕ) := by
  have hdbOrig := hdb
  unfold cancelledDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · obtain ⟨e,he,hpair⟩ := Finset.mem_image.mp hdb
    have heb : (n/largestPrime n)/e=b := congrArg Prod.snd hpair
    have heR := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp he).2)
      (Nat.dvd_of_mem_divisors he)
    have hle : log e ≤ log (leastPairBlock (n/largestPrime n)) := log_le_log
      (by exact_mod_cast Nat.pos_of_mem_divisors he)
      (by exact_mod_cast heR)
    have hl := cofactor_log (core_data hn hs).2 (core_data hn hs).1
      ((Nat.dvd_of_mem_divisors he).trans h.1)
    rw [heb] at hl
    have hb0 : b ≠ 0 := by
      have hb := (Nat.ne_zero_of_mem_divisorsAntidiagonal
        ((cancelledDivisors_subset hn hs) hdbOrig)).2
      exact hb
    have hp0 := (core_data hn hs).1.ne_zero
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp0) (by exact_mod_cast hb0)]
    have hshort := h.2.2.1
    linarith
  · simp only [Finset.notMem_empty] at hdb

theorem cancelled_not_ownerGapRows {u : ℝ} {N K n d b : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hdb : (d,b) ∈ cancelledDivisors u N n) :
    (largestPrime n,b) ∉ ownerGapRows u N := by
  intro h
  have hcut := (Finset.mem_filter.mp h).2.2.2.2.2.1
  linarith [cancelled_outer_log_gt hn hs hdb]

theorem cancelled_not_largeOwner {u : ℝ} {N K n d b : ℕ}
    (hdb : (d,b) ∈ cancelledDivisors u N n) :
    n ∉ ZetaRieszUnifiedSignedRows.largeOwnerLabels u N K := by
  unfold cancelledDivisors at hdb
  dsimp only at hdb
  split_ifs at hdb with h
  · intro hlarge
    have hcut := (Finset.mem_filter.mp hlarge).2.2.2.2.1
    have hP := h.2.2.2.2.2
    linarith
  · simp only [Finset.notMem_empty] at hdb

/-- The whole selected short-boundary population has exactly zero
complex contribution, at every height and every finite moment order. -/
theorem cancelled_literal_sum_eq_zero {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n) (y : ℝ) :
    (∑ db ∈ cancelledDivisors u N n,
      phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
        (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
        (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
          (largestPrime n) db.2 : ℂ)) = 0 := by
  unfold cancelledDivisors
  dsimp only
  split_ifs with h
  · exact literal_block_eq_zero (core_data hn hs).2 (core_data hn hs).1 h.1 h.2.1
      h.2.2.2.1 h.2.2.2.2.1 _ N y
  · exact Finset.sum_empty

/-- Removing all the selected zero blocks from the whole original
convolution is exact. No new carrier or signed remainder is substituted. -/
theorem coreConvolution_eq_sum_sdiff (u y : ℝ) (N K : ℕ) :
    coreConvolution u y N K =
      ∑ n ∈ (coreBand u N K).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \ cancelledDivisors u N n,
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
              (largestPrime n) db.2 : ℂ) := by
  unfold coreConvolution
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hcore,hs⟩ := Finset.mem_filter.mp hn
  have he := Finset.sum_sdiff (f := fun db : ℕ×ℕ =>
    phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
      (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
      (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
        (largestPrime n) db.2 : ℂ)) (cancelledDivisors_subset hcore hs)
  rw [cancelled_literal_sum_eq_zero hcore hs y,add_zero] at he
  exact he.symm

/-- The independent saving for the selected ORIGINAL short boundary is
exactly zero at source scale, uniformly in count, height and moment order. -/
theorem source_scaled_cancelled_norm_eq_zero (u y : ℝ) (N K : ℕ) :
    ‖(u : ℂ)^(N+1)*
      (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ cancelledDivisors u N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ))‖ = 0 := by
  have he : (∑ n ∈ (coreBand u N K).filter Squarefree, ∑ db ∈ cancelledDivisors u N n,
        phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u N ∩ {largestPrime n})
          (SquarefreeVaughanLogSource.length u N) N y (n/largestPrime n) (largestPrime n)*
          (μ db.2 : ℂ)*(pairHinge (SquarefreeVaughanLogSource.length u N)
            (largestPrime n) db.2 : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact cancelled_literal_sum_eq_zero (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 y
  rw [he,mul_zero,norm_zero]

/-- Outside the whole large-owner population, an uncancelled unsigned
unit must meet one of TWO explicit boundaries: its small block reaches
the short cutoff, or its owner crosses the reflected hinge within that
block's width. No phase or norm information has been discarded. -/
theorem uncancelled_unsigned_unit_geometry {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hs : Squarefree n)
    (hP : log (largestPrime n) < (243/200 : ℝ)*N)
    (hL : SquarefreeVaughanLogSource.length u N ≤ (3899/2000 : ℝ)*N)
    (hnot : (1,n/largestPrime n) ∉ cancelledDivisors u N n) :
    log n-(3899/2000 : ℝ)*N ≤
        log (leastPairBlock (n/largestPrime n)) ∨
      (log n-
        SquarefreeVaughanLogSource.length u N-log (leastPairBlock (n/largestPrime n)) <
          log (largestPrime n) ∧
       log (largestPrime n) < log n-
          SquarefreeVaughanLogSource.length u N) := by
  have hcore := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hd := ZetaRieszMarkedSaturation.cofactor_data hs hcore hp
  have hcnt : 2 ≤ (n/largestPrime n).primeFactors.card := by
    have he := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
    have hpp := (core_data hn hs).1
    have hc : n.primeFactors.card=(n/largestPrime n).primeFactors.card+1 := by
      conv_lhs => rw [← he,Nat.primeFactors_mul hpp.ne_zero hd.1.ne_zero,
        hpp.primeFactors,Finset.singleton_union,Finset.card_insert_of_notMem
          (show largestPrime n ∉ (n/largestPrime n).primeFactors from
            fun h => hd.2.2.2 (Nat.dvd_of_mem_primeFactors h))]
    omega
  have hdata := leastPairBlock_data hd.1 hcnt
  have he : largestPrime n*(n/largestPrime n)=n :=
    Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)
  by_contra h
  push Not at h
  have hshort : log (leastPairBlock (n/largestPrime n)) <
      log (largestPrime n*(n/largestPrime n) : ℕ)-(3899/2000 : ℝ)*N := by
    simpa only [he] using h.1
  have hR : log (leastPairBlock (n/largestPrime n)) ≤
      log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N := by
    linarith
  have hside : log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N ≤
      log (largestPrime n) ∨ log (largestPrime n)+log (leastPairBlock (n/largestPrime n)) ≤
        log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N := by
    by_cases hh : log (largestPrime n*(n/largestPrime n) : ℕ)-
        SquarefreeVaughanLogSource.length u N ≤ log (largestPrime n)
    · exact Or.inl hh
    · apply Or.inr
      have hhh := h.2
      have himp : log (largestPrime n*(n/largestPrime n) : ℕ)-
          SquarefreeVaughanLogSource.length u N-log (leastPairBlock (n/largestPrime n)) <
            log (largestPrime n) →
          log (largestPrime n*(n/largestPrime n) : ℕ)-SquarefreeVaughanLogSource.length u N ≤
            log (largestPrime n) := by
        simpa only [he] using hhh
      have hno : ¬log (largestPrime n*(n/largestPrime n) : ℕ)-
          SquarefreeVaughanLogSource.length u N-log (leastPairBlock (n/largestPrime n)) <
            log (largestPrime n) := fun hlt => hh (himp hlt)
      linarith
  exact hnot (unsigned_unit_mem_cancelled ⟨hdata.1,by omega,hshort,hR,hside,hP⟩)

/-- Any fixed polynomial small-prime block lies strictly below the
minimum unpaid short cutoff eventually. The threshold is unevaluated. -/
theorem eventually_logarithmic_block_short (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B*log ((N : ℝ)+1) < (N : ℝ)/2000 := by
  have hx : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun N : ℕ => B*log ((N : ℝ)+1)/((N : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,id_eq,mul_div_assoc,mul_zero] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hx).const_mul B
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ)<1/4000),
    eventually_ge_atTop 1] with N h hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh := (div_lt_iff₀ (by positivity : (0 : ℝ)<(N : ℝ)+1)).mp h
  linarith

/-- For polynomially small cofactor blocks, all surviving unsigned
units are confined to a logarithmic-width reflected-owner strip,
uniformly over the ORIGINAL labels and count cutoff. This is exact
support localization after signed cancellation, not a small norm bound. -/
theorem eventually_uncancelled_unit_logarithmic_strip {u : ℝ} (hu : 1/2 ≤ u)
    (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K n : ℕ, n ∈ coreBand u N K → Squarefree n →
      log (largestPrime n) < (243/200 : ℝ)*N →
      log (leastPairBlock (n/largestPrime n)) ≤ B*log ((N : ℝ)+1) →
      (1,n/largestPrime n) ∉ cancelledDivisors u N n →
      log n-SquarefreeVaughanLogSource.length u N-B*log ((N : ℝ)+1) < log (largestPrime n) ∧
        log (largestPrime n) < log n-SquarefreeVaughanLogSource.length u N := by
  filter_upwards [eventually_logarithmic_block_short B,eventually_ge_atTop 2]
    with N hwidth hN
  intro K n hn hs hP hB hnot
  have hL : SquarefreeVaughanLogSource.length u N ≤ (3899/2000 : ℝ)*N := by
    have hl := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have ht : 2*log 2 ≤ (3899/2000 : ℝ) := by linarith [log_two_lt_d9]
    exact hl.trans (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N))
  have hgeom := uncancelled_unsigned_unit_geometry hn hs hP hL hnot
  have hcore := (Finset.mem_filter.mp hn).2.1
  rcases hgeom with hgeom | hgeom
  · exfalso
    linarith
  · exact ⟨by linarith [hgeom.1],hgeom.2⟩

/-- The exact current whole-floor ledger can drop these zero blocks
without adding an error, supply assumption or duplicate row payment. -/
theorem ownerGapRemaining_eq_sum_sdiff (u y : ℝ) (j : ℕ) :
    ownerGapRemaining u y j =
      (∑ n ∈ (coreBand u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).filter Squarefree,
        ∑ db ∈ (n/largestPrime n).divisorsAntidiagonal \ cancelledDivisors u
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) n,
          phaseWeight (ZetaRieszAnnulusJoint.intermediatePrimes u
              (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) ∩ {largestPrime n})
            (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) y (n/largestPrime n) (largestPrime n)*
            (μ db.2 : ℂ)*(pairHinge
              (SquarefreeVaughanLogSource.length u (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))
              (largestPrime n) db.2 : ℂ)).re-
        (ZetaRieszUnifiedSignedRows.largeOwnerIncidences u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)
          (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)).re-
        (ownerGapLiteralRows u y j+ownerGapEndpointRows u y j) := by
  rw [ownerGapRemaining,coreConvolution_eq_sum_sdiff]

end RiemannGaussian.ZetaRieszShortDivisorCancellation
