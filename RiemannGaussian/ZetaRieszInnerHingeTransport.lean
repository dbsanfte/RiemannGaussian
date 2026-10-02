/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedConvolution
import RiemannGaussian.ZetaRieszPairBoundary
import RiemannGaussian.ZetaRieszReplacementPhase
import RiemannGaussian.ZetaRieszPairMatching

/-!
# Opposite-count transport on the literal inner hinge

On the innermost reflected crossing the complete coefficient, at EVERY
composite cofactor count, is one linear cutoff times Mobius parity.
Replacing an owner prime by two actual primes therefore pays a difference
of the two ORIGINAL weighted atoms, rather than a divisor-count allowance.
The allocation, full phase and arbitrary signed funding multipliers stay
inside this difference. No prime partner, matching coverage, physical-mask
completion or source-scale bound on the unmatched population is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszInnerHingeTransport
open ZetaRieszSignedConvolution ZetaRieszParityPacket ZetaRieszJointAllocation
open ZetaRieszFixedCountPeriod

/-- Literal cutoff conditions only: the second prime is at the reflected
hinge, and no nonunit divisor of the remaining composite enters it. -/
def InnerHinge (L : ℝ) (p q b : ℕ) : Prop :=
  log (q*b : ℕ) ≤ L ∧
    log b ≤ log (p*(q*b) : ℕ)-L ∧
    0 ≤ log (p*b : ℕ)-L ∧
    log (p*b : ℕ)-L ≤ log b.minFac

private theorem composite_of_count {b : ℕ} (hc : 2 ≤ b.primeFactors.card) :
    b ≠ 1 ∧ ¬b.Prime := by
  constructor
  · intro h
    simp [h] at hc
  · intro h
    simp [h.primeFactors] at hc

/-- The joined response is EXACTLY its signed unit hinge. There is no
factor exponential in the number of cofactor divisors. -/
theorem response_inner {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : Squarefree b) (hc : 2 ≤ b.primeFactors.card) (hqb : ¬q ∣ b)
    {L : ℝ} (hi : InnerHinge L p q b) :
    response L (log p+log (q*b : ℕ)) (q*b) = -(log (p*b : ℕ)-L) := by
  have hqb0 : (q*b : ℕ) ≠ 0 := mul_ne_zero hq.ne_zero hb.ne_zero
  have hlogq : log (q*b : ℕ)=log q+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hq.ne_zero)
      (by exact_mod_cast hb.ne_zero)]
  have hlogp : log (p*b : ℕ)=log p+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hb.ne_zero)]
  have hlogn : log (p*(q*b) : ℕ)=log p+log (q*b : ℕ) := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hqb0)]
  have hzero := ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hb
    (composite_of_count hc).1 (composite_of_count hc).2 hi.2.1
  have hunit := ZetaRieszTypeII.riesz_eq_cutoff_below_minFac hb.ne_zero
    hi.2.2.1 hi.2.2.2
  rw [response,ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
    (sub_nonpos.mpr hi.1),sub_zero,← hlogn,
    ZetaSquarefreeRieszWindows.riesz_prime_mul _ hq hqb,hzero,
    show log (p*(q*b) : ℕ)-L-log q=log (p*b : ℕ)-L by
      rw [hlogn,hlogq,hlogp]; ring,hunit,zero_sub]

/-- Exact reduction of the ORIGINAL residual atom, with its own allocation
and complex product phase. This covers arbitrary counts, including56+. -/
theorem literal_inner_atom {p q b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hb : Squarefree b) (hc : 2 ≤ b.primeFactors.card)
    (hqb : ¬q ∣ b) (hpqb : ¬p ∣ q*b) {L : ℝ}
    (hi : InnerHinge L p q b) (A : Finset ℕ) (N : ℕ) (y : ℝ) :
    residualCoefficient A L N (p*(q*b))*zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b)) =
      (μ b : ℂ)*((log (p*b : ℕ)-L : ℝ) : ℂ)*phaseWeight A L N y (q*b) p := by
  have hsf : Squarefree (q*b) := Nat.squarefree_mul_iff.mpr
    ⟨hq.coprime_iff_not_dvd.mpr hqb,hq.squarefree,hb⟩
  have hcount : 2 ≤ (q*b).primeFactors.card := hc.trans
    (Finset.card_le_card (Nat.primeFactors_mono (dvd_mul_left b q) (mul_ne_zero hq.ne_zero hb.ne_zero)))
  rw [residual_atom_eq_parity_response hsf hcount hp hpqb,
    response_inner hp hq hb hc hqb hi,moebius_prime_mul_eq_not_dvd hq,if_neg hqb]
  push_cast
  ring

/-- Opposite prime-count classes combine at the level of their literal
atoms. Funding and allocation may differ: both ORIGINAL values remain.
No equality of phases or unproved prime transport is inserted. -/
theorem inserted_pair_eq {p p' q r b : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hq : q.Prime) (hr : r.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hrb : ¬r ∣ b)
    (hqb : ¬q ∣ b) (hqr : ¬q ∣ r*b)
    (hpqb : ¬p ∣ q*b) (hp'qr : ¬p' ∣ q*(r*b))
    {L : ℝ} (hi : InnerHinge L p q b) (hi' : InnerHinge L p' q (r*b))
    (A A' : Finset ℕ) (N : ℕ) (y v v' : ℝ) :
    (v : ℂ)*(residualCoefficient A L N (p*(q*b))*
      zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b)))+
      (v' : ℂ)*(residualCoefficient A' L N (p'*(q*(r*b)))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*(q*(r*b)))) =
      (μ b : ℂ)*(
        ((log (p*b : ℕ)-L : ℝ) : ℂ)*((v : ℂ)*phaseWeight A L N y (q*b) p)-
        ((log (p'*(r*b) : ℕ)-L : ℝ) : ℂ)*((v' : ℂ)*phaseWeight A' L N y (q*(r*b)) p')) := by
  have hsf : Squarefree (r*b) := Nat.squarefree_mul_iff.mpr
    ⟨hr.coprime_iff_not_dvd.mpr hrb,hr.squarefree,hb⟩
  have hcount : 2 ≤ (r*b).primeFactors.card := hc.trans
    (Finset.card_le_card (Nat.primeFactors_mono (dvd_mul_left b r) (mul_ne_zero hr.ne_zero hb.ne_zero)))
  rw [literal_inner_atom hp hq hb hc hqb hpqb hi,
    literal_inner_atom hp' hq hsf hcount hqr hp'qr hi',
    moebius_prime_mul_eq_not_dvd hr,if_neg hrb]
  push_cast
  ring

private theorem norm_moebius_le (b : ℕ) : ‖(μ b : ℂ)‖ ≤ 1 := by
  have h : |(μ b : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using h

/-- A sharp coupled floor: the ORIGINAL amplitudes are subtracted before
their real part is priced. No2^count, countwise cost or absolute phase sum
appears. Actual matching coverage and the source cost are still open. -/
theorem inserted_pair_floor {p p' q r b : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hq : q.Prime) (hr : r.Prime) (hb : Squarefree b)
    (hc : 2 ≤ b.primeFactors.card) (hrb : ¬r ∣ b)
    (hqb : ¬q ∣ b) (hqr : ¬q ∣ r*b)
    (hpqb : ¬p ∣ q*b) (hp'qr : ¬p' ∣ q*(r*b))
    {L : ℝ} (hi : InnerHinge L p q b) (hi' : InnerHinge L p' q (r*b))
    (A A' : Finset ℕ) (N : ℕ) (y v v' : ℝ) :
    -|(
        ((log (p*b : ℕ)-L : ℝ) : ℂ)*((v : ℂ)*phaseWeight A L N y (q*b) p)-
        ((log (p'*(r*b) : ℕ)-L : ℝ) : ℂ)*((v' : ℂ)*phaseWeight A' L N y (q*(r*b)) p')).re| ≤
      ((v : ℂ)*(residualCoefficient A L N (p*(q*b))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*(q*b)))+
        (v' : ℂ)*(residualCoefficient A' L N (p'*(q*(r*b)))*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p'*(q*(r*b))))).re := by
  rw [inserted_pair_eq hp hp' hq hr hb hc hrb hqb hqr hpqb hp'qr hi hi']
  simp only [Complex.mul_re,Complex.intCast_re,Complex.intCast_im,zero_mul,sub_zero]
  have hm : |(μ b : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
  have h := mul_le_mul_of_nonneg_right hm (abs_nonneg
    (((log (p*b : ℕ)-L : ℝ) : ℂ)*((v : ℂ)*phaseWeight A L N y (q*b) p)-
      ((log (p'*(r*b) : ℕ)-L : ℝ) : ℂ)*((v' : ℂ)*phaseWeight A' L N y (q*(r*b)) p')).re)
  have hneg := neg_abs_le ((μ b : ℝ)*(
    ((log (p*b : ℕ)-L : ℝ) : ℂ)*((v : ℂ)*phaseWeight A L N y (q*b) p)-
      ((log (p'*(r*b) : ℕ)-L : ℝ) : ℂ)*((v' : ℂ)*phaseWeight A' L N y (q*(r*b)) p')).re)
  rw [abs_mul] at hneg
  nlinarith only [h,hneg]

/-- Count-free quantitative mismatch AFTER parity pairing. Allocation and
signed funding errors remain inside the complex amplitude difference. -/
theorem norm_linear_pair_le (b : ℕ) (x x' : ℝ) (W W' : ℂ) :
    ‖(μ b : ℂ)*((x : ℂ)*W-(x' : ℂ)*W')‖ ≤
      |x-x'| * ‖W‖+|x'| * ‖W-W'‖ := by
  calc
    _ = ‖(μ b : ℂ)‖*‖(x : ℂ)*W-(x' : ℂ)*W'‖ := norm_mul _ _
    _ ≤ ‖(x : ℂ)*W-(x' : ℂ)*W'‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_le b)
    _ = ‖((x-x' : ℝ) : ℂ)*W+(x' : ℂ)*(W-W')‖ := by congr 1; push_cast; ring
    _ ≤ _ := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
        norm_add_le (((x-x' : ℝ) : ℂ)*W) ((x' : ℂ)*(W-W'))

/-- The cutoff and total-log mismatch is EXACTLY the owner-to-product
log gap; the common cofactor does not contribute to phase transport. -/
theorem cutoff_gap_eq {p p' r b : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (hr : 0 < r) (hb : 0 < b) (L : ℝ) :
    (log (p'*(r*b) : ℕ)-L)-(log (p*b : ℕ)-L) = log (p'*r : ℕ)-log p := by
  simpa only [sub_sub_sub_cancel_right] using
    ZetaRieszReplacementPhase.replacement_log_difference hp' hr hp hb

/-- Spend disjoint ORIGINAL cross-count pairs once, retaining every
unmatched label and funding contribution SIGNED. This is a finite lower
inequality; neither pair coverage nor its total numerical price is assumed. -/
theorem matching_floor_with_signed_rest (S : Finset ℕ) (E : Finset (ℕ×ℕ))
    (hE : ZetaRieszPairMatching.separatedPairs E) (hS : E ⊆ S ×ˢ S)
    (f : ℕ → ℂ) (cost : ℕ×ℕ → ℝ)
    (hcost : ∀ e ∈ E, -cost e ≤ (f e.1+f e.2).re) :
    -(∑ e ∈ E,cost e)+
      (∑ n ∈ S \ ZetaRieszPairMatching.matchedVertices E,f n).re ≤
        (∑ n ∈ S,f n).re := by
  rw [ZetaRieszPairMatching.sum_eq_pairs_add_remainder S E hE hS,
    Complex.add_re]
  simp only [Complex.re_sum]
  exact add_le_add (by
    simpa only [Finset.sum_neg_distrib] using Finset.sum_le_sum hcost) le_rfl

end RiemannGaussian.ZetaRieszInnerHingeTransport
