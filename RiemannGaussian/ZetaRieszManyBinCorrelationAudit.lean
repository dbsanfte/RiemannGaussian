/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCutoffPeriodFloor
import RiemannGaussian.ZetaRieszPrefixCoherenceAudit
import RiemannGaussian.ZetaRieszQuadraticPrimeEnergy

/-!
# Actual common-cofactor correlations after the Riesz hinge

Occupied cofactor bins are preserved along a canonical owner fibre. The
actual sharp Möbius columns can agree on that fibre even at post-hinge
cutoffs, where the unit logarithmic correction is active. These are exact
statements about the existing prefix energy, with arbitrary original
phase/allocation/funding weights retained inside their signed sum.

No diagonalization, arithmetic cancellation or whole-floor bound is
deduced. The explicit small-integer regression is not the unpaid count-56
population or a native physical-prime example.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Real
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszManyBinCorrelationAudit
open ZetaRieszCofactorPhaseEnergy ZetaRieszCutoffPeriodFloor
open ZetaRieszQuadraticPrimeEnergy ZetaRieszJointPrimeEnergy

private theorem sharp_divisors (k : ℕ) {n : ℕ} (hn : 0 < n) :
    sharp k n = ∑ d ∈ n.divisors, if d ≤ k then (μ d : ℝ) else 0 := by
  have he : (Finset.Icc 1 k).filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ k) := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,hk⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hk⟩
    · rintro ⟨⟨hd,_⟩,hk⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hk⟩,hd⟩
  rw [sharp,← Finset.sum_filter,he,Finset.sum_filter]

private theorem sharp_response (k : ℕ) {n : ℕ} (hn : 0 < n) :
    sharp k n = divisorResponse (fun d => if d ≤ k then 1 else 0) n := by
  rw [sharp_divisors k hn,divisorResponse]
  exact Finset.sum_congr rfl (fun d _ => by split_ifs <;> simp)

/-- Inserting an actual coprime owner prime translates the sharp prefix
by its exact integer quotient. No divisor or partial interval is lost. -/
theorem sharp_prime_mul (k : ℕ) {p a : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) :
    sharp k (p*a) = sharp k a-sharp (k/p) a := by
  have ha : 0 < a := Nat.pos_of_ne_zero (by intro h; exact hpa (by simp [h]))
  rw [sharp_response k (Nat.mul_pos hp.pos ha),divisor_prime_mul hp hpa,
    sharp_response k ha,sharp_response (k/p) ha,divisorResponse,divisorResponse,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have he : d ≤ k/p ↔ p*d ≤ k := by
    rw [Nat.le_div_iff_mul_le hp.pos,Nat.mul_comm d p]
  simp only [he]
  ring

/-- Owner primes inside the same quotient cell have identical ACTUAL
Möbius columns, regardless of the cofactor's occupied bins or count. -/
theorem sharp_owner_cell {k Q a p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpa : ¬p ∣ a) (hqa : ¬q ∣ a) (hpQ : k/p=Q) (hqQ : k/q=Q) :
    sharp k (p*a)=sharp k (q*a) := by
  rw [sharp_prime_mul k hp hpa,sharp_prime_mul k hq hqa,hpQ,hqQ]

/-- Canonical ownership preserves the literal cofactor and hence every
occupied-bin restriction, including a many-bin hypothesis. -/
theorem owner_bins_eq (N : ℕ) {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    (ho : ∀ q ∈ a.primeFactors, q < p) :
    ZetaRieszFewBinCoverFloor.cofactorBins N
      ((p*a)/ZetaRieszPrimeEndpoint.largestPrime (p*a)) =
        ZetaRieszFewBinCoverFloor.cofactorBins N a := by
  rw [ZetaRieszPrimeIntervals.largestPrime_mul p a hp ha ho,
    Nat.mul_div_cancel_left a hp.pos]

/-- The entire signed original fibre moment survives inside one common
prefix. This includes phase, factorial, allocation and funding weights. -/
theorem correlation_owner_cell (P : Finset ℕ) {a k Q : ℕ} (ha : 0 < a)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ a ∧ k/p=Q) (w : ℕ → ℝ) :
    correlation (P.image (fun p => p*a)) w k =
      (sharp k a-sharp Q a)*(∑ p ∈ P,w (p*a)) := by
  rw [correlation,Finset.sum_image (by
    intro p _ q _ he
    exact Nat.eq_of_mul_eq_mul_right ha he),Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p hp => by
    rw [sharp_prime_mul k (hP p hp).1 (hP p hp).2.1,(hP p hp).2.2,mul_comm])

/-- Post-hinge common-cofactor correlations enter the EXISTING energy.
They are not automatically diminished by increasing bin occupancy. -/
theorem phaseEnergy_owner_cell_lower (R : ℕ) (P : Finset ℕ) {a k Q : ℕ}
    (ha : 0 < a) (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ a ∧ k/p=Q)
    (w f : ℕ → ℝ) (hk : k ∈ activeCutoffs R f) :
    ((sharp k a-sharp Q a)*(∑ p ∈ P,w (p*a)))^2/(k : ℝ) ≤
      phaseEnergy R (P.image (fun p => p*a)) w f := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ activeCutoffs R f) =>
      div_nonneg (sq_nonneg (correlation (P.image (fun p => p*a)) w i))
        (Nat.cast_nonneg i)) hk
  simpa only [phaseEnergy,correlation_owner_cell P ha hP w] using h

/-- Unit logarithmic correction does not remove a genuine post-hinge
cutoff. The endpoint X itself is deliberately excluded. -/
theorem post_hinge_active {X k : ℕ} (hk : 0 < k) (hkX : k < X)
    {L : ℝ} (hL : L ≤ log k) :
    k ∈ activeCutoffs X (correctedProfile X L 1 0) := by
  have hnext : k+1 ≤ X := by omega
  have hlog : log k < log (k+1 : ℕ) := log_lt_log
    (by exact_mod_cast hk) (by exact_mod_cast Nat.lt_succ_self k)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨hk,le_of_lt hkX⟩,?_⟩
  simp only [correctedProfile,zero_mul,add_zero,
    ZetaRieszCenteredPrimeEnergy.centeredProfile,if_pos (le_of_lt hkX),
    if_pos hnext,one_mul,max_eq_left (sub_nonpos.mpr hL),
    max_eq_left (sub_nonpos.mpr (hL.trans hlog.le)),zero_add]
  linarith

/-- A diagonal bound valid for EVERY weight needs to pay the coherent
fibre size at this cutoff, even when the early prefix is inactive. This
does not assert that the specific whole-carrier weights attain it. -/
theorem diagonal_coefficient_owner_cell_lower (R : ℕ) (P : Finset ℕ)
    {a k Q : ℕ} (ha : 0 < a) (hPne : P.Nonempty)
    (hP : ∀ p ∈ P, p.Prime ∧ ¬p ∣ a ∧ k/p=Q)
    (f : ℕ → ℝ) (hk : k ∈ activeCutoffs R f) (C : ℝ)
    (hbound : ∀ w : ℕ → ℝ,
      phaseEnergy R (P.image (fun p => p*a)) w f ≤
        C*(∑ n ∈ P.image (fun p => p*a),w n^2)) :
    (P.card : ℝ)*(sharp k a-sharp Q a)^2/(k : ℝ) ≤ C := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hPne.card_pos
  have hkp : (0 : ℝ) < k := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hi : (P.image (fun p => p*a)).card=P.card :=
    Finset.card_image_of_injOn (by intro p _ q _ he; exact Nat.eq_of_mul_eq_mul_right ha he)
  have h := (phaseEnergy_owner_cell_lower R P ha hP (fun _ => 1) f hk).trans
    (hbound (fun _ => 1))
  simp only [Finset.sum_const,one_pow,nsmul_eq_mul,mul_one,hi] at h
  apply (mul_le_mul_iff_right₀ hc).mp
  convert h using 1 <;> field_simp

end RiemannGaussian.ZetaRieszManyBinCorrelationAudit
