/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCentralPrimeLayers
import RiemannGaussian.ZetaRieszEndpointTaper

/-!
# Prime endpoint cancellation in the complete three-prime coefficient

The third-prime insertion is a signed difference of two tents. On the
actual upper-reflection half, each prime supplies a vanishing endpoint
weight. The strongest such bound uses the actual largest prime. Its full
negative-phase cost remains open; no zero-free conclusion is claimed.
-/
namespace RiemannGaussian.ZetaRieszPrimeEndpoint
noncomputable section
open ZetaSquarefreeRieszWindows ZetaRieszTriplePrime

/-- The exact pair tent lies below its nonnegative physical cutoff. -/
theorem primePairTent_le_cutoff {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    primePairTent a b t ≤ t := by
  rw [primePairTent_eq_overlap ha hb]
  exact max_le ((sub_le_self _ (le_max_right _ _)).trans (min_le_left _ _)) ht

/-- The negative of the complete three-prime difference is bounded by
the inserted prime's cutoff gap. The upper-half sign theorem is needed
to turn this one-sided estimate into an amplitude bound. -/
theorem neg_tripleDifference_le_prime_gap {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hcL : c ≤ L) :
    -tripleDifference a b c L ≤ L - c := by
  have h0 := (primePairTent_bounds ha hb L).1
  have h1 := primePairTent_le_cutoff ha hb (sub_nonneg.mpr hcL)
  unfold tripleDifference
  linarith

/-- The new endpoint bound applies to an actual product of three distinct
primes, with the original signed divisor sum and physical length. -/
theorem neg_riesz_three_primes_le_prime_gap {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hrL : Real.log r ≤ L) :
    -VaughanLogAverage.riesz L (p * (q * r)) ≤ L - Real.log r := by
  rw [riesz_three_primes_eq_difference L hp hq hr hpq hpr hqr]
  exact neg_tripleDifference_le_prime_gap
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) hrL

/-- The endpoint estimate holds for every prime factor of an arbitrary
squarefree three-prime integer, without fixing an ordering of its primes. -/
theorem neg_riesz_three_le_prime_gap {n p : ℕ} (hn : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hp : p ∈ n.primeFactors)
    {L : ℝ} (hpL : Real.log p ≤ L) :
    -VaughanLogAverage.riesz L n ≤ L - Real.log p := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc, he⟩ := exists_three_primes hn hcard
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  rw [he] at hd
  rcases hprime.dvd_mul.mp hd with hpa | hpbc
  · have hpa := (Nat.dvd_prime_two_le ha hprime.two_le).mp hpa
    subst p
    have he' : n = b * (c * a) := by rw [he]; ring
    rw [he']
    exact neg_riesz_three_primes_le_prime_gap hb hc ha hbc hab.symm hac.symm hpL
  · rcases hprime.dvd_mul.mp hpbc with hpb | hpc
    · have hpb := (Nat.dvd_prime_two_le hb hprime.two_le).mp hpb
      subst p
      have he' : n = a * (c * b) := by rw [he]; ring
      rw [he']
      exact neg_riesz_three_primes_le_prime_gap ha hc hb hac hab hbc.symm hpL
    · have hpc := (Nat.dvd_prime_two_le hc hprime.two_le).mp hpc
      subst p
      rw [he]
      exact neg_riesz_three_primes_le_prime_gap ha hb hc hab hac hbc hpL

/-- On the actual upper-reflection half, the full three-prime coefficient
is bounded by the distance of any selected prime from its own endpoint.
The original physical-log prefactor is preserved. -/
theorem norm_three_coefficient_le_prime_gap {n p : ℕ}
    (hcard : n.primeFactors.card = 3) (hp : p ∈ n.primeFactors)
    {L : ℝ} (hL : 0 < L) (hmid : Real.log n ≤ 2 * L)
    (hpL : Real.log p ≤ L) :
    ‖SquarefreeVaughanLogSource.coefficient L n‖ ≤
      Real.log n / L * (L - Real.log p) := by
  unfold SquarefreeVaughanLogSource.coefficient
  split_ifs with hn
  · have hr := riesz_of_three_primeFactors_bounds hn.1 hcard hmid
    have hg := neg_riesz_three_le_prime_gap hn.1 hcard hp hpL
    have hlog := Real.log_natCast_nonneg n
    have hnonneg : 0 ≤ -Real.log n * VaughanLogAverage.riesz L n / L :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hr.2) hL.le
    rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    calc
      _ = Real.log n / L * (-VaughanLogAverage.riesz L n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (div_nonneg hlog hL.le)
  · simp only [norm_zero]
    exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (sub_nonneg.mpr hpL)

/-- Every prime of an ACTUAL retained three-prime integer provides its
own endpoint taper for the entire original coefficient. This is a
full-coefficient amplitude bound, without a frequency restriction. -/
theorem actual_three_coefficient_le_prime_taper {u : ℝ} {N n p : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N)
    (hcard : n.primeFactors.card = 3) (hp : p ∈ n.primeFactors) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      Real.log n * ZetaRieszEndpointTaper.endpointWeight
        (SquarefreeVaughanLogSource.length u N) (Real.log p) := by
  have hall : ∀ q ∈ n.primeFactors,
      q < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).1).1).2
  have hpL : Real.log p ≤ SquarefreeVaughanLogSource.length u N := by
    apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast (hall p hp).le
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hmid := (ZetaRieszCentralPrimeLayers.log_lt_twice_length_of_mem_annulus huh
    (ZetaRieszCentralPrimeLayers.centralUnpairedBand_subset_annulus u N hn)).le
  apply (norm_three_coefficient_le_prime_gap hcard hp hL hmid hpL).trans_eq
  unfold ZetaRieszEndpointTaper.endpointWeight
  field_simp

/-- The actual complete coefficient keeps whichever bound is smaller:
the old half-logarithm or the selected prime's vanishing endpoint taper. -/
theorem actual_three_coefficient_le_min_taper {u : ℝ} {N n p : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N)
    (hcard : n.primeFactors.card = 3) (hp : p ∈ n.primeFactors) :
    ‖SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n‖ ≤
      min (Real.log n / 2) (Real.log n * ZetaRieszEndpointTaper.endpointWeight
        (SquarefreeVaughanLogSource.length u N) (Real.log p)) :=
  le_min (ZetaRieszCentralPrimeLayers.central_three_coefficient_bounds huh hn hcard).2.1
    (actual_three_coefficient_le_prime_taper huh hn hcard hp)

/-- The sharpened full-coefficient amplitude bound pays only for negative
real observations. The sign of the arithmetic coefficient is used before
its product phase is bounded. -/
theorem re_actual_three_atom_ge_min_taper {u : ℝ} {N n p : ℕ}
    (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N)
    (hcard : n.primeFactors.card = 3) (hp : p ∈ n.primeFactors) (z : ℂ) :
    -(min (Real.log n / 2) (Real.log n * ZetaRieszEndpointTaper.endpointWeight
      (SquarefreeVaughanLogSource.length u N) (Real.log p))) * max 0 (-z.re) ≤
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n * z).re := by
  have h0 := (ZetaRieszCentralPrimeLayers.central_three_coefficient_bounds huh hn hcard).1
  have h1 := (Complex.re_le_norm _).trans (actual_three_coefficient_le_min_taper huh hn hcard hp)
  rw [Complex.mul_re, ZetaRieszCosineCarrier.coefficient_im_eq_zero, zero_mul, sub_zero]
  by_cases hz : 0 ≤ z.re
  · rw [max_eq_left (neg_nonpos.mpr hz), mul_zero]
    exact mul_nonneg h0 hz
  · rw [max_eq_right (by linarith : 0 ≤ -z.re)]
    nlinarith [mul_le_mul_of_nonpos_right h1 (le_of_not_ge hz)]

/-- Every choice of one prime per actual three-prime integer gives the
improved finite signed floor, with the original factorial filter and
source factor intact. Estimating this negative-phase cost remains open. -/
theorem re_normalized_three_ge_min_taper (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ)))
    (p : ℕ → ℕ) (hp : ∀ n ∈ (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
      (fun n => n.primeFactors.card = 3), p n ∈ n.primeFactors) :
    u ^ (N + 1) *
      (∑ n ∈ (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
        (fun n => n.primeFactors.card = 3),
        -(min (Real.log n / 2) (Real.log n * ZetaRieszEndpointTaper.endpointWeight
          (SquarefreeVaughanLogSource.length u N) (Real.log (p n)))) *
            max 0 (-(zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n).re)) ≤
      ((u : ℂ) ^ (N + 1) *
        ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N).re := by
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
  rw [ZetaRieszCentralPrimeLayers.centralThreePrimeResponse, Complex.re_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact re_actual_three_atom_ge_min_taper huh (Finset.mem_filter.mp hn).1
    (Finset.mem_filter.mp hn).2 (hp n hn) _

/-- The largest prime is a canonical arithmetic choice, with a harmless
zero value at integers with no prime factors. -/
def largestPrime (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

/-- Every actual three-prime label has its canonical largest prime in
its genuine prime support, discharging the choice premise of the floor. -/
theorem largestPrime_mem_of_three {n : ℕ} (hcard : n.primeFactors.card = 3) :
    largestPrime n ∈ n.primeFactors := by
  have h : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  rw [largestPrime, dif_pos h]
  exact Finset.max'_mem _ _

/-- The canonical largest-prime floor bounds the complete actual signed
three-prime response with no auxiliary prime-selection premise. The
negative-phase sum on the left remains an explicit arithmetic cost. -/
theorem re_normalized_three_ge_largest_prime_taper (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u : ℝ} (hu : 0 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    u ^ (N + 1) *
      (∑ n ∈ (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
        (fun n => n.primeFactors.card = 3),
        -(min (Real.log n / 2) (Real.log n * ZetaRieszEndpointTaper.endpointWeight
          (SquarefreeVaughanLogSource.length u N) (Real.log (largestPrime n)))) *
            max 0 (-(zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n).re)) ≤
      ((u : ℂ) ^ (N + 1) *
        ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N).re :=
  re_normalized_three_ge_min_taper P y N hu huh largestPrime
    (fun _ hn => largestPrime_mem_of_three (Finset.mem_filter.mp hn).2)

/-- The largest actual prime minimizes the entire family of one-prime
endpoint allowances. The comparison uses its arithmetic ordering, not
numerical coefficient search. -/
theorem largest_prime_taper_le {n p : ℕ} (hp : p ∈ n.primeFactors)
    {L : ℝ} (hL : 0 < L) :
    Real.log n * ZetaRieszEndpointTaper.endpointWeight L (Real.log (largestPrime n)) ≤
      Real.log n * ZetaRieszEndpointTaper.endpointWeight L (Real.log p) := by
  have hne : n.primeFactors.Nonempty := ⟨p, hp⟩
  have hpn : p ≤ largestPrime n := by
    rw [largestPrime, dif_pos hne]
    exact Finset.le_max' _ _ hp
  have hlog : Real.log p ≤ Real.log (largestPrime n) := by
    apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast hpn
  unfold ZetaRieszEndpointTaper.endpointWeight
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg n)
  exact sub_le_sub_left (div_le_div_of_nonneg_right hlog hL.le) _

/-- Replacing the actual largest-prime coordinate by only the average
prime logarithm loses the new saving: the older half-logarithm and
midpoint-gap envelope is already at least as strong at that averaged
coordinate. Actual prime imbalance must remain available. -/
theorem average_prime_taper_no_improvement (x : ℝ) :
    min (1 / 2 : ℝ) (2 - x) ≤ 1 - x / 3 := by
  by_cases hx : x ≤ 3 / 2
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- When both pairs involving the last prime reach the cutoff and the
remaining pair does not exceed it, the complete signed difference is
exactly that prime's endpoint gap. No frequency integration or norm estimate is used. -/
theorem tripleDifference_eq_neg_prime_gap {a b c L : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (habL : a + b ≤ L)
    (hcL : c ≤ L) (hLa : L - c ≤ a) (hLb : L - c ≤ b) :
    tripleDifference a b c L = -(L - c) := by
  rw [tripleDifference, primePairTent_eq_zero_of_outside ha hb (Or.inr habL)]
  unfold primePairTent
  rw [max_eq_right (sub_nonneg.mpr hcL), max_eq_left (by linarith : L - c - a ≤ 0),
    max_eq_left (by linarith : L - c - b ≤ 0),
    max_eq_left (by linarith : L - c - a - b ≤ 0)]
  ring

/-- The one-small-pair chamber of three actual distinct primes has an
exact signed Riesz coefficient. Its endpoint weight is the same physical
taper appearing in the retained wing, with the prime coordinate kept. -/
theorem riesz_three_primes_eq_neg_prime_gap {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {L : ℝ} (hpqL : Real.log p + Real.log q ≤ L) (hrL : Real.log r ≤ L)
    (hprL : L ≤ Real.log p + Real.log r) (hqrL : L ≤ Real.log q + Real.log r) :
    VaughanLogAverage.riesz L (p * (q * r)) = -(L - Real.log r) := by
  rw [riesz_three_primes_eq_difference L hp hq hr hpq hpr hqr]
  exact tripleDifference_eq_neg_prime_gap
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q) hpqL hrL
    (by linarith) (by linarith)

end
end RiemannGaussian.ZetaRieszPrimeEndpoint
