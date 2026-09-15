/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCrossCompletion

/-!
# All inherited support cuts for cross-cutoff semiprimes

Two distinct primes above the quadratic head survive every earlier
adaptive arithmetic deletion. A cross-cutoff product has exactly one
extreme prime. On 1/2<=u<exp(-2/3), the entire physical annulus eventually
fits the original and narrowed logarithmic bands, so no unproved extra
mask remains on its completed upper-prime sum.
-/

namespace RiemannGaussian.ZetaRieszCrossSupport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSemiprimeSupport

/-- Both prime factors above the quadratic head exclude every smaller
prime divisor, with the actual product label retained. -/
theorem no_small_prime_divisor {a p r N : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hNa : N ^ 2 < a) (hNp : N ^ 2 < p) (hr : r.Prime) (hrN : r ≤ N ^ 2) :
    ¬ r ∣ p * a := by
  intro hd
  rcases hr.dvd_mul.mp hd with h | h
  · have he := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq hr ha).mp h
    omega

/-- A squarefree smooth divisor of a two-rough-prime product is exactly
one. Its size is not estimated by destroying its prime support. -/
theorem smooth_divisor_eq_one {a p b N : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hNa : N ^ 2 < a) (hNp : N ^ 2 < p) (hb : Squarefree b)
    (hsmall : ∀ r ∈ b.primeFactors, r ≤ N ^ 2) (hbd : b ∣ p * a) : b = 1 := by
  by_contra hb1
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hb1
  exact no_small_prime_divisor ha hp hNa hNp hr
    (hsmall r (Nat.mem_primeFactors.mpr ⟨hr, hrd, hb.ne_zero⟩)) (hrd.trans hbd)

/-- Two distinct rough primes survive all the earlier adaptive smooth
and composite deletions. This discharges the complete inherited mask. -/
theorem rough_semiprime_mem_adaptive {a p N : ℕ} {u : ℝ}
    (ha : a.Prime) (hp : p.Prime) (hNa : N ^ 2 < a) (hNp : N ^ 2 < p)
    (hpa : ¬ p ∣ a) (hb : p * a ∈ zetaPrimeLogBand N) :
    p * a ∈ adaptiveBand u N := by
  have hsf : Squarefree (p * a) := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, ha.squarefree⟩
  have hrough : p * a ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N := by
    exact Finset.mem_filter.mpr ⟨semiprime_mem_optimizedReducedBand ha hp hb u, hsf, p,
      Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p a, hsf.ne_zero⟩, hNp⟩
  have hprefix : p * a ∈ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hrough, ?_⟩
    intro hm
    obtain ⟨_, b, r, hbs, hsmall, hr, _, _, he⟩ :=
      (ZetaRieszSmoothPrimePrefix.mem_actualProductBand_iff _ u N (p * a)).mp hm
    have hbd : b ∣ p * a := by rw [he]; exact dvd_mul_left b r
    have hb1 := smooth_divisor_eq_one ha hp hNa hNp hbs hsmall hbd
    rw [hb1, mul_one] at he
    exact (Nat.not_prime_mul hp.ne_one ha.ne_one) (he ▸ hr)
  have hcomposite : p * a ∈ ZetaRieszCompositeDeletion.compositeResidualBand u N := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hprefix, ?_⟩
    intro hm
    obtain ⟨_, b, r, _, _, hnp, _, hr, _, he⟩ :=
      (ZetaRieszCompositeSmooth.mem_compositeSmoothBand_iff _ N (p * a)).mp hm
    exact hnp (prime_cofactor_of_semiprime ha hp hr he)
  have hprevious : p * a ∈ ZetaRieszLargeSmoothDeletion.previousBand u N := by
    unfold ZetaRieszLargeSmoothDeletion.previousBand
    split_ifs
    · exact hcomposite
    · exact hrough
  unfold adaptiveBand
  split_ifs
  · apply Finset.mem_sdiff.mpr
    refine ⟨hprevious, ?_⟩
    intro hm
    obtain ⟨_, b, c, hbs, hsmall, hXb, _, _, he⟩ :=
      (ZetaRieszLargeSmoothClass.mem_largeSmoothFactorBand_iff _ u N (p * a)).mp hm
    have hbd : b ∣ p * a := by rw [he]; exact dvd_mul_left b c
    have hb1 := smooth_divisor_eq_one ha hp hNa hNp hbs hsmall hbd
    rw [hb1] at hXb
    have : 2 ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 := by omega
    nlinarith
  · exact hprevious

/-- No small-prime semiprime deletion removes a product whose two prime
factors both exceed the quadratic head. -/
theorem rough_semiprime_mem_residual {a p N : ℕ} {u : ℝ}
    (ha : a.Prime) (hp : p.Prime) (hNa : N ^ 2 < a) (hNp : N ^ 2 < p)
    (hpa : ¬ p ∣ a) (hb : p * a ∈ zetaPrimeLogBand N) :
    p * a ∈ ZetaRieszSemiprimeDeletion.residualBand u N := by
  apply Finset.mem_sdiff.mpr
  refine ⟨rough_semiprime_mem_adaptive ha hp hNa hNp hpa hb, ?_⟩
  intro hm
  change p * a ∈ ZetaRieszSmoothPrimePrefix.productBand (fun _ => True)
    (Nat.primesLE (N ^ 2))
    ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) N at hm
  simp only [ZetaRieszSmoothPrimePrefix.productBand, Finset.mem_filter,
    Finset.mem_image, Finset.mem_product] at hm
  obtain ⟨⟨⟨b, r⟩, ⟨hb, _⟩, he⟩, _⟩ := hm
  have hb' := Nat.mem_primesLE.mp hb
  apply no_small_prime_divisor ha hp hNa hNp hb'.2 hb'.1
  rw [← he]
  exact dvd_mul_left b r

/-- For the separated prime ranges the extreme-prime set is the literal
singleton containing the upper prime, so every later degree cut survives. -/
theorem cross_extremePrimes_eq_singleton {a p N : ℕ} {u : ℝ}
    (ha : a.Prime) (hp : p.Prime)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hXp : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p) :
    ZetaRieszExtremePrimeCount.extremePrimes u N (p * a) = {p} := by
  ext r
  simp only [ZetaRieszExtremePrimeCount.extremePrimes, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hXr⟩
    have hrp := Nat.prime_of_mem_primeFactors hr
    rcases hrp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hr) with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp h
    · have he := (Nat.prime_dvd_prime_iff_eq hrp ha).mp h
      omega
  · intro he
    subst r
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p a, mul_ne_zero hp.ne_zero ha.ne_zero⟩, hXp⟩

/-- Cross-cutoff semiprimes in the physical annulus and logarithmic
window survive EVERY inherited support cut. No arbitrary mask remains on
this class when the window conditions are discharged. -/
theorem cross_semiprime_mem_annulus {a p N : ℕ} {u : ℝ}
    (hu : u < Real.exp (-(2 / 3 : ℝ)))
    (ha : a.Prime) (hp : p.Prime) (hNa : N ^ 2 < a)
    (haX : a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hXp : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p)
    (hb : p * a ∈ zetaPrimeLogBand N)
    (hlo : (2 / 5 : ℝ) * N < Real.log (p * a : ℕ))
    (hhi : Real.log (p * a : ℕ) ≤ 8 * (N : ℝ) * Real.log 2)
    (hproduct : p * a < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) :
    p * a ∈ ZetaRieszPhysicalAnnulus.annulusBand u N := by
  have hNp : N ^ 2 < p := by omega
  have hpa : ¬ p ∣ a := by
    intro hd
    have hh := Nat.le_of_dvd ha.pos hd
    omega
  have hres := rough_semiprime_mem_residual (u := u) ha hp hNa hNp hpa hb
  have hnarrow : p * a ∈ ZetaRieszNarrowCarrier.residualBand u N :=
    ZetaRieszNarrowCarrier.mem_residualBand.mpr ⟨hres, hlo, hhi⟩
  have hext := cross_extremePrimes_eq_singleton ha hp haX hXp
  have hfour : p * a ∈ ZetaRieszFourExtremeDeletion.fourResidualBand u N := by
    unfold ZetaRieszFourExtremeDeletion.fourResidualBand
    split_ifs
    · exact Finset.mem_filter.mpr ⟨hnarrow, by simp [hext]⟩
    · exact hnarrow
  apply (ZetaRieszPhysicalAnnulus.mem_annulusBand hu).mpr
  refine ⟨?_, ?_, hproduct⟩
  · rw [ZetaRieszLowerDegreeDeletion.degreeResidualBand, if_pos hu]
    exact Finset.mem_filter.mpr ⟨hfour, by simp [hext]⟩
  · exact hXp.trans_lt (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left ha.one_lt hp.pos)

/-- The physical upper square fits inside the narrowed logarithmic
ceiling at every order at least two when u>=1/2. The integer floor remains
part of the bound. -/
theorem physical_square_le_narrow_ceiling {u : ℝ} (hu : 1 / 2 ≤ u) {N : ℕ}
    (hN : 2 ≤ N) :
    ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ 2 ^ (8 * N) := by
  have hu0 : 0 < u := by linarith
  have hinv : u⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hu0).mpr (by linarith)
  have hfloor : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤
      u⁻¹ ^ N / (N + 1) := Nat.floor_le (by positivity)
  have hreal : (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) ≤ (2 : ℝ) ^ N := by
    calc
      _ ≤ u⁻¹ ^ N / (N + 1) := hfloor
      _ ≤ u⁻¹ ^ N := div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N])
      _ ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) hinv N
  have hnat : ZetaVaughanCutoffBudget.linearDampedCutoff u N ≤ 2 ^ N := by exact_mod_cast hreal
  have hbase : ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 ≤ 2 ^ (N + 2) := by
    rw [pow_add]
    have hpow : 1 ≤ (2 : ℕ) ^ N := one_le_pow₀ (by norm_num)
    norm_num only [Nat.reducePow]
    omega
  calc
    _ = (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 4 := by ring
    _ ≤ (2 ^ (N + 2)) ^ 4 := Nat.pow_le_pow_left hbase 4
    _ = 2 ^ (4 * N + 8) := by rw [← pow_mul]; congr 1; omega
    _ ≤ 2 ^ (8 * N) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- On the exposed-zero source range of the physical annulus, its whole
interval eventually satisfies both the original and narrowed bands. These
conditions impose no hidden extra mask on the semiprime completion. -/
theorem eventually_physical_window {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n →
      n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 →
      n ∈ zetaPrimeLogBand N ∧ (2 / 5 : ℝ) * N < Real.log n ∧
        Real.log n ≤ 8 * (N : ℝ) * Real.log 2 := by
  have hu0 : 0 < u := by linarith
  have hc : u < Real.exp (-(1 / 2 : ℝ)) :=
    huh.trans (Real.exp_lt_exp.mpr (by norm_num))
  filter_upwards [ZetaRieszExtremePrimeCount.eventually_length_ge_order hu0 hc,
    eventually_ge_atTop 2] with N hL hN
  intro n hnX hnXX
  have hlog : SquarefreeVaughanLogSource.length u N < Real.log n := by
    apply Real.log_lt_log (by positivity)
    exact_mod_cast hnX
  have hnup : n ≤ 2 ^ (8 * N) := hnXX.le.trans (physical_square_le_narrow_ceiling hu hN)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNc : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogup := Real.log_le_log hn0
    (show (n : ℝ) ≤ ((2 ^ (8 * N) : ℕ) : ℝ) by exact_mod_cast hnup)
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul] at hlogup
  refine ⟨?_, by linarith,
    by simpa only [Nat.cast_ofNat] using hlogup⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, hnup.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩, ?_⟩
  have hlog2 := Real.log_two_lt_d9
  nlinarith

/-- Eventually every actual cross-range semiprime below the physical
square belongs to the live annular carrier, with every earlier cutoff
proved rather than imposed on its completed prime sum. -/
theorem eventually_cross_semiprime_mem_annulus {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ a p : ℕ, a.Prime → p.Prime → N ^ 2 < a →
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 →
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p →
      p * a < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 →
      p * a ∈ ZetaRieszPhysicalAnnulus.annulusBand u N := by
  filter_upwards [eventually_physical_window hu huh] with N hN
  intro a p ha hp hNa haX hXp hprod
  have hXn := hXp.trans_lt (by simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left ha.one_lt hp.pos)
  obtain ⟨hb, hlo, hhi⟩ := hN (p * a) hXn hprod
  exact cross_semiprime_mem_annulus huh ha hp hNa haX hXp hb hlo hhi hprod

end
end RiemannGaussian.ZetaRieszCrossSupport
