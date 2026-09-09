/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseArithmetic
import RiemannGaussian.Hybrid.EtaSupportGapPhaseGram

/-!
# Prime-power recurrence forces arithmetic work

The same exact cosine Gram identity used by the eta support/gap machinery
applies to any summable nonnegative real-frequency spectrum. Its zero
frequency forces a lower bound on the energy of a whole phase block.

Consequently the first `N` nonzero multiples of an angle cannot all have
small kernel values. At the arithmetic angle `y * log p`, this forces an
explicit positive contribution from powers of any chosen prime. The result
is uniform in `y` and applies to arbitrary finite or infinite spectra.

This supplies arithmetic information beyond nonnegativity in the coupled
zeta inequality. A fixed prime block gives a bounded floor, not the missing
height-dependent saving required for the RH frontier.
-/

open Complex
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

variable {a ω : ℕ → ℝ}

/-- At zero angle the kernel retains the whole coefficient mass. -/
theorem zetaPhaseKernel_zero (a ω : ℕ → ℝ) :
    zetaPhaseKernel a ω 0 = ∑' n : ℕ, a n := by
  simp [zetaPhaseKernel]

/-- Reversing an angle retains the real cosine kernel exactly. -/
theorem zetaPhaseKernel_neg (a ω : ℕ → ℝ) (t : ℝ) :
    zetaPhaseKernel a ω (-t) = zetaPhaseKernel a ω t := by
  simp [zetaPhaseKernel]

/-- Every finite mixed phase energy is the convergent sum of its exact
frequency energies. Both squares and all cross terms remain available. -/
theorem hasSum_zetaPhase_gramEnergy (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {ι : Type*} [Fintype ι] (u c : ι → ℝ) :
    HasSum (fun n : ℕ ↦ a n * finiteCosinePhaseEnergy (fun i ↦ ω n * u i) c)
      (∑ i, ∑ j, c i * c j * zetaPhaseKernel a ω (u j - u i)) := by
  have h (i j : ι) :=
    (summable_zetaPhaseKernel (ω := ω) ha hs (u j - u i)).hasSum.mul_left (c i * c j)
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ ↦
    hasSum_sum (s := Finset.univ) (fun j _ ↦ h i j))
  apply hsum.congr_fun
  intro n
  simp only [finiteCosinePhaseEnergy, Finset.mul_sum, mul_sub]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A zero-frequency coefficient forces a quantitative lower bound on
every finite mixed phase energy. Remaining frequencies contribute their
nonnegative cosine and sine squares. -/
theorem zetaPhase_gramEnergy_zeroFrequency_le (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (r : ℕ) (hr : ω r = 0)
    {ι : Type*} [Fintype ι] (u c : ι → ℝ) :
    a r * (∑ i, c i) ^ 2 ≤
      ∑ i, ∑ j, c i * c j * zetaPhaseKernel a ω (u j - u i) := by
  have hsum := hasSum_zetaPhase_gramEnergy (ω := ω) ha hs u c
  have h := hsum.summable.le_tsum r
    (fun n _ ↦ mul_nonneg (ha n) (finiteCosinePhaseEnergy_nonneg _ _))
  rw [hsum.tsum_eq] at h
  simpa [hr, finiteCosinePhaseEnergy_eq_squares] using h

/-- A uniform ceiling on the first `N` nonzero phase returns must pay
for the zero-frequency mass in an entire block of `N + 1` phases. This is
independent of the chosen real frequencies and does not assume kernel
nonnegativity. -/
theorem zetaPhase_return_ceiling_constraint (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) (N : ℕ) (θ B : ℝ)
    (hB : ∀ k : ℕ, 1 ≤ k → k ≤ N → zetaPhaseKernel a ω ((k : ℝ) * θ) ≤ B) :
    ((N : ℝ) + 1) * a r - (∑' n : ℕ, a n) ≤ (N : ℝ) * B := by
  let A := ∑' n : ℕ, a n
  let u (i : Fin (N + 1)) := (i.val : ℝ) * θ
  have hpair (i j : Fin (N + 1)) :
      zetaPhaseKernel a ω (u j - u i) ≤ if i = j then A else B := by
    by_cases hij : i = j
    · subst j
      simp [zetaPhaseKernel_zero, A]
    · rw [if_neg hij]
      have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
      by_cases hle : i.val ≤ j.val
      · have h := hB (j.val - i.val) (by omega) (by omega)
        have he : ((j.val - i.val : ℕ) : ℝ) * θ = u j - u i := by
          rw [Nat.cast_sub hle]
          dsimp [u]
          ring
        rwa [he] at h
      · have hji : j.val ≤ i.val := by omega
        have h := hB (i.val - j.val) (by omega) (by omega)
        have he : ((i.val - j.val : ℕ) : ℝ) * θ = -(u j - u i) := by
          rw [Nat.cast_sub hji]
          dsimp [u]
          ring
        rwa [he, zetaPhaseKernel_neg] at h
  have hrow (i : Fin (N + 1)) :
      (∑ j : Fin (N + 1), if i = j then A else B) = A + (N : ℝ) * B := by
    calc
      _ = ∑ j : Fin (N + 1), (B + if j = i then A - B else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp
        · simp [h, Ne.symm h]
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  have hu : (∑ i, ∑ j, (1 : ℝ) * 1 * zetaPhaseKernel a ω (u j - u i)) ≤
      ((N : ℝ) + 1) * (A + (N : ℝ) * B) := by
    calc
      _ ≤ ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), if i = j then A else B := by
        simp only [one_mul]
        exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpair i j
      _ = _ := by simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hl := zetaPhase_gramEnergy_zeroFrequency_le ha hs r hr u (fun _ ↦ 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one] at hl
  simp only [one_mul] at hl hu
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have hmul : ((N : ℝ) + 1) * (((N : ℝ) + 1) * a r) ≤
      ((N : ℝ) + 1) * (A + (N : ℝ) * B) := by nlinarith only [hl, hu]
  have h := (mul_le_mul_iff_right₀ hn).mp hmul
  dsimp only [A] at h
  linarith

/-- A long block cannot consist entirely of contact zeros: the zero
frequency limits its length through the total coefficient mass. -/
theorem zetaPhase_contactBlock_mass_constraint (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) (N : ℕ) (θ : ℝ)
    (hz : ∀ k : ℕ, 1 ≤ k → k ≤ N → zetaPhaseKernel a ω ((k : ℝ) * θ) = 0) :
    ((N : ℝ) + 1) * a r ≤ ∑' n : ℕ, a n := by
  have h := zetaPhase_return_ceiling_constraint ha hs r hr N θ 0
    (fun k hk hkN ↦ (hz k hk hkN).le)
  linarith

/-- Exceeding the coefficient-mass threshold forces a strictly positive
return at an explicit finite depth. No density or independence hypothesis on
the real frequencies or the angle is needed. -/
theorem zetaPhase_exists_positive_return (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (r : ℕ) (hr : ω r = 0) (N : ℕ) (θ : ℝ)
    (hmass : (∑' n : ℕ, a n) < ((N : ℝ) + 1) * a r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ 0 < zetaPhaseKernel a ω ((k : ℝ) * θ) := by
  by_contra h
  have hB (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) : zetaPhaseKernel a ω ((k : ℝ) * θ) ≤ 0 := by
    exact le_of_not_gt (fun hpos ↦ h ⟨k, hk, hkN, hpos⟩)
  have hc := zetaPhase_return_ceiling_constraint ha hs r hr N θ 0 hB
  linarith

/-- A common positive amplitude for the first `N` powers of a prime. -/
def zetaPhasePrimeBlockWeight (σ : ℝ) (p N : ℕ) : ℝ :=
  Real.log p * Real.exp (-σ * (N : ℝ) * Real.log p)

/-- The block amplitude is strictly positive for every prime. -/
theorem zetaPhasePrimeBlockWeight_pos (σ : ℝ) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    0 < zetaPhasePrimeBlockWeight σ p N := by
  exact mul_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.exp_pos _)

/-- The smallest block amplitude is below every actual prime-power
amplitude in the block; the real logarithm and cutoff remain explicit. -/
theorem zetaPhasePrimeBlockWeight_le {σ : ℝ} (hσ : 0 ≤ σ)
    {p : ℕ} (hp : p.Prime) {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    zetaPhasePrimeBlockWeight σ p N ≤ zetaPhasePrimeWeight σ (p ^ k) := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [zetaPhasePrimeWeight, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  unfold zetaPhasePrimeBlockWeight
  apply mul_le_mul_of_nonneg_left _ hlog.le
  apply Real.exp_le_exp.mpr
  have hNk : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNk hσ) hlog.le
  nlinarith only [h]

/-- Powers of any prime force a quantitative floor for the actual signed
zeta combination, uniformly in the height. This holds for every summable
nonnegative real-frequency family whose whole kernel is nonnegative. -/
theorem zetaPhase_primePower_floor (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {σ : ℝ} (hσ : 1 < σ) {p : ℕ} (hp : p.Prime) (N : ℕ) (y : ℝ) :
    zetaPhasePrimeBlockWeight σ p N *
        (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) ≤
      (N : ℝ) * ∑' n : ℕ, a n *
        (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
  let W := ∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)
  let c := zetaPhasePrimeBlockWeight σ p N
  have hc : 0 < c := zetaPhasePrimeBlockWeight_pos σ hp N
  have hB (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
      zetaPhaseKernel a ω ((k : ℝ) * (y * Real.log p)) ≤ W / c := by
    have hsingle := (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).summable.le_tsum (p ^ k)
      (fun m _ ↦ mul_nonneg (zetaPhasePrimeWeight_nonneg σ m) (hP _))
    have he : y * Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * (y * Real.log p) := by
      rw [Nat.cast_pow, Real.log_pow]
      ring
    rw [he] at hsingle
    have hw := mul_le_mul_of_nonneg_right
      (zetaPhasePrimeBlockWeight_le (by linarith : 0 ≤ σ) hp hk hkN) (hP ((k : ℝ) * (y * Real.log p)))
    apply (le_div_iff₀ hc).mpr
    dsimp only [W, c]
    nlinarith only [hsingle, hw]
  have h := zetaPhase_return_ceiling_constraint ha hs r hr N (y * Real.log p) (W / c) hB
  have hm := mul_le_mul_of_nonneg_left h hc.le
  have he : c * ((N : ℝ) * (W / c)) = (N : ℝ) * W := by field_simp
  rw [he] at hm
  dsimp only [c, W] at hm
  rwa [(hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).tsum_eq] at hm

/-- A positive zero-frequency mass forces strictly positive arithmetic
work at every height, for every admissible finite or infinite spectrum.
The proof supplies a finite prime-power block rather than relying on a
density assertion or on strictness of an infinite sum without a witness. -/
theorem zetaPhase_logDeriv_pos (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0) (har : 0 < a r)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    0 < ∑' n : ℕ, a n *
      (-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑' n : ℕ, a n) / a r)
  have hmass : 0 < ((N : ℝ) + 1) * a r - (∑' n : ℕ, a n) := by
    have h := (div_lt_iff₀ har).mp hN
    nlinarith only [h, har]
  have hf := zetaPhase_primePower_floor ha hs hP r hr hσ Nat.prime_two N y
  have hpos := mul_pos (zetaPhasePrimeBlockWeight_pos σ Nat.prime_two N) hmass
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) (le_of_not_gt h)
  linarith

/-- The forced prime-power return reduces the budget available to the
whole coupled family of local zero sums. All height costs and pole terms
remain at their actual frequencies. -/
theorem zetaPhase_primePower_add_localZeros_le (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r : ℕ) (hr : ω r = 0)
    {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) {p : ℕ} (hp : p.Prime)
    (N : ℕ) (y : ℝ)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight (ω n * y))) :
    zetaPhasePrimeBlockWeight (1 + x) p N *
        (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) +
      (N : ℝ) * (∑' n : ℕ, a n * (localZetaPoleSum (ω n * y) ((x - 1 / 2 : ℝ) : ℂ)).re) ≤
      (N : ℝ) * ((∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * y) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * y)) := by
  have h := zetaPhase_primeWork_add_localZeros_le ha hs hx hxsmall y hL
  rw [(hasSum_zetaPhase_arithmetic (ω := ω) ha hs (by linarith : 1 < 1 + x) y).tsum_eq] at h
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := zetaPhase_primePower_floor ha hs hP r hr (by linarith : 1 < 1 + x) hp N y
  nlinarith only [hm, hf]

/-- Every actual zero selected by any frequency-one channel obeys the
strictly stronger arithmetic-floor inequality whenever the block mass
exceeds the total coefficient mass. The zero's multiplicity is retained. -/
theorem zetaPhase_primePower_add_multiplicity_le (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t) (r s : ℕ) (hr : ω r = 0) (hsone : ω s = 1)
    (rho : NontrivialZetaZero) (hrho : 3 / 4 ≤ rho.1.re)
    {x : ℝ} (hx : 0 < x) (hxsmall : x ≤ 1 / 4) {p : ℕ} (hp : p.Prime)
    (N : ℕ)
    (hL : Summable (fun n : ℕ ↦ a n * localZetaLogHeight (ω n * rho.1.im))) :
    zetaPhasePrimeBlockWeight (1 + x) p N *
        (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) +
      (N : ℝ) * (a s * (analyticZetaZeroMultiplicity rho : ℝ) / (x + 1 - rho.1.re)) ≤
      (N : ℝ) * ((∑' n : ℕ, a n * (x / (x ^ 2 + (ω n * rho.1.im) ^ 2))) +
        448 * ∑' n : ℕ, a n * localZetaLogHeight (ω n * rho.1.im)) := by
  have h := zetaPhase_primePower_add_localZeros_le ha hs hP r hr hx hxsmall hp N rho.1.im hL
  have hz := (summable_zetaPhase_localZeros ha hs hx hxsmall rho.1.im hL).le_tsum s
    (fun n _ ↦ mul_nonneg (ha n) (localZetaPoleSum_re_nonneg _ hx))
  have hsingle := mul_le_mul_of_nonneg_left
    (multiplicity_div_gap_le_localZetaPoleSum_re rho hrho hx) (ha s)
  simp only [hsone, one_mul] at hz
  rw [← mul_div_assoc] at hsingle
  have hm := mul_le_mul_of_nonneg_left (hsingle.trans hz) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  linarith

end

end RiemannGaussian
