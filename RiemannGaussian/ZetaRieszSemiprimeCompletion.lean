/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimePrefixDecay

/-!
# Completed semiprimes on the original integer band

Genuine convergent prime completions are reindexed by their integer
products. The actual divisor majorant pays both omitted original-band
tails. The actual-minus-completed semiprime coefficient vanishes above
the physical prime cutoff, leaving only the independently bounded prefix.
All integer floors, product phases and factorial shifts are retained.
-/

namespace RiemannGaussian.ZetaRieszSemiprimeCompletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor
open ZetaRieszSemiprimePrefix
open ZetaRieszSemiprimePrefixDecay

/-- One completed cofactor series reindexed on its actual integer
multiples, with the prime quotient kept as a support condition. -/
def pairLift (L : ℝ) (a n : ℕ) : ℂ :=
  if a ∣ n ∧ (n / a).Prime then ((-Real.log n * Real.log a / L : ℝ) : ℂ) else 0

/-- Dilation to actual integer labels preserves the genuine complete
series and its exact factorial filter, with no unproved rearrangement. -/
theorem hasSum_pairLift {a : ℕ} (ha : 0 < a) (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => pairLift L a n * zetaPrimeFilterKernel P N s n)
      (-((Real.log a : ℂ) / (L : ℂ)) * completedPrimeProductFilter a P N s) := by
  have hinj : Function.Injective (fun p : ℕ => a * p) := fun _ _ h => Nat.eq_of_mul_eq_mul_left ha h
  have hz (n : ℕ) (hn : n ∉ Set.range (fun p : ℕ => a * p)) :
      pairLift L a n * zetaPrimeFilterKernel P N s n = 0 := by
    have hnd : ¬ a ∣ n := by
      intro hd
      exact hn ⟨n / a, Nat.mul_div_cancel' hd⟩
    simp [pairLift, hnd]
  apply (hinj.hasSum_iff hz).mp
  have h := (hasSum_completedPrimeProductFilter hs ha P N).mul_left
    (-((Real.log a : ℂ) / (L : ℂ)))
  apply h.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp only [Function.comp_apply, pairLift, dvd_mul_right, Nat.mul_div_cancel_left _ ha,
      hp, and_self, if_true, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  · simp [Function.comp_apply, pairLift, Nat.mul_div_cancel_left _ ha, hp]

/-- The completed arithmetic coefficient counts every selected
cofactor incidence at its exact integer label. -/
def integerCoefficient (L : ℝ) (A : Finset ℕ) (n : ℕ) : ℂ := ∑ a ∈ A, pairLift L a n

/-- The full completed head is the genuinely convergent integer
series of its coefficient; duplicate factorizations are retained explicitly. -/
theorem hasSum_integerCoefficient (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => integerCoefficient L A n * zetaPrimeFilterKernel P N s n)
      (completedCofactorHead A P N s L) := by
  have h := hasSum_sum (s := A) (fun a ha => hasSum_pairLift (hA a ha) L P N hs)
  apply h.congr_fun
  intro n
  simp only [integerCoefficient, Finset.sum_mul]

/-- At a semiprime label at most two prime cofactor incidences exist.
Their small-prime logarithmic mass is uniformly bounded by twice log K. -/
theorem selected_prime_cofactor_log_mass_le (A : Finset ℕ) (K n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a ≤ K) :
    (∑ a ∈ A.filter (fun a => a ∣ n ∧ (n / a).Prime), Real.log a) ≤ 2 * Real.log K := by
  let S := A.filter (fun a => a ∣ n ∧ (n / a).Prime)
  have hcard : S.card ≤ 2 := by
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      have ha' := Finset.mem_filter.mp ha
      let p := n / a
      have hp : p.Prime := ha'.2.2
      have hn : a * p = n := Nat.mul_div_cancel' ha'.2.1
      have hsub : S ⊆ {a, p} := by
        intro b hb
        have hb' := Finset.mem_filter.mp hb
        have hbp := (hA b hb'.1).1
        have hdiv : b ∣ a * p := hn ▸ hb'.2.1
        rcases hbp.dvd_mul.mp hdiv with hd | hd
        · have he : b = a := (Nat.prime_dvd_prime_iff_eq hbp (hA a ha'.1).1).mp hd
          simp [he]
        · have he : b = p := (Nat.prime_dvd_prime_iff_eq hbp hp).mp hd
          simp [he]
      apply (Finset.card_le_card hsub).trans
      by_cases he : a = p <;> simp [he]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  calc
    _ ≤ ∑ _a ∈ S, Real.log K := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' := hA a (Finset.mem_filter.mp ha).1
      exact Real.log_le_log (by exact_mod_cast ha'.1.pos) (by exact_mod_cast ha'.2)
    _ = (S.card : ℝ) * Real.log K := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_natCast_nonneg K)

/-- A logarithmic length containing twice the cofactor-head logarithm
makes the complete integer coefficient fit the original divisor majorant. -/
theorem norm_integerCoefficient_le_majorant (A : Finset ℕ) (K n : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ a ≤ K) {L : ℝ} (hL : 0 < L)
    (hKL : 2 * Real.log K ≤ L) :
    ‖integerCoefficient L A n‖ ≤ zetaMoebiusLogMajorant n := by
  have he : integerCoefficient L A n =
      ((-Real.log n / L : ℝ) : ℂ) *
        ((∑ a ∈ A.filter (fun a => a ∣ n ∧ (n / a).Prime), Real.log a : ℝ) : ℂ) := by
    simp only [integerCoefficient, pairLift, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∣ n ∧ (n / a).Prime
    · simp only [if_pos ha, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    · simp [ha]
  have hm0 : 0 ≤ ∑ a ∈ A.filter (fun a => a ∣ n ∧ (n / a).Prime), Real.log a :=
    Finset.sum_nonneg fun a _ => Real.log_natCast_nonneg a
  have hmL := (selected_prime_cofactor_log_mass_le A K n hA).trans hKL
  rw [he, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_pos hL, abs_of_nonneg hm0]
  apply ((mul_le_mul_of_nonneg_left hmL (div_nonneg (Real.log_natCast_nonneg n) hL.le)).trans_eq
    (div_mul_cancel₀ _ hL.ne')).trans
  by_cases hn : n = 0
  · simp [hn, zetaMoebiusLogMajorant]
  · unfold zetaMoebiusLogMajorant
    have hmem : (1, n) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn⟩
    exact Finset.single_le_sum (fun a _ => Real.log_natCast_nonneg a.2) hmem

/-- The actual length eventually contains both small-cofactor
logarithms, making the full integer completion uniformly dominated. -/
theorem eventually_two_head_logs_le_length {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.log ((N ^ 2 : ℕ) : ℝ) ≤ SquarefreeVaughanLogSource.length u N := by
  obtain ⟨c, hc, hlength⟩ := eventually_linear_length_lower hu hu1
  have hl : Tendsto (fun N : ℕ => 4 * Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, pow_one, one_mul, add_zero, mul_div_assoc, mul_zero] using h.const_mul 4
  filter_upwards [hlength, hl.eventually_lt_const hc, eventually_ge_atTop 1] with N hL hlog hN
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := ((div_lt_iff₀ hp).mp hlog).le.trans hL
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, show (2 : ℝ) * (2 * Real.log N) =
    4 * Real.log N by ring] using h

/-- The literal completed integer series and original finite band
differ by an independently vanishing error, uniformly in the moving prime
cofactor head. The complete divisor majorant pays both omitted band tails. -/
theorem tendsto_completed_integer_filter_sub_band (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2)
    (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ =>
      zetaArithmeticFilter (integerCoefficient (SquarefreeVaughanLogSource.length u N) (A N)) P N
        (3 / 2 + Complex.I * y) -
      zetaArithmeticBand (integerCoefficient (SquarefreeVaughanLogSource.length u N) (A N)) P N y)
        atTop (𝓝 0) := by
  let b (N n : ℕ) : ℂ := if 2 * Real.log ((N ^ 2 : ℕ) : ℝ) ≤ SquarefreeVaughanLogSource.length u N
    then integerCoefficient (SquarefreeVaughanLogSource.length u N) (A N) n else 0
  have hb : ∀ N n, ‖b N n‖ ≤ zetaMoebiusLogMajorant n := by
    intro N n
    dsimp [b]
    split_ifs with hN
    · exact norm_integerCoefficient_le_majorant (A N) (N ^ 2) n (hA N)
        (SquarefreeVaughanLogSource.length_pos u N) hN
    · simpa using zetaMoebiusLogMajorant_nonneg n
  apply (tendsto_zetaDominatedFilter_sub_band b hb P y).congr'
  filter_upwards [eventually_two_head_logs_le_length hu hu1] with N hN
  have he : b N = integerCoefficient (SquarefreeVaughanLogSource.length u N) (A N) := by
    funext n
    simp only [b, if_pos hN]
  rw [he]

/-- The completed cofactor bound now holds on the ORIGINAL finite
integer band, with its exact factorial filter and moving prime cofactor
head. This is still the completed coefficient, before the prefix correction. -/
theorem tendsto_completed_integer_band (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaArithmeticBand (integerCoefficient
        (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (A N)) P N rho.1.im) atTop (𝓝 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hau : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] using hu1
  have hp : Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hau).comp (tendsto_add_atTop_nat 1)
  have herr := hp.mul (tendsto_completed_integer_filter_sub_band A hA P rho.1.im hu hu1)
  have hc := tendsto_completed_quadratic_cofactor_head rho hrho hexposed P A
    (fun N a ha => ⟨(hA N a ha).1.pos, (hA N a ha).2⟩)
  have h := hc.sub herr
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have he : zetaArithmeticFilter (integerCoefficient (SquarefreeVaughanLogSource.length u N) (A N))
      P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) = completedCofactorHead (A N) P N
        (3 / 2 + Complex.I * (rho.1.im : ℂ)) (SquarefreeVaughanLogSource.length u N) :=
    (hasSum_integerCoefficient (A N) (fun a ha => (hA N a ha).1.pos)
      (SquarefreeVaughanLogSource.length u N) P N (by norm_num)).tsum_eq
  rw [he]
  dsimp [u]
  ring

/-- A single cofactor's finite integer band is exactly its prime
quotient band. Dilation is injective and its prime cutoff is derived from
the original product ceiling. -/
theorem pairLift_band_eq_prime_sum {a : ℕ} (ha : 0 < a) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaArithmeticBand (pairLift L a) P N y =
      ∑ p ∈ Nat.primesLE (2 ^ (32 * N)), if a * p ∈ zetaPrimeLogBand N then
        completedPairCoefficient L a p *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0 := by
  let Q := (Nat.primesLE (2 ^ (32 * N))).filter (fun p => a * p ∈ zetaPrimeLogBand N)
  let T := (zetaPrimeLogBand N).filter (fun n => a ∣ n ∧ (n / a).Prime)
  have himage : Q.image (fun p => a * p) = T := by
    ext n
    constructor
    · intro hn
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hp'.2, dvd_mul_right a p,
        by simpa only [Nat.mul_div_cancel_left _ ha] using (Nat.mem_primesLE.mp hp'.1).2⟩
    · intro hn
      have hn' := Finset.mem_filter.mp hn
      have he : a * (n / a) = n := Nat.mul_div_cancel' hn'.2.1
      refine Finset.mem_image.mpr ⟨n / a, ?_, he⟩
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_primesLE.mpr ⟨?_, hn'.2.2⟩, by simpa only [he] using hn'.1⟩
      exact (Nat.div_le_self n a).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hn'.1).1).2
  have hinj : Set.InjOn (fun p : ℕ => a * p) Q :=
    fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left ha h
  have he : zetaArithmeticBand (pairLift L a) P N y =
      ∑ n ∈ T, ((-Real.log n * Real.log a / L : ℝ) : ℂ) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
    simp only [zetaArithmeticBand, pairLift, T, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by split_ifs <;> simp)
  rw [he, ← himage, Finset.sum_image hinj]
  simp only [Q, Finset.sum_filter, completedPairCoefficient]

/-- Summing over the small prime head preserves every integer
incidence and gives an exact finite pair formula for the completed band. -/
theorem integer_band_eq_completed_pairs (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaArithmeticBand (integerCoefficient L A) P N y =
      ∑ a ∈ A, ∑ p ∈ Nat.primesLE (2 ^ (32 * N)), if a * p ∈ zetaPrimeLogBand N then
        completedPairCoefficient L a p *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0 := by
  have he : zetaArithmeticBand (integerCoefficient L A) P N y =
      ∑ a ∈ A, zetaArithmeticBand (pairLift L a) P N y := by
    simp only [zetaArithmeticBand, integerCoefficient, Finset.sum_mul]
    exact Finset.sum_comm
  rw [he]
  exact Finset.sum_congr rfl (fun a ha => pairLift_band_eq_prime_sum (hA a ha) L P N y)

/-- At a prime beyond the physical cutoff the completion error is
exactly zero. Saturation also rules out the repeated-prime diagonal. -/
theorem semiprime_completion_error_eq_zero_above {u : ℝ} {N a p : ℕ}
    (ha : a.Prime) (hp : p.Prime) (haL : Real.log a ≤ SquarefreeVaughanLogSource.length u N)
    (hpX : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (a * p) -
      completedPairCoefficient (SquarefreeVaughanLogSource.length u N) a p = 0 := by
  have hLp := (ZetaRieszCompositeBoundaryWindow.physical_log_lt_iff u N hp.pos).mpr hpX
  have hpa : ¬ p ∣ a := by
    intro hd
    have he : p = a := (Nat.prime_dvd_prime_iff_eq hp ha).mp hd
    rw [he] at hLp
    linarith
  have he := ZetaRieszFixedCofactor.coefficient_prime_pair_above_cutoff ha hp hpa haL hLp.le
  simpa only [Nat.mul_comm p a, completedPairCoefficient, sub_self] using
    congrArg (fun z => z - completedPairCoefficient (SquarefreeVaughanLogSource.length u N) a p) he

/-- The exact actual-minus-completed pair band is confined to the
physical prime prefix. No sign, factorial order or cutoff boundary is dropped. -/
theorem actual_pair_band_sub_completed_eq_prefix (A : Finset ℕ) (P : Polynomial ℂ)
    (N : ℕ) (y u : ℝ) (hA : ∀ a ∈ A, a.Prime ∧ Real.log a ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ a ∈ A, ∑ p ∈ Nat.primesLE (2 ^ (32 * N)), if a * p ∈ zetaPrimeLogBand N then
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (a * p) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0) -
      zetaArithmeticBand (integerCoefficient (SquarefreeVaughanLogSource.length u N) A) P N y =
    ∑ a ∈ A, ∑ p ∈ (Nat.primesLE (2 ^ (32 * N))).filter
      (fun p => p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2),
      (if a * p ∈ zetaPrimeLogBand N then
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (a * p) -
          completedPairCoefficient (SquarefreeVaughanLogSource.length u N) a p else 0) *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) := by
  rw [integer_band_eq_completed_pairs A (fun a ha => (hA a ha).1.pos)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : a * p ∈ zetaPrimeLogBand N
  · by_cases hpX : p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
    · simp only [if_pos hband, if_pos hpX, sub_mul]
    · have hz := semiprime_completion_error_eq_zero_above (hA a ha).1
        (Nat.mem_primesLE.mp hp).2 (hA a ha).2 (lt_of_not_ge hpX)
      simp only [if_pos hband, if_neg hpX, ← sub_mul, hz, zero_mul]
  · simp [hband]

end
end RiemannGaussian.ZetaRieszSemiprimeCompletion
