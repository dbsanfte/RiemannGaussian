/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowGram
import RiemannGaussian.ZetaRieszSperner

/-!
# One signed Gram form for every original prime-pair family

The exact arithmetic signs, complex amplitudes and physical cutoffs remain
available alongside their finite energy bounds. No source-scale decay of
the complete signed energy or new zero-free region is asserted.
-/

namespace RiemannGaussian.ZetaRieszWholeWindow
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate Classical
open ZetaRieszWindowGram
/-- A unit-interval feature with independently specified endpoints.
This allows different prime pairs to remain coupled in a common integral. -/
def intervalAtom (l r v : ℝ) : ℂ := (Ioo l r).indicator (fun _ => 1) v

/-- The exact overlap of two independently scaled intervals inside
the common unit integration domain. -/
def unitOverlap (l r l' r' : ℝ) : ℝ :=
  max (min (min r r') 1 - max (max l l') 0) 0

/-- Every unequal-window pair is a genuinely integrable interval
intersection. -/
theorem integrable_intervalAtom_pair (l r l' r' : ℝ) :
    Integrable (fun v => intervalAtom l r v * conj (intervalAtom l' r' v)) := by
  have he : (fun v => intervalAtom l r v * conj (intervalAtom l' r' v)) =
      (Ioo (max l l') (min r r')).indicator (fun _ => (1 : ℂ)) := by
    funext v
    simp only [intervalAtom, indicator_apply, mem_Ioo, max_lt_iff, lt_min_iff]
    split_ifs <;> simp_all
  rw [he]
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))

/-- The Gram entry for independently scaled prime windows retains
both pairs of endpoints and the common unit cutoff. -/
theorem setIntegral_intervalAtom_pair (l r l' r' : ℝ) :
    (∫ v in Ioo 0 1, intervalAtom l r v * conj (intervalAtom l' r' v)) =
      (unitOverlap l r l' r' : ℂ) := by
  have he : (fun v => intervalAtom l r v * conj (intervalAtom l' r' v)) =
      (Ioo (max l l') (min r r')).indicator (fun _ => (1 : ℂ)) := by
    funext v
    simp only [intervalAtom, indicator_apply, mem_Ioo, max_lt_iff, lt_min_iff]
    split_ifs <;> simp_all
  rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    Ioo_inter_Ioo, setIntegral_const, Real.volume_real_Ioo]
  simp [unitOverlap]

/-- An entire complex family with independent interval endpoints.
No norm is taken between families. -/
def intervalLift {ι : Type*} (S : Finset ι) (c : ι → ℂ) (l r : ι → ℝ)
    (v : ℝ) : ℂ := ∑ i ∈ S, c i * intervalAtom (l i) (r i) v

/-- All independent interval features give an integrable finite lift. -/
theorem integrable_intervalLift {ι : Type*} (S : Finset ι) (c : ι → ℂ) (l r : ι → ℝ) :
    Integrable (intervalLift S c l r) := by
  apply integrable_finsetSum S
  intro i _
  apply Integrable.const_mul
  exact (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))

/-- The exact full quadratic expansion keeps correlations between
unequal prime-pair families as well as inside each family. -/
theorem intervalLift_mul_conj {ι : Type*} (S : Finset ι) (c : ι → ℂ) (l r : ι → ℝ)
    (v : ℝ) :
    intervalLift S c l r v * conj (intervalLift S c l r v) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        (intervalAtom (l i) (r i) v * conj (intervalAtom (l j) (r j) v)) := by
  simp only [intervalLift, map_sum, map_mul, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full unequal-window lift has integrable complex energy. -/
theorem integrable_intervalLift_mul_conj {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (l r : ι → ℝ) :
    Integrable (fun v => intervalLift S c l r v * conj (intervalLift S c l r v)) := by
  simp_rw [intervalLift_mul_conj]
  exact integrable_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ =>
    (integrable_intervalAtom_pair (l i) (r i) (l j) (r j)).const_mul (c i * conj (c j))))

/-- The full unequal-window lift is genuinely square-integrable. -/
theorem integrable_intervalLift_norm_sq {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (l r : ι → ℝ) : Integrable (fun v => ‖intervalLift S c l r v‖ ^ 2) := by
  have h := (integrable_intervalLift_mul_conj S c l r).re
  simpa only [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using h

/-- The complete finite signed energy has an exact Gram expansion
for all independently scaled arithmetic windows. -/
theorem setIntegral_intervalLift_norm_sq {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (l r : ι → ℝ) :
    (∫ v in Ioo 0 1, ‖intervalLift S c l r v‖ ^ 2) =
      (∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        (unitOverlap (l i) (r i) (l j) (r j) : ℂ)).re := by
  have he : (∫ v in Ioo 0 1, intervalLift S c l r v * conj (intervalLift S c l r v)) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        (unitOverlap (l i) (r i) (l j) (r j) : ℂ) := by
    simp_rw [intervalLift_mul_conj]
    rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ =>
      ((integrable_intervalAtom_pair (l i) (r i) (l j) (r j)).const_mul
        (c i * conj (c j))).integrableOn))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum S (fun j _ =>
      ((integrable_intervalAtom_pair (l i) (r i) (l j) (r j)).const_mul
        (c i * conj (c j))).integrableOn)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, setIntegral_intervalAtom_pair]
  have h := congrArg (RCLike.re : ℂ → ℝ) he
  rw [← integral_re (integrable_intervalLift_mul_conj S c l r).integrableOn] at h
  simpa only [RCLike.re_eq_complex_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq] using h

/-- One Gram bound for all families together, with no count-of-families
factor and no loss of their relative complex phases. -/
theorem norm_integral_intervalLift_sq_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (l r : ι → ℝ) :
    ‖∫ v in Ioo 0 1, intervalLift S c l r v‖ ^ 2 ≤
      (∑ i ∈ S, ∑ j ∈ S, (c i * conj (c j)) *
        (unitOverlap (l i) (r i) (l j) (r j) : ℂ)).re := by
  rw [← setIntegral_intervalLift_norm_sq]
  simpa only [one_mul] using norm_setIntegral_sq_le (by norm_num : (0 : ℝ) < 1)
    (integrable_intervalLift S c l r).integrableOn
    (integrable_intervalLift_norm_sq S c l r).integrableOn

/-- Rescaling each prime pair to the common unit interval preserves
its exact four-term cancellation and pays precisely its smaller prime log. -/
theorem primePair_scaled_overlap {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (u : ℝ) :
    a * max (min (u / a) 1 - max ((u - b) / a) 0) 0 =
      ZetaSquarefreeRieszWindows.primePairTent a b u := by
  have hmin : min (u / a) 1 = min u a / a := by
    simpa only [div_self ha.ne'] using min_div_div_right ha.le u a
  have hmax : max ((u - b) / a) 0 = max (u - b) 0 / a := by
    simpa only [zero_div] using max_div_div_right ha.le (u - b) 0
  rw [hmin, hmax, ← sub_div]
  have houter := max_div_div_right ha.le (min u a - max (u - b) 0) 0
  rw [zero_div] at houter
  rw [houter, mul_div_cancel₀ _ ha.ne',
    ZetaSquarefreeRieszWindows.primePairTent_eq_overlap ha.le hb]

/-- Every prime tent is one scaled complex interval integral on the
same unit domain, allowing different prime pairs to interfere. -/
theorem integral_scaled_interval {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (u : ℝ) (c : ℂ) :
    (∫ v in Ioo 0 1, (a : ℂ) * c * intervalAtom ((u - b) / a) (u / a) v) =
      c * (ZetaSquarefreeRieszWindows.primePairTent a b u : ℂ) := by
  rw [integral_const_mul]
  have he : (∫ v in Ioo 0 1, intervalAtom ((u - b) / a) (u / a) v) =
      (max (min (u / a) 1 - max ((u - b) / a) 0) 0 : ℝ) := by
    unfold intervalAtom
    rw [integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, Ioo_inter_Ioo,
      setIntegral_const, Real.volume_real_Ioo]
    simp
  rw [he]
  calc
    _ = c * ((a * max (min (u / a) 1 - max ((u - b) / a) 0) 0 : ℝ) : ℂ) := by
      push_cast
      ring
    _ = _ := by rw [primePair_scaled_overlap ha hb]

/-- The full original complex amplitude, exact smaller-prime scaling
and signed divisor factor for one labelled whole-band window. -/
def primeWindowCoefficient (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (p : ℕ → ℕ) (z : (_ : ℕ) × ℕ) : ℂ :=
  (Real.log (p z.1) : ℂ) * ZetaArithmeticBandCorrelation.bandAmplitude L P N t z.1 *
    ((ArithmeticFunction.moebius z.2 : ℤ) : ℂ)

/-- The physical lower edge of a divisor window after exact
rescaling by its own first prime logarithm. -/
def primeWindowLower (L : ℝ) (p q : ℕ → ℕ) (z : (_ : ℕ) × ℕ) : ℝ :=
  (L - Real.log z.2 - Real.log (q z.1)) / Real.log (p z.1)

/-- The upper edge uses the same physical length and divisor as the
lower edge, before clipping to the common unit interval. -/
def primeWindowUpper (L : ℝ) (p : ℕ → ℕ) (z : (_ : ℕ) × ℕ) : ℝ :=
  (L - Real.log z.2) / Real.log (p z.1)

/-- Every original integer and every one of its cofactor divisors
remain labelled in one common complex lift across all prime pairs. -/
def primeWindowLift (S : Finset ℕ) (p q m : ℕ → ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t v : ℝ) : ℂ :=
  intervalLift (S.sigma (fun n => (m n).divisors))
    (primeWindowCoefficient L P N t p) (primeWindowLower L p q) (primeWindowUpper L p) v

/-- The full signed Gram form includes cross terms between different
prime pairs, original integers, divisors, cutoff locations and phases. -/
def primeWindowGram (S : Finset ℕ) (p q m : ℕ → ℕ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ S.sigma (fun n => (m n).divisors), ∑ j ∈ S.sigma (fun n => (m n).divisors),
    (primeWindowCoefficient L P N t p i * conj (primeWindowCoefficient L P N t p j)) *
      (unitOverlap (primeWindowLower L p q i) (primeWindowUpper L p i)
        (primeWindowLower L p q j) (primeWindowUpper L p j) : ℂ)).re

/-- The original finite carrier is exactly the integral of the
single lift containing every prime-pair family. No family norms are taken. -/
theorem sum_bandWeight_eq_integral_primeWindowLift (S : Finset ℕ) (p q m : ℕ → ℕ)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (hS : ∀ n ∈ S, (p n).Prime ∧ (q n).Prime ∧ p n ≠ q n ∧
      n = p n * (q n * m n) ∧ ¬ p n ∣ m n ∧ ¬ q n ∣ m n) :
    (∑ n ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      ∫ v in Ioo 0 1, primeWindowLift S p q m L P N t v := by
  unfold primeWindowLift intervalLift
  rw [integral_finsetSum _ (fun z _ => by
    apply Integrable.const_mul
    exact ((integrable_indicator_iff measurableSet_Ioo).mpr
      (integrableOn_const (by simp))).integrableOn), Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hp, hq, hpq, he, hpm, hqm⟩ := hS n hn
  have hr : VaughanLogAverage.riesz L n =
      ∑ d ∈ (m n).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ZetaSquarefreeRieszWindows.primePairTent (Real.log (p n)) (Real.log (q n))
          (L - Real.log d) := by
    calc
      _ = VaughanLogAverage.riesz L (p n * (q n * m n)) := congrArg _ he
      _ = _ := ZetaSquarefreeRieszWindows.riesz_two_primes_eq_tent L hp hq hpq hpm hqm
  rw [ZetaArithmeticBandCorrelation.bandWeight_eq_amplitude_mul_riesz, hr]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hh := integral_scaled_interval (a := Real.log (p n))
    (Real.log_pos (by exact_mod_cast hp.one_lt))
    (Real.log_natCast_nonneg (q n)) (L - Real.log d)
    (ZetaArithmeticBandCorrelation.bandAmplitude L P N t n *
      ((ArithmeticFunction.moebius d : ℤ) : ℂ))
  calc
    _ = (ZetaArithmeticBandCorrelation.bandAmplitude L P N t n *
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
        (ZetaSquarefreeRieszWindows.primePairTent (Real.log (p n)) (Real.log (q n))
          (L - Real.log d) : ℂ) := by push_cast; ring
    _ = _ := by
      rw [← hh]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [primeWindowCoefficient, primeWindowLower, primeWindowUpper]
      ring

/-- Genuine energy of the complete lift is exactly the finite signed
Gram form. All integrability obligations are discharged. -/
theorem integral_primeWindowLift_norm_sq (S : Finset ℕ) (p q m : ℕ → ℕ)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∫ v in Ioo 0 1, ‖primeWindowLift S p q m L P N t v‖ ^ 2) =
      primeWindowGram S p q m L P N t :=
  setIntegral_intervalLift_norm_sq _ _ _ _

/-- The full original arithmetic sum is bounded by one signed energy
across all prime-pair families. No number-of-families cost is introduced. -/
theorem norm_sum_bandWeight_sq_le_primeWindowGram (S : Finset ℕ) (p q m : ℕ → ℕ)
    (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (hS : ∀ n ∈ S, (p n).Prime ∧ (q n).Prime ∧ p n ≠ q n ∧
      n = p n * (q n * m n) ∧ ¬ p n ∣ m n ∧ ¬ q n ∣ m n) :
    ‖∑ n ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t n‖ ^ 2 ≤
      primeWindowGram S p q m L P N t := by
  rw [sum_bandWeight_eq_integral_primeWindowLift S p q m L P N t hS]
  exact norm_integral_intervalLift_sq_le _ _ _ _

/-- Only identically zero original summands are removed; this is
not an additional arithmetic truncation. -/
def activeOriginalBand (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (fun n => ZetaRieszConditionedEnergy.bandWeight L P N t n ≠ 0)

/-- Every nonzero original atom has two distinct prime factors,
with squarefreeness proved from its literal coefficient. -/
theorem activeOriginalBand_support (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {n : ℕ} (hn : n ∈ activeOriginalBand L P N t) :
    Squarefree n ∧ 2 ≤ n.primeFactors.card := by
  obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hn
  have hf : SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) n ≠ 0 := by
    simpa only [ZetaRieszConditionedEnergy.bandWeight, if_pos hb] using hc
  exact ZetaRieszSperner.coefficient_ne_zero_support (left_ne_zero_of_mul hf)

/-- The nonzero support sums to exactly the full original carrier,
with no approximation, cutoff error or missing coefficient. -/
theorem sum_activeOriginalBand (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∑ n ∈ activeOriginalBand L P N t, ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [activeOriginalBand, Finset.sum_filter]
  unfold zetaArithmeticBand
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ZetaRieszConditionedEnergy.bandWeight, if_pos hn]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

/-- Retain the complete two-smallest-prime factorization certificate,
including cofactor squarefreeness, prime ordering and exact prime count. -/
def smallestPairFactorization (n p q m : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * (q * m) ∧ Squarefree m ∧
    ¬ p ∣ m ∧ ¬ q ∣ m ∧ (∀ r ∈ n.primeFactors, p ≤ r) ∧
    (∀ r ∈ m.primeFactors, q ≤ r) ∧ m.primeFactors.card = n.primeFactors.card - 2

/-- The whole original carrier has a single cutoff-preserving signed
Gram bound with all prime-selection and support premises discharged. The
complete smallest-prime factorization data remain available. This does not
assert source-scale decay of the explicit Gram form or a zero-free region. -/
theorem exists_original_band_primeWindowGram (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ∃ p q m : ℕ → ℕ,
      (∀ n ∈ activeOriginalBand L P N t, smallestPairFactorization n (p n) (q n) (m n)) ∧
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t =
        (∫ v in Ioo 0 1, primeWindowLift (activeOriginalBand L P N t) p q m L P N t v) ∧
      ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ^ 2 ≤
        primeWindowGram (activeOriginalBand L P N t) p q m L P N t := by
  have hex : ∀ n : ℕ, ∃ p q m : ℕ, n ∈ activeOriginalBand L P N t →
      smallestPairFactorization n p q m := by
    intro n
    by_cases hn : n ∈ activeOriginalBand L P N t
    · obtain ⟨hs, hk⟩ := activeOriginalBand_support L P N t hn
      obtain ⟨p, q, m, h⟩ := ZetaRieszSperner.exists_two_smallest_factorization hs hk
      exact ⟨p, q, m, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => False.elim (hn h)⟩
  choose p q m hs using hex
  have hS : ∀ n ∈ activeOriginalBand L P N t,
      (p n).Prime ∧ (q n).Prime ∧ p n ≠ q n ∧ n = p n * (q n * m n) ∧
      ¬ p n ∣ m n ∧ ¬ q n ∣ m n := by
    intro n hn
    obtain ⟨hp, hq, hpq, he, _, hpm, hqm, _, _, _⟩ := hs n hn
    exact ⟨hp, hq, hpq, he, hpm, hqm⟩
  refine ⟨p, q, m, hs, ?_, ?_⟩
  · rw [← sum_activeOriginalBand L P N t]
    exact sum_bandWeight_eq_integral_primeWindowLift _ _ _ _ _ _ _ _ hS
  · rw [← sum_activeOriginalBand L P N t]
    exact norm_sum_bandWeight_sq_le_primeWindowGram _ _ _ _ _ _ _ _ hS

end
end RiemannGaussian.ZetaRieszWholeWindow
