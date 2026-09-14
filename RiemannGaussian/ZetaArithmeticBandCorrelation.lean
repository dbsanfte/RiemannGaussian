/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaArithmeticAffine

/-!
# Literal band phases and divisor correlations

The full complex band, factorial filter and divisor support are retained
in affine correlation and logarithmic phase-freezing identities. The named
norm relaxations pay their complete amplitude costs; a phase estimate alone
does not give the independent signed arithmetic floor.
-/

namespace RiemannGaussian.ZetaArithmeticBandCorrelation
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory Set Filter Topology
open ZetaArithmeticAffine

/-- Along a surviving progression, the same determinant that controls
prime compatibility controls the derivative of the logarithmic phase ratio. -/
theorem hasDerivAt_log_ratio {B D x₀ y₀ H k : ℝ}
    (hdet : B * x₀ - D * y₀ = H) (hxpos : 0 < x₀ + D * k)
    (hypos : 0 < y₀ + B * k) :
    HasDerivAt (fun t : ℝ => Real.log (x₀ + D * t) - Real.log (y₀ + B * t))
      (-H / ((x₀ + D * k) * (y₀ + B * k))) k := by
  have hx : HasDerivAt (fun t : ℝ => x₀ + D * t) D k := by
    convert! (hasDerivAt_const k x₀).add (hasDerivAt_const_mul D) using 1
    simp
  have hy : HasDerivAt (fun t : ℝ => y₀ + B * t) B k := by
    convert! (hasDerivAt_const k y₀).add (hasDerivAt_const_mul B) using 1
    simp
  convert! (hx.log hxpos.ne').sub (hy.log hypos.ne') using 1
  field_simp [hxpos.ne', hypos.ne',
    show y₀ + k * B ≠ 0 by nlinarith only [hypos],
    show x₀ + k * D ≠ 0 by nlinarith only [hxpos]]
  nlinarith only [hdet]

/-- A unit complex phase, with its actual real angle retained. -/
def unitPhase (u : ℝ) : ℂ := Complex.exp (Complex.I * (u : ℂ))

/-- Every real phase has exactly unit norm. -/
theorem norm_unitPhase (u : ℝ) : ‖unitPhase u‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

/-- Replacing one phase by another costs at most their angular separation. -/
theorem norm_unitPhase_sub_le (u v : ℝ) : ‖unitPhase u - unitPhase v‖ ≤ |u - v| := by
  have he : unitPhase u - unitPhase v = unitPhase v * (unitPhase (u - v) - 1) := by
    unfold unitPhase
    rw [mul_sub, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · ring
  rw [he, norm_mul, norm_unitPhase, one_mul]
  simpa only [unitPhase, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

/-- A phase may be replaced by one common angle with an explicit weighted
error; the main term remains the full signed complex sum. -/
theorem norm_sum_phase_freeze_le {ι : Type*} (S : Finset ι) (A : ι → ℂ)
    (φ : ι → ℝ) (φ₀ : ℝ) :
    ‖(∑ i ∈ S, A i * unitPhase (φ i)) - unitPhase φ₀ * ∑ i ∈ S, A i‖ ≤
      ∑ i ∈ S, ‖A i‖ * |φ i - φ₀| := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have he : A i * unitPhase (φ i) - unitPhase φ₀ * A i =
      A i * (unitPhase (φ i) - unitPhase φ₀) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_unitPhase_sub_le _ _) (norm_nonneg _)

/-- A uniform angular allowance gives a uniform error on the exact signed sum. -/
theorem norm_sum_phase_freeze_le_uniform {ι : Type*} (S : Finset ι) (A : ι → ℂ)
    (φ : ι → ℝ) (φ₀ ε : ℝ) (hε : ∀ i ∈ S, |φ i - φ₀| ≤ ε) :
    ‖(∑ i ∈ S, A i * unitPhase (φ i)) - unitPhase φ₀ * ∑ i ∈ S, A i‖ ≤
      ε * ∑ i ∈ S, ‖A i‖ := by
  apply (norm_sum_phase_freeze_le S A φ φ₀).trans
  calc
    _ ≤ ∑ i ∈ S, ‖A i‖ * ε := Finset.sum_le_sum
      (fun i hi => mul_le_mul_of_nonneg_left (hε i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The complete non-Riesz factor of the original band weight. Squarefree
support, prime deletion, normalization and complex filter are unchanged. -/
def bandAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ zetaPrimeLogBand N ∧ Squarefree n ∧ ¬ n.Prime then
    ((-Real.log n / L : ℝ) : ℂ) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) n else 0

/-- The literal original band weight factors into its signed Riesz divisor
sum and its original complex amplitude. -/
theorem bandWeight_eq_amplitude_mul_riesz (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (n : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L P N t n =
      bandAmplitude L P N t n * (VaughanLogAverage.riesz L n : ℂ) := by
  by_cases hb : n ∈ zetaPrimeLogBand N
  · by_cases ha : Squarefree n ∧ ¬ n.Prime
    · simp only [ZetaRieszConditionedEnergy.bandWeight, bandAmplitude,
        SquarefreeVaughanLogSource.coefficient, hb, ha, true_and, if_true,
        not_false_eq_true, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    · simp [ZetaRieszConditionedEnergy.bandWeight, bandAmplitude,
        SquarefreeVaughanLogSource.coefficient, hb, ha]
  · simp [ZetaRieszConditionedEnergy.bandWeight, bandAmplitude, hb]

/-- One actual signed divisor coefficient, with its logarithmic cutoff intact. -/
def rieszDivisorWeight (L : ℝ) (r : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius r : ℤ) : ℝ) * max 0 (L - Real.log r) : ℝ)

/-- Expand the original band weight over its literal divisors without taking norms. -/
theorem bandWeight_eq_divisor_sum (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (n : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L P N t n =
      ∑ r ∈ n.divisors, rieszDivisorWeight L r * bandAmplitude L P N t n := by
  rw [bandWeight_eq_amplitude_mul_riesz]
  simp only [VaughanLogAverage.riesz, Complex.ofReal_sum, rieszDivisorWeight,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Both complete signed divisor families remain coupled in every original
Riesz pair, including the full original phase and amplitude factors. -/
theorem bandWeight_pair_divisors (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) (x y : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L P N t x *
        starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N t y) =
      ∑ r ∈ x.divisors, ∑ s ∈ y.divisors,
        (rieszDivisorWeight L r * starRingEnd ℂ (rieszDivisorWeight L s)) *
          (bandAmplitude L P N t x * starRingEnd ℂ (bandAmplitude L P N t y)) := by
  rw [bandWeight_eq_divisor_sum, bandWeight_eq_divisor_sum]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- Divisor pairs inherit the full cross-prime obstruction before they are
summed: their dilated products can share only divisors of the actual lag. -/
theorem divisor_collision_gcd_dvd {b d x y r s h : ℤ}
    (he : b * x - d * y = h) (hr : r ∣ x) (hs : s ∣ y) :
    (Int.gcd (b * r) (d * s) : ℤ) ∣ h := by
  rw [← he]
  exact dvd_sub
    (dvd_trans (Int.gcd_dvd_left _ _) (mul_dvd_mul (dvd_refl b) hr))
    (dvd_trans (Int.gcd_dvd_right _ _) (mul_dvd_mul (dvd_refl d) hs))

/-- Unit-lag divisor pairs have coprime dilated products, simultaneously
retaining the r/s, b/s, d/r and b/d prime restrictions. -/
theorem unit_lag_divisor_products_coprime {b d x y r s : ℤ}
    (he : b * x - d * y = 1) (hr : r ∣ x) (hs : s ∣ y) :
    Int.gcd (b * r) (d * s) = 1 := by
  have hd := divisor_collision_gcd_dvd he hr hs
  simpa only [← Int.natCast_one, Int.natCast_dvd_natCast, Nat.dvd_one] using hd

/-- If every nonunit divisor lies beyond the cutoff, the entire signed
Riesz factor equals its positive unit ramp. -/
theorem riesz_eq_unit_of_rough {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hrough : ∀ d ∈ n.divisors, d ≠ 1 → L ≤ Real.log d) :
    VaughanLogAverage.riesz L n = L := by
  rw [VaughanLogAverage.riesz, Finset.sum_eq_single 1]
  · simp [max_eq_right hL]
  · intro d hd hd1
    rw [max_eq_left (sub_nonpos.mpr (hrough d hd hd1)), mul_zero]
  · exact fun h => False.elim (h (Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩))

/-- A logarithmic difference is bounded by the relative additive gap,
using any positive lower bound on the denominator. -/
theorem log_sub_le_gap_div {x y M : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hM : 0 < M) (hMy : M ≤ y) : Real.log x - Real.log y ≤ |x - y| / M := by
  have he := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at he
  calc
    _ ≤ x / y - 1 := he
    _ = (x - y) / y := by field_simp
    _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy.le
    _ ≤ |x - y| / M := div_le_div_of_nonneg_left (abs_nonneg _) hM hMy

/-- Both orientations of the logarithmic gap obey the same explicit bound. -/
theorem abs_log_sub_le_gap_div {x y M : ℝ} (hM : 0 < M) (hMx : M ≤ x)
    (hMy : M ≤ y) : |Real.log x - Real.log y| ≤ |x - y| / M := by
  have hx : 0 < x := hM.trans_le hMx
  have hy : 0 < y := hM.trans_le hMy
  have hxy := log_sub_le_gap_div hx hy hM hMy
  have hyx := log_sub_le_gap_div hy hx hM hMx
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith only [hyx], hxy⟩

/-- The exact affine collision controls the distance from the limiting
logarithmic ratio, uniformly over the actual input labels. -/
theorem abs_log_ratio_deviation {b d x y h M : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hx : 0 < x) (hy : 0 < y)
    (hM : 0 < M) (hMx : M ≤ b * x) (hMy : M ≤ d * y)
    (he : b * x - d * y = h) :
    |(Real.log x - Real.log y) - Real.log (d / b)| ≤ |h| / M := by
  have hf : (Real.log x - Real.log y) - Real.log (d / b) =
      Real.log (b * x) - Real.log (d * y) := by
    rw [Real.log_div hd.ne' hb.ne', Real.log_mul hb.ne' hx.ne',
      Real.log_mul hd.ne' hy.ne']
    ring
  rw [hf]
  simpa only [he] using abs_log_sub_le_gap_div hM hMx hMy

/-- Subtraction of real phase angles retains exact complex conjugation. -/
theorem unitPhase_sub (u v : ℝ) :
    unitPhase (u - v) = unitPhase u * starRingEnd ℂ (unitPhase v) := by
  simp only [unitPhase, Complex.ofReal_sub, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  ring

/-- The original zeta filter separates its exact vertical phase from the
zero-height amplitude, for every polynomial filter. -/
theorem filterKernel_phase (P : Polynomial ℂ) (N : ℕ) (t x : ℝ) :
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) x =
      zetaPrimeFilterKernel P N (3 / 2) x * unitPhase (-t * Real.log x) := by
  simp only [zetaPrimeFilterKernel, unitPhase, mul_assoc, ← Complex.exp_add,
    Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  congr 1
  ring

/-- Demodulation of the literal original Riesz band preserves every
arithmetic coefficient, cutoff and complex polynomial filter. -/
theorem bandWeight_phase (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (n : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L P N t n =
      ZetaRieszConditionedEnergy.bandWeight L P N 0 n * unitPhase (-t * Real.log n) := by
  by_cases hb : n ∈ zetaPrimeLogBand N
  · simp only [ZetaRieszConditionedEnergy.bandWeight, hb, if_true, Complex.ofReal_zero,
      mul_zero, add_zero, filterKernel_phase, mul_assoc]
  · simp [ZetaRieszConditionedEnergy.bandWeight, hb]

/-- A pair of original bands has its full zero-height signed amplitude
times the literal logarithmic ratio phase. -/
theorem bandWeight_pair_phase (L : ℝ) (P : Polynomial ℂ) (N : ℕ)
    (t : ℝ) (x y : ℕ) :
    ZetaRieszConditionedEnergy.bandWeight L P N t x *
        starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N t y) =
      (ZetaRieszConditionedEnergy.bandWeight L P N 0 x *
        starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 y)) *
          unitPhase (-t * (Real.log x - Real.log y)) := by
  rw [bandWeight_phase L P N t x, bandWeight_phase L P N t y, map_mul]
  calc
    _ = (ZetaRieszConditionedEnergy.bandWeight L P N 0 x *
        starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 y)) *
          (unitPhase (-t * Real.log x) * starRingEnd ℂ (unitPhase (-t * Real.log y))) := by ring
    _ = _ := by
      rw [← unitPhase_sub]
      congr 1
      congr 1
      ring

/-- The original pair sum on any chosen finite set of input pairs. The set
can retain exact lag, size, prime and slow-phase restrictions together. -/
def bandPairSum (S : Finset (ℕ × ℕ)) (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) : ℂ :=
  ∑ z ∈ S, ZetaRieszConditionedEnergy.bandWeight L P N t z.1 *
    starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N t z.2)

/-- The finite original pair sum retains both signed divisor families in
each exact support cell, with no absolute-value replacement. -/
theorem bandPairSum_divisors (S : Finset (ℕ × ℕ)) (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (t : ℝ) :
    bandPairSum S L P N t =
      ∑ z ∈ S, ∑ r ∈ z.1.divisors, ∑ s ∈ z.2.divisors,
        (rieszDivisorWeight L r * starRingEnd ℂ (rieszDivisorWeight L s)) *
          (bandAmplitude L P N t z.1 * starRingEnd ℂ (bandAmplitude L P N t z.2)) := by
  unfold bandPairSum
  apply Finset.sum_congr rfl
  intro z hz
  exact bandWeight_pair_divisors L P N t z.1 z.2

/-- Freeze only the basic zeta phase of the original pair sum. Its complete
zero-height signed divisor aggregate remains as the main term. -/
theorem norm_bandPairSum_freeze_le (S : Finset (ℕ × ℕ)) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t α δ : ℝ)
    (hδ : ∀ z ∈ S, |(Real.log z.1 - Real.log z.2) - α| ≤ δ) :
    ‖bandPairSum S L P N t - unitPhase (-t * α) * bandPairSum S L P N 0‖ ≤
      (|t| * δ) * ∑ z ∈ S,
        ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.1‖ *
          ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.2‖ := by
  have he := norm_sum_phase_freeze_le_uniform S
    (fun z => ZetaRieszConditionedEnergy.bandWeight L P N 0 z.1 *
      starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 z.2))
    (fun z => -t * (Real.log z.1 - Real.log z.2)) (-t * α) (|t| * δ) (by
      intro z hz
      rw [show -t * (Real.log z.1 - Real.log z.2) - -t * α =
        -t * ((Real.log z.1 - Real.log z.2) - α) by ring, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hδ z hz) (abs_nonneg t))
  have hf : bandPairSum S L P N t =
      ∑ z ∈ S, (ZetaRieszConditionedEnergy.bandWeight L P N 0 z.1 *
        starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N 0 z.2)) *
          unitPhase (-t * (Real.log z.1 - Real.log z.2)) := by
    unfold bandPairSum
    apply Finset.sum_congr rfl
    intro z hz
    exact bandWeight_pair_phase L P N t z.1 z.2
  rw [hf]
  simpa only [bandPairSum, norm_mul, Complex.norm_conj] using he

/-- An actual affine lag and a lower bound on the two product labels give
an explicit phase-freezing error for the literal original Riesz pair sum. -/
theorem norm_bandPairSum_affine_freeze_le (S : Finset (ℕ × ℕ)) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t b d h M : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hM : 0 < M) (hS : ∀ z ∈ S,
      0 < z.1 ∧ 0 < z.2 ∧ M ≤ b * z.1 ∧ M ≤ d * z.2 ∧ b * z.1 - d * z.2 = h) :
    ‖bandPairSum S L P N t - unitPhase (-t * Real.log (d / b)) *
        bandPairSum S L P N 0‖ ≤
      (|t| * (|h| / M)) * ∑ z ∈ S,
        ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.1‖ *
          ‖ZetaRieszConditionedEnergy.bandWeight L P N 0 z.2‖ := by
  apply norm_bandPairSum_freeze_le
  intro z hz
  obtain ⟨hx, hy, hMx, hMy, he⟩ := hS z hz
  exact abs_log_ratio_deviation hb hd (by exact_mod_cast hx) (by exact_mod_cast hy)
    hM hMx hMy he

/-- Finite atom families have exactly the expected lag correlation, even
when labels coincide; no injectivity or support completion is assumed. -/
theorem correlation_single_sums {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (u : ι → ℂ) (v : κ → ℂ) (b d h : ℤ) :
    correlation b d (∑ i ∈ S, Finsupp.single (f i) (u i))
        (∑ j ∈ T, Finsupp.single (g j) (v j)) h =
      ∑ i ∈ S, ∑ j ∈ T,
        if b * f i - d * g j = h then u i * starRingEnd ℂ (v j) else 0 := by
  have hc := correlation_eq_pairing 0 b h d
    (∑ i ∈ S, Finsupp.single (f i) (u i)) (∑ j ∈ T, Finsupp.single (g j) (v j))
  simp only [sub_zero] at hc
  rw [hc]
  unfold pairing
  rw [observe_affine, observe_sum]
  simp only [observe_single, add_zero, affine, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, Finsupp.finsetSum_apply, Finsupp.single_apply,
    map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : b * f i - d * g j = h
  · have he' : d * g j + h = b * f i := by linarith only [he]
    simp [he, he']
  · have he' : ¬ d * g j + h = b * f i := by
      intro heq
      apply he
      linarith only [heq]
    simp [he, he']

/-- Every complete original Riesz lag equals the pair sum on its literal
positive band endpoint, with exactly the requested affine collision mask. -/
theorem correlation_riesz_eq_bandPairSum (b d h : ℤ) (L : ℝ)
    (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    correlation b d (rieszVector L P N t) (rieszVector L P N t) h =
      bandPairSum (((Finset.Icc 1 (2 ^ (32 * N))) ×ˢ
        (Finset.Icc 1 (2 ^ (32 * N)))).filter
          (fun z : ℕ × ℕ => b * (z.1 : ℤ) - d * (z.2 : ℤ) = h)) L P N t := by
  unfold rieszVector
  rw [correlation_single_sums]
  let F : ℕ → ℕ → ℂ := fun x y => if b * (x : ℤ) - d * (y : ℤ) = h then
    ZetaRieszConditionedEnergy.bandWeight L P N t x *
      starRingEnd ℂ (ZetaRieszConditionedEnergy.bandWeight L P N t y) else 0
  change (∑ i : Fin (2 ^ (32 * N)), ∑ j : Fin (2 ^ (32 * N)),
    F (i.val + 1) (j.val + 1)) = _
  have hj (x : ℕ) : (∑ j : Fin (2 ^ (32 * N)), F x (j.val + 1)) =
      ∑ y ∈ Finset.Icc 1 (2 ^ (32 * N)), F x y :=
    ZetaRieszConditionedEnergy.sum_positive_window _ (F x)
  simp_rw [hj]
  rw [ZetaRieszConditionedEnergy.sum_positive_window (2 ^ (32 * N))
    (fun x => ∑ y ∈ Finset.Icc 1 (2 ^ (32 * N)), F x y)]
  simp only [bandPairSum, Finset.sum_filter, Finset.sum_product, F]

end
end RiemannGaussian.ZetaArithmeticBandCorrelation
