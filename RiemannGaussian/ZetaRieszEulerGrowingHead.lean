/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerHead

/-!
# Explicit Euler budgets for every finite and growing head

All head Fourier families have an explicit positive Euler-product allowance. An elementary window bound lets the geometric source saving pay a linearly growing prime head along a positive integer stride. The estimates apply to the literal prime universe, physical cutoff and original factorial filter; the growing leading quotient remains unpaid.
-/

namespace RiemannGaussian.ZetaRieszEulerGrowingHead
noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter
open ZetaRieszEulerCutoff ZetaRieszEulerMoments ZetaRieszEulerCorrectionDeletion
open ZetaRieszEulerCorrectionEnergy
open ZetaRieszEulerMultiplier ZetaRieszEulerHead

/-- An explicit height-uniform Cauchy bound for each exact head Fourier
coefficient, expressed solely through its prime exponential weights. -/
def headCoefficientCeiling (S T : Finset ℕ) (sigma : ℝ) : ℝ :=
  (∏ p ∈ T, Real.exp (-sigma * Real.log p)) *
    ∏ p ∈ S \ T, (1 + Real.exp (-sigma * Real.log p))

/-- The explicit coefficient allowance is nonnegative for every real
half-plane parameter and every finite head subset. -/
theorem headCoefficientCeiling_nonneg (S T : Finset ℕ) (sigma : ℝ) :
    0 ≤ headCoefficientCeiling S T sigma := by
  unfold headCoefficientCeiling
  positivity

/-- The entire head coefficients have an explicit bound uniform over
the whole closed half-plane, independently of frequency and height. -/
theorem norm_headCoefficient_le (S T : Finset ℕ) {s : ℂ} {sigma : ℝ} (hs : sigma ≤ s.re) :
    ‖headCoefficient S T s‖ ≤ headCoefficientCeiling S T sigma := by
  have hb (p : ℕ) : ‖zetaPrimeFeature s p‖ ≤ Real.exp (-sigma * Real.log p) := by
    rw [norm_zetaPrimeFeature, zetaPrimeExpWeight]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hs) (Real.log_natCast_nonneg p))
  unfold headCoefficient headCoefficientCeiling
  simp only [norm_mul, norm_prod, norm_neg]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _hp => hb p)
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _hp =>
      (norm_add_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl (hb p)))
  · positivity
  · positivity

/-- The sum of all head coefficient allowances is an exact positive
Euler product, eliminating the need to search individual Fourier families. -/
theorem sum_headCoefficientCeiling (S : Finset ℕ) (sigma : ℝ) :
    (∑ T ∈ S.powerset, headCoefficientCeiling S T sigma) =
      ∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p)) := by
  unfold headCoefficientCeiling
  rw [← Finset.prod_add]
  exact Finset.prod_congr rfl (fun p _hp => by ring)

/-- A finite explicit arithmetic budget for the full head multiplier,
retaining the actual frequency of every subset and a literal prime tail. -/
def headResponseBudget (S : Finset ℕ) (sigma a : ℝ) (K : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, headCoefficientCeiling S T sigma * shiftBudget sigma a (headFrequency T) K

/-- Every finite head has a quantitative original-filter bound. The
entire head dependence is explicit, so growing heads can be audited against
the geometric source saving without postulating a complex circle bound. -/
theorem norm_scaled_headFilteredResponse_le (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p)
    {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) :
    ‖(u : ℂ) ^ (N + 1) * headFilteredResponse S Q P N s L‖ ≤
      (headResponseBudget S (s.re - R) a K * filterRadiusCost P R) *
        (((N : ℝ) + 1) * (u / R) ^ (N + 1)) := by
  rw [headFilteredResponse_eq_sum S Q h16 P N (show 1 / 2 < s.re by linarith), Finset.mul_sum]
  calc
    _ ≤ ∑ T ∈ S.powerset, ‖(u : ℂ) ^ (N + 1) *
        weightedFilteredResponse (headCoefficient S T) Q P N s (headFrequency T) L‖ := norm_sum_le _ _
    _ ≤ ∑ T ∈ S.powerset,
        (headCoefficientCeiling S T (s.re - R) * shiftBudget (s.re - R) a (headFrequency T) K *
          filterRadiusCost P R) * (((N : ℝ) + 1) * (u / R) ^ (N + 1)) := by
      apply Finset.sum_le_sum
      intro T _hT
      exact norm_scaled_weightedFilteredResponse_le _ (differentiable_headCoefficient S T)
        Q h16 P N hR hu hhalf (headCoefficientCeiling_nonneg S T (s.re - R))
        (fun z hz => norm_headCoefficient_le S T (disc_re_lower_bound (Metric.sphere_subset_closedBall hz)))
        K hK ha hL (headFrequency T)
    _ = _ := by simp only [headResponseBudget, Finset.sum_mul]

/-- The physical phase allowance increases with nonnegative cutoff
length, with all half-plane constants kept unchanged. -/
theorem phaseTailCost_mono_nonneg (sigma : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    phaseTailCost sigma x ≤ phaseTailCost sigma y := by
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  unfold phaseTailCost
  rw [abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]
  gcongr

/-- Every head subset has a nonnegative exact logarithmic frequency. -/
theorem headFrequency_nonneg (T : Finset ℕ) : 0 ≤ headFrequency T :=
  Finset.sum_nonneg (fun p _hp => Real.log_natCast_nonneg p)

/-- A head subset cannot exceed the full head's logarithmic frequency. -/
theorem headFrequency_mono {S T : Finset ℕ} (hTS : T ⊆ S) : headFrequency T ≤ headFrequency S :=
  Finset.sum_le_sum_of_subset_of_nonneg hTS (fun p _hp _hT => Real.log_natCast_nonneg p)

/-- The cost of every head Fourier family is bounded together by one
explicit positive Euler product and the full head's exact logarithmic extent. -/
theorem headResponseBudget_le_product (S : Finset ℕ) {sigma a : ℝ}
    (hsigma : 1 / 2 < sigma) (ha : 0 < a) (K : ℕ) :
    headResponseBudget S sigma a K ≤
      (∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p))) *
        shiftBudget sigma a (headFrequency S) K := by
  unfold headResponseBudget
  calc
    _ ≤ ∑ T ∈ S.powerset,
        headCoefficientCeiling S T sigma * shiftBudget sigma a (headFrequency S) K := by
      apply Finset.sum_le_sum
      intro T hT
      apply mul_le_mul_of_nonneg_left _ (headCoefficientCeiling_nonneg S T sigma)
      unfold shiftBudget
      apply mul_le_mul_of_nonneg_right _ (ZetaPrimeNonlinearTail.squareLogTail_nonneg hsigma K)
      apply div_le_div_of_nonneg_right _ ha.le
      rw [abs_of_nonneg (headFrequency_nonneg T), abs_of_nonneg (headFrequency_nonneg S)]
      exact phaseTailCost_mono_nonneg sigma (add_nonneg ha.le (headFrequency_nonneg T))
        (add_le_add le_rfl (headFrequency_mono (Finset.mem_powerset.mp hT)))
    _ = _ := by rw [← Finset.sum_mul, sum_headCoefficientCeiling]

/-- A closed arithmetic bound for the full head-filtered correction:
only a positive finite Euler product and the head's total log frequency
multiply the geometric source saving. It applies to every finite head. -/
theorem norm_scaled_headFilteredResponse_le_product (S Q : Finset ℕ) (h16 : ∀ p ∈ Q, 16 ≤ p)
    (P : Polynomial ℂ) (N : ℕ) {s : ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u)
    (hhalf : 1 / 2 < s.re - R) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p)
    {a L : ℝ} (ha : 0 < a) (hL : a ≤ L) :
    ‖(u : ℂ) ^ (N + 1) * headFilteredResponse S Q P N s L‖ ≤
      ((∏ p ∈ S, (1 + 2 * Real.exp (-(s.re - R) * Real.log p))) *
        shiftBudget (s.re - R) a (headFrequency S) K * filterRadiusCost P R) *
          (((N : ℝ) + 1) * (u / R) ^ (N + 1)) := by
  apply (norm_scaled_headFilteredResponse_le S Q h16 P N hR hu hhalf K hK ha hL).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (headResponseBudget_le_product S hhalf ha K)
      (by unfold filterRadiusCost; positivity))
  positivity

/-- The fixed-shift budget grows at most linearly in the nonnegative
logarithmic extent of a head, uniformly over the original physical cutoff. -/
theorem shiftBudget_le_linear {sigma a delta : ℝ} (hsigma : 1 / 2 < sigma)
    (ha : 0 < a) (hdelta : 0 ≤ delta) (K : ℕ) :
    shiftBudget sigma a delta K ≤ shiftBudget sigma a 1 K * (1 + delta) := by
  let B : ℝ := (32 + 64 * massCeiling sigma * (2 + Real.exp (8 * massCeiling sigma)) +
    4 * (2 + Real.exp (8 * massCeiling sigma))) * (Real.pi / 2)
  let D : ℝ := 4 * Real.pi * (2 + Real.exp (8 * massCeiling sigma)) / Real.log 16
  have hM : 0 ≤ massCeiling sigma := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he (x : ℝ) : phaseTailCost sigma x = B + D * |x| := by
    unfold phaseTailCost
    dsimp [B, D]
    ring
  have hp : phaseTailCost sigma (a + delta) ≤ phaseTailCost sigma (a + 1) * (1 + delta) := by
    rw [he, he, abs_of_nonneg (add_nonneg ha.le hdelta), abs_of_pos (by positivity : 0 < a + 1)]
    nlinarith [mul_nonneg hB hdelta, mul_nonneg (mul_nonneg hD ha.le) hdelta]
  unfold shiftBudget
  rw [abs_of_nonneg hdelta, abs_one]
  calc
    _ ≤ (phaseTailCost sigma (a + 1) * (1 + delta) / a) *
        ZetaPrimeNonlinearTail.squareLogTail sigma K :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp ha.le)
        (ZetaPrimeNonlinearTail.squareLogTail_nonneg hsigma K)
    _ = _ := by ring

/-- The full coefficient Euler product costs at most three per head
element on every nonnegative half-plane; no prime-density estimate is needed. -/
theorem head_product_le_three_pow_card (S : Finset ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    (∏ p ∈ S, (1 + 2 * Real.exp (-sigma * Real.log p))) ≤ (3 : ℝ) ^ S.card := by
  calc
    _ ≤ ∏ _p ∈ S, (3 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _hp
      have hp : Real.exp (-sigma * Real.log p) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsigma)
          (Real.log_natCast_nonneg p))
      linarith
    _ = _ := by simp

/-- A head contained in a natural-number window has an elementary
quadratic log-frequency bound, uniform over every subset of that window. -/
theorem headFrequency_le_window (S : Finset ℕ) (b : ℕ) (hS : S ⊆ Finset.range (b + 1)) :
    headFrequency S ≤ ((b : ℝ) + 1) ^ 2 := by
  have hc : S.card ≤ b + 1 := by simpa using Finset.card_le_card hS
  calc
    headFrequency S ≤ ∑ _p ∈ S, (b : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' : p ≤ b := by have := Finset.mem_range.mp (hS hp); omega
      exact (Real.log_le_self (by positivity : (0 : ℝ) ≤ p)).trans (by exact_mod_cast hp')
    _ = (S.card : ℝ) * b := by simp
    _ ≤ ((b : ℝ) + 1) * b := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ b by positivity]

/-- The head contribution has an explicit bound depending only on its
window, even when that window grows. Every coefficient family is covered. -/
theorem headResponseBudget_le_window (S : Finset ℕ) (b : ℕ) (hS : S ⊆ Finset.range (b + 1))
    {sigma a : ℝ} (hsigma : 1 / 2 < sigma) (ha : 0 < a) (K : ℕ) :
    headResponseBudget S sigma a K ≤
      (3 : ℝ) ^ (b + 1) * (shiftBudget sigma a 1 K * (1 + ((b : ℝ) + 1) ^ 2)) := by
  apply (headResponseBudget_le_product S hsigma ha K).trans
  apply mul_le_mul
  · apply (head_product_le_three_pow_card S (by linarith)).trans
    exact pow_le_pow_right₀ (by norm_num) (by simpa using Finset.card_le_card hS)
  · apply (shiftBudget_le_linear hsigma ha (headFrequency_nonneg S) K).trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (headFrequency_le_window S b hS))
      (shiftBudget_nonneg hsigma ha 1 K)
  · exact shiftBudget_nonneg hsigma ha _ K
  · positivity

/-- Every strict geometric saving admits a positive integer stride
which pays even the coarse factor of three per additional head element. -/
theorem exists_head_stride {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ d : ℕ, 0 < d ∧ 3 * r ^ d < 1 := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have he : ∀ᶠ d : ℕ in atTop, r ^ d < 1 / 3 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  obtain ⟨d, hd, hd0⟩ := (he.and (eventually_gt_atTop 0)).exists
  exact ⟨d, hd0, by linarith⟩

/-- The elementary growing-window allowance decays along every stride
whose geometric saving pays its exponential head cost. The remaining
frequency and factorial factors form only a cubic polynomial. -/
theorem tendsto_window_geometric (d c : ℕ) {r : ℝ} (hr : 0 ≤ r) (hd : 3 * r ^ d < 1) :
    Tendsto (fun n : ℕ => (3 : ℝ) ^ (n + c + 1) * (1 + ((n + c : ℕ) + 1 : ℝ) ^ 2) *
      (((d * n : ℕ) : ℝ) + 1) * r ^ (d * n + 1)) atTop (nhds 0) := by
  let b : ℝ := 3 * r ^ d
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b < 1 := hd
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hb hb1
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hb hb1
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hb hb1
  have h3 := tendsto_pow_const_mul_const_pow_of_lt_one 3 hb hb1
  let C : ℝ := (c : ℝ) + 1
  have ht := (((h3.const_mul (d : ℝ)).add
    (h2.const_mul (1 + 2 * d * C))).add
    (h1.const_mul (2 * C + d * (C ^ 2 + 1)))).add (h0.const_mul (C ^ 2 + 1))
  have ht' : Tendsto (fun n : ℕ => ((3 : ℝ) ^ (c + 1) * r) *
      ((d : ℝ) * ((n : ℝ) ^ 3 * b ^ n) + (1 + 2 * d * C) * ((n : ℝ) ^ 2 * b ^ n) +
        (2 * C + d * (C ^ 2 + 1)) * ((n : ℝ) ^ 1 * b ^ n) + (C ^ 2 + 1) * b ^ n))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using ht.const_mul ((3 : ℝ) ^ (c + 1) * r)
  apply ht'.congr'
  filter_upwards [] with n
  have hthree : (3 : ℝ) ^ (n + c + 1) = 3 ^ (c + 1) * 3 ^ n := by
    rw [show n + c + 1 = c + 1 + n by omega, pow_add]
  have hrpow : r ^ (d * n + 1) = r * (r ^ d) ^ n := by rw [pow_succ, pow_mul]; ring
  dsimp [C, b]
  rw [hthree, hrpow, mul_pow]
  push_cast
  ring

/-- Every family of heads inside a linearly growing prime window has
source-scale decay along a sufficiently strong stride, uniformly over all
head subsets, all large-prime selections and unbounded physical lengths. -/
theorem tendsto_window_headFilteredResponse (d c : ℕ) (S Q : ℕ → Finset ℕ)
    (hS : ∀ n, S n ⊆ Finset.range (n + c + 1)) (h16 : ∀ n p, p ∈ Q n → 16 ≤ p)
    (P : Polynomial ℂ) (L : ℕ → ℝ) {a : ℝ} (ha : 0 < a) (hL : ∀ n, a ≤ L n)
    {s : ℂ} {R u : ℝ} (hR : 0 < R) (hu : 0 ≤ u) (hhalf : 1 / 2 < s.re - R)
    (hd : 3 * (u / R) ^ d < 1) :
    Tendsto (fun n : ℕ => (u : ℂ) ^ (d * n + 1) *
      headFilteredResponse (S n) (Q n) P (d * n) s (L n)) atTop (nhds 0) := by
  let C : ℝ := shiftBudget (s.re - R) a 1 0 * filterRadiusCost P R
  have hC : 0 ≤ C := mul_nonneg (shiftBudget_nonneg hhalf ha 1 0)
    (by unfold filterRadiusCost; positivity)
  have hb (n : ℕ) : ‖(u : ℂ) ^ (d * n + 1) *
      headFilteredResponse (S n) (Q n) P (d * n) s (L n)‖ ≤
      C * ((3 : ℝ) ^ (n + c + 1) * (1 + ((n + c : ℕ) + 1 : ℝ) ^ 2) *
        (((d * n : ℕ) : ℝ) + 1) * (u / R) ^ (d * n + 1)) := by
    apply (norm_scaled_headFilteredResponse_le (S n) (Q n) (h16 n) P (d * n)
      hR hu hhalf 0 (fun _ _ => Nat.zero_le _) ha (hL n)).trans
    calc
      _ ≤ ((3 : ℝ) ^ (n + c + 1) *
          (shiftBudget (s.re - R) a 1 0 * (1 + ((n + c : ℕ) + 1 : ℝ) ^ 2)) *
            filterRadiusCost P R) * ((((d * n : ℕ) : ℝ) + 1) * (u / R) ^ (d * n + 1)) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (headResponseBudget_le_window (S n) (n + c) (hS n) hhalf ha 0)
            (by unfold filterRadiusCost; positivity))
        positivity
      _ = _ := by dsimp [C]; ring
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using
    (tendsto_window_geometric d c (div_nonneg hu hR.le) hd).const_mul C

/-- The head below an arbitrary threshold in the literal original
primorial prime universe; its membership is never approximated. -/
def actualWindowHead (N b : ℕ) : Finset ℕ :=
  (primorial (2 ^ (32 * N))).primeFactors.filter (fun p => p ≤ b)

/-- The complementary tail in the same literal prime universe. -/
def actualWindowTail (N b : ℕ) : Finset ℕ :=
  (primorial (2 ^ (32 * N))).primeFactors.filter (fun p => b < p)

/-- At every source scale below one, an entire linearly growing head
of the actual prime universe can multiply the full complementary correction
with decaying error along a cofinal stride of original factorial orders. -/
theorem exists_stride_actual_window_correction_decay (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∃ d : ℕ, 0 < d ∧ Tendsto (fun n : ℕ => (u : ℂ) ^ (d * n + 1) *
      headFilteredResponse (actualWindowHead (d * n) (n + 16)) (actualWindowTail (d * n) (n + 16))
        P (d * n) (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u (d * n)))
      atTop (nhds 0) := by
  let R : ℝ := (u + 1) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have huR : u < R := by dsimp [R]; linarith
  obtain ⟨d, hd0, hd⟩ := exists_head_stride (div_nonneg hu.le hR.le) ((div_lt_one hR).mpr huR)
  refine ⟨d, hd0, ?_⟩
  apply tendsto_window_headFilteredResponse d 16
    (fun n => actualWindowHead (d * n) (n + 16))
    (fun n => actualWindowTail (d * n) (n + 16))
    (fun _ _ hp => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2))
    (fun _ _ hp => by have := (Finset.mem_filter.mp hp).2; omega)
    P (fun n => SquarefreeVaughanLogSource.length u (d * n))
    (Real.log_pos (by norm_num : (1 : ℝ) < 4))
    (fun n => ZetaRieszFixedCofactor.length_ge_log_four u (d * n)) hR hu.le _ hd
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  rw [hs]
  dsimp [R]
  linarith

end
end RiemannGaussian.ZetaRieszEulerGrowingHead
