/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellation
import RiemannGaussian.SuzukiLocalCancellationBoundary
import RiemannGaussian.SuzukiLaplaceCompensator
import RiemannGaussian.SuzukiBalancedCells
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Inverting the local Suzuki cancellation

Exact finite recurrence identities and their one-sided transfer. The
normalized boundary condition is retained explicitly: it removes the
homogeneous growing mode and cannot follow from the local forcing bound.
-/

set_option warningAsError true

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

/-- Finite inversion retains the entire terminal boundary value. -/
theorem localCancellation_finite_inversion (u g : ℕ → ℝ) {c : ℝ}
    (hc : c ≠ 0) (hrec : ∀ n, u (n + 1) = c * u n + g n) (r : ℕ) :
    u 0 = (c⁻¹) ^ r * u r -
      ∑ j ∈ Finset.range r, (c⁻¹) ^ (j + 1) * g j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, pow_succ, hrec r]
    calc
      u 0 = c⁻¹ ^ r * u r - ∑ j ∈ Finset.range r, c⁻¹ ^ (j + 1) * g j := ih
      _ = _ := by field_simp [hc]; ring

/-- First differences are the initial slope plus the full finite curvature. -/
theorem localCancellation_first_difference (s : ℕ → ℝ) (n : ℕ) :
    s (n + 1) - s n = s 1 - s 0 +
      ∑ j ∈ Finset.range n, (s (j + 2) - 2 * s (j + 1) + s j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : n + 1 + 1 = n + 2 := by omega
    rw [hn]
    linarith

/-- Exact second-difference reconstruction. The last summand has coefficient
zero, so this is the usual triangular sum through `n - 2`, including `n=0,1`. -/
theorem localCancellation_second_difference_reconstruction (s : ℕ → ℝ) (n : ℕ) :
    s n = s 0 + (n : ℝ) * (s 1 - s 0) +
      ∑ j ∈ Finset.range n, ((n : ℝ) - 1 - j) *
        (s (j + 2) - 2 * s (j + 1) + s j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    have heq : (∑ j ∈ Finset.range n, ((n : ℝ) + 1 - 1 - j) *
        (s (j + 2) - 2 * s (j + 1) + s j)) =
        (∑ j ∈ Finset.range n, ((n : ℝ) - 1 - j) *
          (s (j + 2) - 2 * s (j + 1) + s j)) +
        ∑ j ∈ Finset.range n, (s (j + 2) - 2 * s (j + 1) + s j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    have hd := localCancellation_first_difference s n
    linarith

/-- A lower forcing bound yields an upper bound on the initial value, using
only the vanishing normalized terminal boundary. No infinite forcing sum
or absolute convergence hypothesis is introduced. -/
theorem localCancellation_upper_of_boundary (u : ℕ → ℝ) {c a C : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hac : a < c)
    (hrec : ∀ n, -(C * a ^ n) ≤ u (n + 1) - c * u n)
    (hboundary : Tendsto (fun n => (c⁻¹) ^ n * u n) atTop (𝓝 0)) :
    u 0 ≤ C / (c - a) := by
  let D := C / (c - a)
  have hD : D * (c - a) = C := by
    dsimp [D]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hac.ne')
  have hstep : ∀ n, c * (u n - D * a ^ n) ≤ u (n + 1) - D * a ^ (n + 1) := by
    intro n
    have hh := hrec n
    rw [pow_succ]
    nlinarith [congrArg (fun x : ℝ => x * a ^ n) hD]
  have hinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc.ne'
  have hmono : ∀ n, u 0 - D ≤ (c⁻¹) ^ n * (u n - D * a ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := mul_le_mul_of_nonneg_left (hstep n)
        (pow_nonneg (inv_nonneg.mpr hc.le) (n + 1))
      have hmul : (c⁻¹) ^ (n + 1) * c = (c⁻¹) ^ n := by
        rw [pow_succ]
        calc c⁻¹ ^ n * c⁻¹ * c = c⁻¹ ^ n * (c⁻¹ * c) := by ring
             _ = _ := by rw [hinv, mul_one]
      rw [← mul_assoc, hmul] at hh
      exact ih.trans hh
  have hq : Tendsto (fun n : ℕ => (a / c) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hc.le)
      ((div_lt_one hc).mpr hac)
  have hlim : Tendsto (fun n => (c⁻¹) ^ n * (u n - D * a ^ n)) atTop (𝓝 0) := by
    convert hboundary.sub (hq.const_mul D) using 1
    · funext n
      rw [mul_sub, div_pow, div_eq_mul_inv, inv_pow]
      ring
    · simp
  have h := ge_of_tendsto hlim (Filter.Eventually.of_forall hmono)
  dsimp [D] at h
  linarith

/-- A concave sequence with nonpositive initial slope never exceeds its
initial value. -/
theorem localCancellation_concave_upper (s : ℕ → ℝ)
    (hfirst : s 1 ≤ s 0)
    (hsecond : ∀ n, s (n + 2) - 2 * s (n + 1) + s n ≤ 0) (n : ℕ) :
    s n ≤ s 0 := by
  have hd : ∀ k, s (k + 1) ≤ s k := by
    intro k
    induction k with
    | zero => simpa using hfirst
    | succ k ih =>
      have hh := hsecond k
      have heq : k + 1 + 1 = k + 2 := by omega
      rw [heq]
      linarith
  induction n with
  | zero => rfl
  | succ n ih => exact (hd n).trans ih

/-- Uniform bounds at the first two points and an exponential curvature
upper bound yield an exponential upper bound at every lattice point. -/
theorem localCancellation_sequence_exp_upper (s : ℕ → ℝ) {a B D : ℝ}
    (ha : 1 < a) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hzero : |s 0| ≤ B) (hone : |s 1| ≤ B)
    (hsecond : ∀ n, s (n + 2) - 2 * s (n + 1) + s n ≤ D * a ^ n) :
    ∀ n, s n ≤ (B + (D / (a - 1) ^ 2 + 2 * B / (a - 1))) * a ^ n := by
  let L := D / (a - 1) ^ 2 + 2 * B / (a - 1)
  have ha0 : 0 < a - 1 := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hL1 : 2 * B ≤ L * (a - 1) := by
    dsimp [L]
    have he : 2 * B / (a - 1) * (a - 1) = 2 * B := div_mul_cancel₀ _ ha0.ne'
    have hn : 0 ≤ D / (a - 1) ^ 2 * (a - 1) := by positivity
    nlinarith
  have hL2 : D ≤ L * (a - 1) ^ 2 := by
    dsimp [L]
    have he : D / (a - 1) ^ 2 * (a - 1) ^ 2 = D :=
      div_mul_cancel₀ _ (pow_ne_zero _ ha0.ne')
    have hn : 0 ≤ 2 * B / (a - 1) * (a - 1) ^ 2 := by positivity
    nlinarith
  let q : ℕ → ℝ := fun n => s n - L * a ^ n
  have hqfirst : q 1 ≤ q 0 := by
    dsimp [q]
    simp only [pow_one, pow_zero, mul_one]
    linarith [(abs_le.mp hzero).1, (abs_le.mp hone).2]
  have hqsecond : ∀ n, q (n + 2) - 2 * q (n + 1) + q n ≤ 0 := by
    intro n
    have hh := hsecond n
    have hp := mul_le_mul_of_nonneg_right hL2 (pow_nonneg (by linarith : 0 ≤ a) n)
    dsimp [q]
    simp only [pow_succ]
    nlinarith
  intro n
  change s n ≤ (B + L) * a ^ n
  have hh := localCancellation_concave_upper q hqfirst hqsecond n
  have hn : 1 ≤ a ^ n := one_le_pow₀ ha.le
  have hBn := mul_le_mul_of_nonneg_left hn hB
  dsimp [q] at hh
  simp only [pow_zero, mul_one] at hh
  nlinarith [(abs_le.mp hzero).2]

/-- A single uniform lattice constant works for every point of a compact
base interval. This handles real cutoffs, rather than just one orbit. -/
theorem localCancellation_real_exp_upper (f : ℝ → ℝ) {h T ε B D : ℝ}
    (hh : 0 < h) (hT : 0 ≤ T) (hε : 0 < ε) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbase : ∀ r ∈ Icc T (T + 2 * h), |f r| ≤ B)
    (hsecond : ∀ t, T ≤ t →
      f (t + 2 * h) - 2 * f (t + h) + f t ≤ D * Real.exp (ε * t)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, T ≤ t → f t ≤ K * Real.exp (ε * t) := by
  let a := Real.exp (ε * h)
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos hε hh)
  let E := D * Real.exp (ε * (T + h))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let L := E / (a - 1) ^ 2 + 2 * B / (a - 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨B + L, by positivity, fun t ht => ?_⟩
  let n := ⌊(t - T) / h⌋₊
  let r := t - n * h
  have htT : 0 ≤ (t - T) / h := div_nonneg (sub_nonneg.mpr ht) hh.le
  have hnle : (n : ℝ) ≤ (t - T) / h := Nat.floor_le htT
  have hnlt : (t - T) / h < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hr : T ≤ r := by dsimp [r]; nlinarith [(le_div_iff₀ hh).mp hnle]
  have hrh : r < T + h := by dsimp [r]; nlinarith [(div_lt_iff₀ hh).mp hnlt]
  let s : ℕ → ℝ := fun k => f (r + k * h)
  have hzero : |s 0| ≤ B := by
    dsimp [s]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact hbase r ⟨hr, by linarith⟩
  have hone : |s 1| ≤ B := by
    dsimp [s]
    simp only [Nat.cast_one, one_mul]
    exact hbase (r + h) ⟨by linarith, by linarith⟩
  have hseq : ∀ k, s (k + 2) - 2 * s (k + 1) + s k ≤ E * a ^ k := by
    intro k
    have hrk : T ≤ r + k * h := hr.trans (le_add_of_nonneg_right (by positivity))
    have hh2 := hsecond (r + k * h) hrk
    have hid : Real.exp (ε * (r + k * h)) = Real.exp (ε * r) * a ^ k := by
      dsimp [a]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hem : Real.exp (ε * r) ≤ Real.exp (ε * (T + h)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrh.le hε.le)
    have hmajor := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hem hD) (pow_nonneg (le_trans zero_le_one ha.le) k)
    dsimp [s]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [show r + ((k : ℝ) + 2) * h = r + k * h + 2 * h by ring,
      show r + ((k : ℝ) + 1) * h = r + k * h + h by ring]
    apply hh2.trans
    rw [hid]
    dsimp [E]
    nlinarith [hmajor]
  have hseqbound : ∀ k, s k ≤ (B + L) * a ^ k :=
    localCancellation_sequence_exp_upper s ha hB hE hzero hone hseq
  have hnexp : a ^ n ≤ Real.exp (ε * t) := by
    dsimp [a]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hr0 : 0 ≤ r := hT.trans hr
    dsimp [r] at hr0
    nlinarith
  have hsn : s n = f t := by dsimp [s, r]; congr 1; ring
  rw [← hsn]
  exact (hseqbound n).trans (mul_le_mul_of_nonneg_left hnexp (by positivity))

/-- Continuity of the full prime hinge signal gives uniform compact bounds,
including prime-power entry points. -/
theorem suzukiLocalSignal_compact_bound {T V : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc T V,
      |suzukiChebyshevLogAverageLaplaceSignal t| ≤ B := by
  let f : ℝ → ℝ := fun t => suzukiLegendreSignal t -
    suzukiArchimedeanSlopeConstant * t - suzukiArchimedeanIntercept
  have hf : Continuous f := by
    dsimp [f]
    exact (continuous_suzukiLegendreSignal.sub (continuous_const.mul continuous_id)).sub
      continuous_const
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hf.abs.continuousOn
  refine ⟨|B|, abs_nonneg B, fun t ht => ?_⟩
  have hh : |f t| ≤ B := hB (mem_image_of_mem _ ht)
  have he : f t = suzukiChebyshevLogAverageLaplaceSignal t := by
    dsimp [f]
    rw [suzukiLegendreSignal_eq_laplace_add_affine (hT.trans ht.1)]
    ring
  rw [he] at hh
  exact hh.trans (le_abs_self B)

/-- The one-sided prime comparison controls the full second difference.
The normalized boundary remains an explicit independent premise. -/
theorem suzukiLocalSecondDifference_upper_of_comparison_lower
    {T ε C : ℝ} (hT : 0 ≤ T) (hεhalf : ε < 1 / 2)
    (hC : 0 ≤ C)
    (hg : ∀ t, T ≤ t → -(C * Real.exp (ε * t)) ≤ suzukiLocalPrimeComparison t)
    (hboundary : ∀ t, T ≤ t → Tendsto
      (fun n : ℕ => (Real.sqrt 2)⁻¹ ^ n *
        suzukiLocalSecondDifference (t + n * Real.log 2)) atTop (𝓝 0)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, T ≤ t →
      suzukiLocalSecondDifference t ≤ D * Real.exp (ε * t) := by
  let a := Real.exp (ε * Real.log 2)
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hac : a < Real.sqrt 2 := by
    have he : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
      rw [Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [← he]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hden : 0 < Real.sqrt 2 - a := sub_pos.mpr hac
  refine ⟨C / (Real.sqrt 2 - a), div_nonneg hC hden.le, fun t ht => ?_⟩
  let u : ℕ → ℝ := fun n => suzukiLocalSecondDifference (t + n * Real.log 2)
  have hrec : ∀ n, -((C * Real.exp (ε * t)) * a ^ n) ≤
      u (n + 1) - Real.sqrt 2 * u n := by
    intro n
    have htn : T ≤ t + n * Real.log 2 :=
      ht.trans (le_add_of_nonneg_right (by positivity))
    have hgg := hg (t + n * Real.log 2) htn
    rw [suzukiLocalPrimeComparison_eq_shift_second_difference (hT.trans htn)] at hgg
    have he : Real.exp (ε * (t + n * Real.log 2)) = Real.exp (ε * t) * a ^ n := by
      dsimp [a]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [he] at hgg
    simpa only [u, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, mul_assoc]
      using hgg
  have hu := localCancellation_upper_of_boundary u hc (Real.exp_nonneg _) hac hrec
    (hboundary t ht)
  dsimp [u] at hu
  simp only [Nat.cast_zero, zero_mul, add_zero] at hu
  convert hu using 1
  ring

/-- The complete proposed transfer, retaining precisely the asymptotic
boundary needed to invert the recurrence. The arithmetic lower bound is
an assumption; this theorem does not establish it. -/
theorem riemannHypothesis_of_suzukiLocalComparison_lower_and_boundary
    (hboundary : ∀ t : ℝ, 0 ≤ t → Tendsto
      (fun n : ℕ => (Real.sqrt 2)⁻¹ ^ n *
        suzukiLocalSecondDifference (t + n * Real.log 2)) atTop (𝓝 0))
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t : ℝ in atTop, -(C * Real.exp (ε * t)) ≤ suzukiLocalPrimeComparison t) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound
    (a := -1) (by norm_num)
  intro ε hε
  let δ := min ε (1 / 4)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C, hC, hlate⟩ := hg δ hδ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hlate
  let T := max T₀ 0
  have hT : 0 ≤ T := le_max_right _ _
  obtain ⟨D, hD, hU⟩ := suzukiLocalSecondDifference_upper_of_comparison_lower hT
    hδhalf hC (fun t ht => hT₀ t ((le_max_left _ _).trans ht))
    (fun t ht => hboundary t (hT.trans ht))
  obtain ⟨B, hB, hbase⟩ := suzukiLocalSignal_compact_bound (V := T + 2 * Real.log 2) hT
  obtain ⟨K, hK, hKbound⟩ := localCancellation_real_exp_upper
    suzukiChebyshevLogAverageLaplaceSignal (Real.log_pos (by norm_num)) hT hδ hB hD hbase
    (fun t ht => by simpa only [suzukiLocalSecondDifference] using hU t ht)
  obtain ⟨B₀, hB₀, hhead⟩ := suzukiLocalSignal_compact_bound (T := 0) (V := T) le_rfl
  refine ⟨K + B₀, by positivity, fun t ht => ?_⟩
  have hexp : 1 ≤ Real.exp (ε * t) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hε.le ht.le)
  have hmain : suzukiChebyshevLogAverageLaplaceSignal t ≤
      (K + B₀) * Real.exp (ε * t) := by
    by_cases htT : T ≤ t
    · have he : Real.exp (δ * t) ≤ Real.exp (ε * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hδε ht.le)
      have hk := (hKbound t htT).trans (mul_le_mul_of_nonneg_left he hK)
      nlinarith [mul_nonneg hB₀ (Real.exp_pos (ε * t)).le]
    · have hb := (abs_le.mp (hhead t ⟨ht.le, (le_of_not_ge htT)⟩)).2
      have hbexp := mul_le_mul_of_nonneg_left hexp hB₀
      nlinarith [mul_nonneg hK (Real.exp_pos (ε * t)).le]
  linarith

/-- The log-time arithmetic criterion after discharging the homogeneous
boundary unconditionally by the prime number theorem. -/
theorem riemannHypothesis_of_suzukiLocalComparison_eventually_subexponential_lower_bound
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t : ℝ in atTop, -(C * Real.exp (ε * t)) ≤ suzukiLocalPrimeComparison t) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_suzukiLocalComparison_lower_and_boundary
    (fun t _ => suzukiLocalSecondDifference_lattice_boundary t) hg

/-- The precise real-cutoff target of the research note implies Mathlib's
literal Riemann hypothesis. All actual prime powers remain in the fixed
signed comparison; only the stated arithmetic estimate is unproved. -/
theorem riemannHypothesis_of_suzukiLocalArithmeticComparison_subpolynomial_lower_bound
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → -(C * X ^ ε) ≤ suzukiLocalArithmeticComparison X) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiLocalComparison_eventually_subexponential_lower_bound
  intro ε hε
  obtain ⟨C, hC, X₀, _, hbound⟩ := hg ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop X₀)] with t ht
  have hh := hbound (Real.exp t) ht
  rw [suzukiLocalArithmeticComparison_exp,
    Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp] at hh
  simpa only [mul_comm t ε] using hh

/-- The finite triangular geometric sum, including its zero endpoint and
all small lengths. -/
theorem localCancellation_triangular_geometric_sum {a : ℝ} (ha : a ≠ 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n - 1 - j : ℕ) : ℝ) * a ^ j) =
      (a ^ n - (n : ℝ) * a + n - 1) / (a - 1) ^ 2 := by
  have hrec := localCancellation_second_difference_reconstruction (fun k => a ^ k) n
  have hcurv : ∀ j : ℕ, a ^ (j + 2) - 2 * a ^ (j + 1) + a ^ j =
      a ^ j * (a - 1) ^ 2 := by
    intro j
    simp only [pow_succ]
    ring
  simp only [pow_zero, pow_one] at hrec
  simp_rw [hcurv] at hrec
  have hcoeff : ∀ j ∈ Finset.range n,
      ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    have hn : 1 ≤ n := by omega
    rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub hn, Nat.cast_one]
  have hsum : (∑ j ∈ Finset.range n, ((n - 1 - j : ℕ) : ℝ) * a ^ j) * (a - 1) ^ 2 =
      ∑ j ∈ Finset.range n, ((n : ℝ) - 1 - j) * (a ^ j * (a - 1) ^ 2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff j hj]
    ring
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr ha))).mpr
  rw [hsum]
  linarith

/-- The triangular geometric sum is bounded by its last exponential scale. -/
theorem localCancellation_triangular_geometric_sum_le {a : ℝ} (ha : 1 < a) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n - 1 - j : ℕ) : ℝ) * a ^ j) ≤
      a ^ n / (a - 1) ^ 2 := by
  rw [localCancellation_triangular_geometric_sum ha.ne']
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hnonneg : 0 ≤ (n : ℝ) * (a - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

end
end RiemannGaussian
