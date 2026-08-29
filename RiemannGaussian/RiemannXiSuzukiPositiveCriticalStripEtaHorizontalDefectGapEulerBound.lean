import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapEuler
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Sharp first-order control of the arithmetic eta-gap tail

This module turns the exact Euler decomposition into a quantitative
asymptotic.  A fundamental-theorem-of-calculus representation and a
mean-value estimate show that every consecutive second difference of
`x ^ (-s)` gains one endpoint power.  An explicit integral-test estimate then
sums those bounds uniformly from every finite cutoff.

At a nontrivial zeta zero `rho`, Lean consequently proves that the finite gap
error has leading term `-(2N+1)^(-rho) / 2`, with an error bounded by a fixed
multiple of `(2N+1)^(-rho.re-1)`.  The functional-equation partner has the
same expansion at the complementary real exponent.  These compatible sharp
asymptotics are a diagnostic interface, not a contradiction or a proof of a
zero-location theorem.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A one-step complex power difference is controlled by the derivative at
the left endpoint when the real exponent is at most one. -/
lemma norm_cpow_add_one_sub_le
    (r : ℂ) {x : ℝ} (hx : 0 < x) (hre : r.re ≤ 1) :
    ‖(((x + 1 : ℝ) : ℂ) ^ r) - (((x : ℝ) : ℂ) ^ r)‖ ≤
      ‖r‖ * x ^ (r.re - 1) := by
  have hle : x ≤ x + 1 := by linarith
  have hderiv (y : ℝ) (hy : y ∈ Icc x (x + 1)) :
      HasDerivWithinAt (fun u : ℝ => ((u : ℂ) ^ r))
        (r * ((y : ℂ) ^ (r - 1))) (Icc x (x + 1)) y := by
    by_cases hr : r = 0
    · subst r
      simpa using (hasDerivAt_const (x := y) (c := (1 : ℂ))).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const
        (show y ≠ 0 by linarith [hy.1]) hr).hasDerivWithinAt
  have hbound (y : ℝ) (hy : y ∈ Ico x (x + 1)) :
      ‖r * ((y : ℂ) ^ (r - 1))‖ ≤ ‖r‖ * x ^ (r.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hy.1])]
    simp only [sub_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx hy.1 (by linarith))
      (norm_nonneg r)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    (x + 1) (right_mem_Icc.mpr hle)
  simpa using h

/-- A positive-real-axis complex power difference is its derivative integral. -/
lemma cpow_sub_add_one_eq_mul_integral
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (-s)) - (((x + 1 : ℝ) : ℂ) ^ (-s)) =
      s * ∫ u : ℝ in x..x + 1, ((u : ℂ) ^ (-s - 1)) := by
  have hle : x ≤ x + 1 := by linarith
  have hderiv (u : ℝ) (hu : u ∈ uIcc x (x + 1)) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        ((-s) * (u : ℂ) ^ (-s - 1)) u := by
    by_cases hs0 : s = 0
    · subst s
      simpa using (hasDerivAt_const (x := u) (c := (1 : ℂ)))
    · exact hasDerivAt_ofReal_cpow_const
        (by rw [uIcc_of_le hle] at hu; linarith [hu.1])
        (neg_ne_zero.mpr hs0)
  have hint : IntervalIntegrable
      (fun u : ℝ => (-s) * (u : ℂ) ^ (-s - 1)) volume x (x + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
    intro u hu
    rw [uIcc_of_le hle] at hu
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hu.1])
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hfund
  calc
    (x : ℂ) ^ (-s) - (((x + 1 : ℝ) : ℂ) ^ (-s)) =
        -((-s) * ∫ u : ℝ in x..x + 1, ((u : ℂ) ^ (-s - 1))) := by
      rw [hfund]
      ring
    _ = s * ∫ u : ℝ in x..x + 1, ((u : ℂ) ^ (-s - 1)) := by
      ring

/-- Consecutive Euler second differences gain one full endpoint power. -/
lemma norm_pairedEtaEulerSecondDiffSummand_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖pairedEtaEulerSecondDiffSummand s n‖ ≤
      ‖s‖ * ‖s + 1‖ *
        (((2 * n + 1 : ℕ) : ℝ) ^ (s.re + 2))⁻¹ := by
  let k : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  have hk : 0 < k := by dsimp [k]; positivity
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s - 1)
  have hshift : (∫ u : ℝ in k + 1..k + 2, f u) =
      ∫ u : ℝ in k..k + 1, f (u + 1) := by
    rw [intervalIntegral.integral_comp_add_right f 1]
    congr 1
    ring
  have hf : IntervalIntegrable f volume k (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
    intro u hu
    rw [uIcc_of_le (by linarith : k ≤ k + 1)] at hu
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hu.1])
  have hfshift : IntervalIntegrable (fun u => f (u + 1)) volume k (k + 1) := by
    rw [IntervalIntegrable.comp_add_right_iff]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
    intro u hu
    rw [uIcc_of_le (by linarith : k + 1 ≤ k + 1 + 1)] at hu
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hu.1])
  have hIntegral :
      ‖∫ u : ℝ in k..k + 1, (f u - f (u + 1))‖ ≤
        ‖s + 1‖ * k ^ (-s.re - 2) := by
    calc
      ‖∫ u : ℝ in k..k + 1, (f u - f (u + 1))‖ ≤
          (‖s + 1‖ * k ^ (-s.re - 2)) * |k + 1 - k| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro u hu
        rw [uIoc_of_le (by linarith : k ≤ k + 1)] at hu
        have hstep := norm_cpow_add_one_sub_le (-s - 1)
          (show 0 < u by linarith [hu.1]) (by simp; linarith)
        have hstep' : ‖f u - f (u + 1)‖ ≤
            ‖s + 1‖ * u ^ (-s.re - 2) := by
          dsimp [f]
          rw [norm_sub_rev]
          have hnorm : ‖-s - 1‖ = ‖s + 1‖ := by
            rw [show -s - 1 = -(s + 1) by ring, norm_neg]
          have hexp : (-s - 1).re - 1 = -s.re - 2 := by
            simp only [neg_re, sub_re, one_re]
            ring
          rw [hnorm, hexp] at hstep
          exact hstep
        calc
          ‖f u - f (u + 1)‖ ≤ ‖s + 1‖ * u ^ (-s.re - 2) := hstep'
          _ ≤ ‖s + 1‖ * k ^ (-s.re - 2) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hk hu.1.le (by linarith))
              (norm_nonneg (s + 1))
      _ = ‖s + 1‖ * k ^ (-s.re - 2) := by
        rw [show k + 1 - k = 1 by ring, abs_one, mul_one]
  have hfirst := cpow_sub_add_one_eq_mul_integral s hk
  have hsecond := cpow_sub_add_one_eq_mul_integral s (show 0 < k + 1 by linarith)
  have hrepr : pairedEtaEulerSecondDiffSummand s n =
      s * ∫ u : ℝ in k..k + 1, (f u - f (u + 1)) := by
    rw [pairedEtaEulerSecondDiffSummand_eq]
    have hk0 : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) = (k : ℂ) := rfl
    have hk1 : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) = ((k + 1 : ℝ) : ℂ) := by
      dsimp [k]
      push_cast
      ring
    have hk2 : ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) = ((k + 2 : ℝ) : ℂ) := by
      dsimp [k]
      push_cast
      ring
    rw [hk0, hk1, hk2]
    rw [show (k : ℂ) ^ (-s) - 2 * ((k + 1 : ℝ) : ℂ) ^ (-s) +
        ((k + 2 : ℝ) : ℂ) ^ (-s) =
        ((k : ℂ) ^ (-s) - ((k + 1 : ℝ) : ℂ) ^ (-s)) -
          (((k + 1 : ℝ) : ℂ) ^ (-s) - ((k + 2 : ℝ) : ℂ) ^ (-s)) by ring]
    rw [show ((k : ℝ) : ℂ) ^ (-s) - ((k + 1 : ℝ) : ℂ) ^ (-s) =
      s * ∫ u : ℝ in k..k + 1, f u by simpa [f] using hfirst]
    have hsecond' : ((k + 1 : ℝ) : ℂ) ^ (-s) - ((k + 2 : ℝ) : ℂ) ^ (-s) =
        s * ∫ u : ℝ in k + 1..k + 2, f u := by
      simpa [f, add_assoc, add_comm, add_left_comm, one_add_one_eq_two] using hsecond
    rw [hsecond']
    rw [hshift, ← mul_sub, ← intervalIntegral.integral_sub hf hfshift]
  rw [hrepr, norm_mul]
  calc
    ‖s‖ * ‖∫ u : ℝ in k..k + 1, (f u - f (u + 1))‖ ≤
        ‖s‖ * (‖s + 1‖ * k ^ (-s.re - 2)) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ = ‖s‖ * ‖s + 1‖ * (k ^ (s.re + 2))⁻¹ := by
      rw [show -s.re - 2 = -(s.re + 2) by ring, Real.rpow_neg hk.le]
      ring
    _ = _ := rfl

/-- The inverse powers on every shifted odd progression are summable in the
range needed by the Euler tail. -/
lemma summable_odd_natAdd_inv_rpow
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    Summable (fun n : ℕ =>
      ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹)) := by
  let q : ℝ := -sigma - 2
  have hq : q < -1 := by dsimp [q]; linarith
  have hq0 : q ≤ 0 := hq.le.trans (by norm_num)
  have hfull : Summable (fun n : ℕ => (n : ℝ) ^ q) :=
    Real.summable_nat_rpow.mpr hq
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ q)) :=
    (summable_nat_add_iff 1).mpr hfull
  apply hshift.of_nonneg_of_le
  · intro n
    exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)
  · intro n
    have hbase : ((n + 1 : ℕ) : ℝ) ≤
        ((2 * (n + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * (n + N) + 1 by omega)
    have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    calc
      ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹) =
          ((2 * (n + N) + 1 : ℕ) : ℝ) ^ q := by
        rw [← Real.rpow_neg (by positivity :
          0 ≤ ((2 * (n + N) + 1 : ℕ) : ℝ))]
        congr 1
        dsimp [q]
        ring
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ q :=
        Real.rpow_le_rpow_of_nonpos hpos hbase hq0

/-- The shifted odd-endpoint power tail gains one endpoint power, with a
simple uniform constant. -/
lemma tsum_odd_natAdd_inv_rpow_le
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    (∑' n : ℕ,
      ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹)) ≤
      2 * (((2 * N + 1 : ℕ) : ℝ) ^ (sigma + 1))⁻¹ := by
  let M : ℕ := 2 * N + 1
  let q : ℝ := -sigma - 2
  have hM : 0 < M := by dsimp [M]; omega
  have hq : q < -1 := by dsimp [q]; linarith
  have hq0 : q ≤ 0 := hq.le.trans (by norm_num)
  let f : ℝ → ℝ := fun x => x ^ q
  have hfAnti : AntitoneOn f (Ici (M : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos
      ((show 0 < (M : ℝ) by exact_mod_cast hM).trans_le ha) hab hq0
  have hfInt : IntegrableOn f (Ioi (M : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt hq (by exact_mod_cast hM)
  have hfNonneg : ∀ x ∈ Ioi (M : ℝ), 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg
      (le_of_lt ((show 0 < (M : ℝ) by exact_mod_cast hM).trans hx)) q
  have htail := hfAnti.tsum_comp_add_le_integral M hfInt hfNonneg
  have hfull : Summable (fun n : ℕ => f n) := by
    exact Real.summable_nat_rpow.mpr hq
  have hshift : Summable (fun n : ℕ => f ((n + M : ℕ) : ℝ)) :=
    (summable_nat_add_iff M).mpr hfull
  have hsplit := hshift.tsum_eq_zero_add
  have hshiftBound :
      (∑' n : ℕ, f ((n + M : ℕ) : ℝ)) ≤
        f M + ∫ x : ℝ in Ioi (M : ℝ), f x := by
    rw [hsplit]
    have htail' : (∑' n : ℕ, f ((n + 1 + M : ℕ) : ℝ)) ≤
        ∫ x : ℝ in Ioi (M : ℝ), f x := by
      convert htail using 1
      congr 1
      funext n
      congr 1
      norm_cast
      omega
    simpa using add_le_add_left htail' (f (M : ℝ))
  have hoddPointwise (n : ℕ) :
      ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹) ≤
        f ((n + M : ℕ) : ℝ) := by
    have hbase : ((n + M : ℕ) : ℝ) ≤
        ((2 * (n + N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + M ≤ 2 * (n + N) + 1 by dsimp [M]; omega)
    have hpos : 0 < ((n + M : ℕ) : ℝ) := by exact_mod_cast Nat.add_pos_right n hM
    calc
      ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹) =
          ((2 * (n + N) + 1 : ℕ) : ℝ) ^ q := by
        rw [← Real.rpow_neg (by positivity :
          0 ≤ ((2 * (n + N) + 1 : ℕ) : ℝ))]
        congr 1
        dsimp [q]
        ring
      _ ≤ f ((n + M : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hpos hbase hq0
  have hoddSummable := summable_odd_natAdd_inv_rpow hsigma N
  calc
    (∑' n : ℕ, ((((2 * (n + N) + 1 : ℕ) : ℝ) ^ (sigma + 2))⁻¹)) ≤
        ∑' n : ℕ, f ((n + M : ℕ) : ℝ) :=
      Summable.tsum_le_tsum hoddPointwise hoddSummable hshift
    _ ≤ f M + ∫ x : ℝ in Ioi (M : ℝ), f x := hshiftBound
    _ = (M : ℝ) ^ q + (M : ℝ) ^ (q + 1) / (sigma + 1) := by
      rw [integral_Ioi_rpow_of_lt hq (by exact_mod_cast hM)]
      dsimp [f]
      rw [show q + 1 = -(sigma + 1) by dsimp [q]; ring]
      field_simp [show sigma + 1 ≠ 0 by linarith]
    _ ≤ 2 * (M : ℝ) ^ (-sigma - 1) := by
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have hfirst : (M : ℝ) ^ q ≤ (M : ℝ) ^ (-sigma - 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hMone
        dsimp [q]
        linarith
      have hdiv : (M : ℝ) ^ (q + 1) / (sigma + 1) ≤
          (M : ℝ) ^ (-sigma - 1) := by
        have hden : 1 ≤ sigma + 1 := by linarith
        have hpow : (M : ℝ) ^ (q + 1) = (M : ℝ) ^ (-sigma - 1) := by
          congr 1
          dsimp [q]
          ring
        rw [hpow]
        exact div_le_self (Real.rpow_nonneg (by positivity) _) hden
      linarith
    _ = 2 * (((2 * N + 1 : ℕ) : ℝ) ^ (sigma + 1))⁻¹ := by
      change 2 * (M : ℝ) ^ (-sigma - 1) =
        2 * ((M : ℝ) ^ (sigma + 1))⁻¹
      rw [show -sigma - 1 = -(sigma + 1) by ring,
        Real.rpow_neg (by exact_mod_cast hM.le)]

/-- The shifted infinite Euler second-difference tail. -/
def pairedEtaEulerSecondDiffTail (N : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, pairedEtaEulerSecondDiffSummand s (n + N)

/-- The complete Euler series splits exactly into its first `N` terms and
the shifted tail. -/
theorem pairedEtaEulerSecondDiffCore_sub_partialSum_eq_tail
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaEulerSecondDiffCore s -
        pairedEtaEulerSecondDiffPartialSum N s =
      pairedEtaEulerSecondDiffTail N s := by
  have hsplit :=
    (summable_pairedEtaEulerSecondDiffSummand hs).sum_add_tsum_nat_add N
  unfold pairedEtaEulerSecondDiffCore pairedEtaEulerSecondDiffPartialSum
    pairedEtaEulerSecondDiffTail
  rw [← hsplit]
  ring

/-- The Euler second-difference tail is one full endpoint power smaller than
the original eta and gap tails. -/
theorem norm_pairedEtaEulerSecondDiffTail_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaEulerSecondDiffTail N s‖ ≤
      2 * ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
  let C : ℝ := ‖s‖ * ‖s + 1‖
  let a : ℕ → ℝ := fun n =>
    (((2 * (n + N) + 1 : ℕ) : ℝ) ^ (s.re + 2))⁻¹
  have hshift : Summable (fun n : ℕ =>
      pairedEtaEulerSecondDiffSummand s (n + N)) :=
    (summable_nat_add_iff N).mpr
      (summable_pairedEtaEulerSecondDiffSummand hs)
  have hnorm := hshift.norm
  have ha : Summable a := by
    exact summable_odd_natAdd_inv_rpow hs N
  have hmajor : Summable (fun n => C * a n) := ha.mul_left C
  have hpoint (n : ℕ) :
      ‖pairedEtaEulerSecondDiffSummand s (n + N)‖ ≤ C * a n := by
    exact norm_pairedEtaEulerSecondDiffSummand_le hs (n + N)
  calc
    ‖pairedEtaEulerSecondDiffTail N s‖ ≤
        ∑' n : ℕ, ‖pairedEtaEulerSecondDiffSummand s (n + N)‖ := by
      unfold pairedEtaEulerSecondDiffTail
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * a n :=
      Summable.tsum_le_tsum hpoint hnorm hmajor
    _ = C * ∑' n : ℕ, a n := tsum_mul_left
    _ ≤ C * (2 * (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_odd_natAdd_inv_rpow_le hs N)
        (mul_nonneg (norm_nonneg s) (norm_nonneg (s + 1)))
    _ = 2 * ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
      dsimp [C]
      ring

/-- Quantitative Euler acceleration of the finite arithmetic gap error. -/
theorem norm_pairedEtaGapCorePartialSum_sub_core_add_half_endpoint_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaGapCorePartialSum N s - pairedEtaGapCore s +
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2‖ ≤
      ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by
  have hid :=
    pairedEtaGapCorePartialSum_sub_core_eq_neg_half_endpoint_add_eulerTail
      hs N
  rw [pairedEtaEulerSecondDiffCore_sub_partialSum_eq_tail hs N] at hid
  rw [hid]
  have htail := norm_pairedEtaEulerSecondDiffTail_le hs N
  calc
    ‖-(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2) +
          pairedEtaEulerSecondDiffTail N s / 2 +
          ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2‖ =
        ‖pairedEtaEulerSecondDiffTail N s‖ / 2 := by
      rw [show -(((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2) +
          pairedEtaEulerSecondDiffTail N s / 2 +
          ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) / 2 =
          pairedEtaEulerSecondDiffTail N s / 2 by ring]
      rw [norm_div]
      norm_num
    _ ≤ (2 * ‖s‖ * ‖s + 1‖ *
          (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹) / 2 := by
      exact div_le_div_of_nonneg_right htail (by norm_num)
    _ = ‖s‖ * ‖s + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (s.re + 1))⁻¹ := by ring

/-- At a nontrivial zeta zero, the gap partial sum has the sharp leading
half-endpoint term with a one-power-smaller explicit error. -/
theorem norm_nontrivialZetaZero_etaGapFiniteError_add_half_endpoint_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaGapCorePartialSum N rho.1 - 1 +
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-rho.1) / 2‖ ≤
      ‖rho.1‖ * ‖rho.1 + 1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (rho.1.re + 1))⁻¹ := by
  simpa [pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho] using
    norm_pairedEtaGapCorePartialSum_sub_core_add_half_endpoint_le
      (NontrivialZetaZero.zero_lt_re rho) N

/-- A hypothetical off-critical zero and its functional-equation partner have
sharp half-endpoint gap asymptotics at distinct complementary exponents. -/
theorem nontrivialZetaZero_offCritical_etaGapSharpComplementary_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    rho.1.re ≠ 1 - rho.1.re ∧
      ∀ N : ℕ,
        (‖pairedEtaGapCorePartialSum N rho.1 - 1 +
            ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-rho.1) / 2‖ ≤
          ‖rho.1‖ * ‖rho.1 + 1‖ *
            (((2 * N + 1 : ℕ) : ℝ) ^ (rho.1.re + 1))⁻¹) ∧
        (‖pairedEtaGapCorePartialSum N
              (NontrivialZetaZero.conjugatePartner rho).1 - 1 +
            ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
              (-(NontrivialZetaZero.conjugatePartner rho).1) / 2‖ ≤
          ‖(NontrivialZetaZero.conjugatePartner rho).1‖ *
            ‖(NontrivialZetaZero.conjugatePartner rho).1 + 1‖ *
              (((2 * N + 1 : ℕ) : ℝ) ^
                ((NontrivialZetaZero.conjugatePartner rho).1.re + 1))⁻¹) := by
  constructor
  · intro heq
    apply hoff
    linarith
  · intro N
    exact
      ⟨norm_nontrivialZetaZero_etaGapFiniteError_add_half_endpoint_le rho N,
        norm_nontrivialZetaZero_etaGapFiniteError_add_half_endpoint_le
          (NontrivialZetaZero.conjugatePartner rho) N⟩

end

end RiemannGaussian
