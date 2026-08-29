import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageMellinKernel
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The real Mellin transform of Suzuki's logarithmic average

This file assembles the atom kernels from the preceding module into the
complete real Mellin transform of the weighted Chebyshev logarithmic-average
error.  Each prime atom is supported on its natural half-line.  Lean proves
that every atom is integrable, that the series of its norm integrals is
summable by absolute convergence of the von Mangoldt L-series, and that its
pointwise sum is exactly the literal finite prime prefix.

Those results justify the infinite sum--integral exchange.  For every real
`sigma > 1`, the transform is identified first with the real von Mangoldt
Dirichlet series and then with the Riemann zeta logarithmic derivative:

`integral_1^infinity (-A(x)) x^(-sigma-1/2) dx
  = (zeta'(sigma) / zeta(sigma)) / (sigma-1/2)^2 + 4/(sigma-1)`.

The displayed equality is stated in `ℂ` after casting the real integral,
matching Mathlib's zeta API.  It is proved only on the absolutely convergent
half-plane.  No analytic continuation, sign estimate for `A`, or
zero-location conclusion is assumed or proved here.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped BigOperators LSeries.notation Topology

/-- A von-Mangoldt logarithmic Mellin atom, extended by zero below its natural event point. -/
def suzukiChebyshevMellinSupportedWeightedLogAtom (sigma : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Set.indicator (Set.Ici (n : ℝ))
    (fun y =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        suzukiChebyshevMellinLogAtom sigma n y) x

/-- Every supported weighted prime atom is integrable on the real line when `sigma > 1/2`. -/
theorem integrable_suzukiChebyshevMellinSupportedWeightedLogAtom
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (n : ℕ) :
    Integrable (suzukiChebyshevMellinSupportedWeightedLogAtom sigma n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : suzukiChebyshevMellinSupportedWeightedLogAtom sigma 0 = fun _x : ℝ => 0 := by
      funext x
      simp [suzukiChebyshevMellinSupportedWeightedLogAtom]
    rw [hzero]
    exact integrable_zero _ _ _
  unfold suzukiChebyshevMellinSupportedWeightedLogAtom
  rw [integrable_indicator_iff measurableSet_Ici]
  apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
  exact (integrableOn_suzukiChebyshevMellinLogAtom_Ioi
    hsigma (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).const_mul _

/-- The integral of a supported weighted atom is its real von-Mangoldt Dirichlet term divided by `(sigma - 1/2)^2`. -/
theorem integral_suzukiChebyshevMellinSupportedWeightedLogAtom
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (n : ℕ) :
    (∫ x : ℝ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [suzukiChebyshevMellinSupportedWeightedLogAtom, suzukiChebyshevMellinLogAtom]
  unfold suzukiChebyshevMellinSupportedWeightedLogAtom
  rw [integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  exact integral_suzukiChebyshevMellinWeightedLogAtom_Ioi
    hsigma (Nat.pos_of_ne_zero hn)

private theorem suzukiChebyshevMellinSupportedWeightedLogAtom_nonnegative
    {sigma : ℝ} (n : ℕ) (x : ℝ) :
    0 ≤ suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x := by
  unfold suzukiChebyshevMellinSupportedWeightedLogAtom
  by_cases hx : x ∈ Set.Ici (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    by_cases hn : n = 0
    · subst n
      simp [suzukiChebyshevMellinLogAtom]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hxpos : 0 < x := hnpos.trans_le hx
    have hratio : 1 ≤ x / n := by
      apply (le_div_iff₀ hnpos).2
      simpa only [one_mul, Set.mem_Ici] using hx
    exact mul_nonneg
      (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        (Real.sqrt_nonneg _))
      (mul_nonneg (Real.log_nonneg hratio)
        (Real.rpow_nonneg hxpos.le _))
  · simp [hx]

private theorem integral_norm_suzukiChebyshevMellinSupportedWeightedLogAtom
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (n : ℕ) :
    (∫ x : ℝ, ‖suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x‖) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
  rw [show (fun x : ℝ => ‖suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x‖) =
      suzukiChebyshevMellinSupportedWeightedLogAtom sigma n by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (suzukiChebyshevMellinSupportedWeightedLogAtom_nonnegative n x)]]
  exact integral_suzukiChebyshevMellinSupportedWeightedLogAtom hsigma n

/-- Casting one real von-Mangoldt power term to `ℂ` gives Mathlib's corresponding `LSeries.term`. -/
theorem ofReal_vonMangoldt_mul_rpow_neg_eq_LSeries_term (sigma : ℝ) (n : ℕ) :
    ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ) : ℝ) : ℂ) =
      LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (sigma : ℂ) n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-sigma)]
  rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by simp,
    Complex.cpow_neg]
  simp only [Complex.ofReal_natCast]
  rw [div_eq_mul_inv]

/-- The real nonnegative von-Mangoldt Dirichlet series is summable for `sigma > 1`. -/
theorem summable_vonMangoldt_mul_rpow_neg_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ)) := by
  rw [← Complex.summable_ofReal]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : ℂ)) (by simpa using hsigma)).congr
      (fun n => (ofReal_vonMangoldt_mul_rpow_neg_eq_LSeries_term sigma n).symm)

/-- At every `b >= 1`, the pointwise infinite atom sum truncates exactly to the literal prime prefix through `floor b`. -/
theorem tsum_suzukiChebyshevMellinSupportedWeightedLogAtom_eq_finite
    (sigma : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∑' n : ℕ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n b) =
      (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            Real.log (b / n)) *
        b ^ (-sigma - 1 / 2 : ℝ) := by
  rw [tsum_eq_sum (s := Finset.Ioc 1 ⌊b⌋₊) (fun n hn => by
    have hnnot : ¬(1 < n ∧ n ≤ ⌊b⌋₊) := by
      simpa only [Finset.mem_Ioc] using hn
    by_cases hnsmall : n ≤ 1
    · interval_cases n <;>
        simp [suzukiChebyshevMellinSupportedWeightedLogAtom, suzukiChebyshevMellinLogAtom]
    · have hfloor : ⌊b⌋₊ < n := by omega
      have hnb : ¬((n : ℝ) ≤ b) := by
        intro hle
        exact (not_le_of_gt hfloor) (Nat.le_floor hle)
      simp [suzukiChebyshevMellinSupportedWeightedLogAtom, hnb])]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hbnonneg : 0 ≤ b := zero_le_one.trans hb
  have hnle : (n : ℝ) ≤ b :=
    (Nat.le_floor_iff hbnonneg).mp (Finset.mem_Ioc.mp hn).2
  unfold suzukiChebyshevMellinSupportedWeightedLogAtom
  rw [Set.indicator_of_mem
    (show b ∈ Set.Ici (n : ℝ) from hnle)]
  unfold suzukiChebyshevMellinLogAtom
  ring

/-- The atom norm integrals form a summable series; this is the exact Fubini hypothesis for the prime part. -/
theorem summable_integral_norm_suzukiChebyshevMellinSupportedWeightedLogAtom
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => ∫ x : ℝ,
      ‖suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x‖) := by
  refine ((summable_vonMangoldt_mul_rpow_neg_of_one_lt hsigma).div_const
    ((sigma - 1 / 2 : ℝ) ^ 2)).congr fun n => ?_
  exact (integral_norm_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n).symm

/-- Termwise integration of all supported prime atoms recovers the complete real von-Mangoldt Dirichlet series. -/
theorem integral_tsum_suzukiChebyshevMellinSupportedWeightedLogAtom
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ x : ℝ, ∑' n : ℕ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x) =
      (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
  have hinterchange :=
    integral_tsum_of_summable_integral_norm
      (fun n => integrable_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n)
      (summable_integral_norm_suzukiChebyshevMellinSupportedWeightedLogAtom hsigma)
  calc
    (∫ x : ℝ, ∑' n : ℕ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x) =
        ∑' n : ℕ, ∫ x : ℝ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x :=
      hinterchange.symm
    _ = ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
          (sigma - 1 / 2 : ℝ) ^ 2 := by
      apply tsum_congr
      intro n
      exact integral_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n
    _ = (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
      rw [tsum_div_const]

private theorem suzukiChebyshevMellinSupportedWeightedLogAtom_eq_zero_of_le_one
    (sigma : ℝ) {x : ℝ} (hx : x ≤ 1) (n : ℕ) :
    suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x = 0 := by
  by_cases hnsmall : n ≤ 1
  · interval_cases n <;>
      simp [suzukiChebyshevMellinSupportedWeightedLogAtom, suzukiChebyshevMellinLogAtom]
  · have hnot : ¬((n : ℝ) ≤ x) := by
      exact not_le_of_gt (hx.trans_lt (by exact_mod_cast (lt_of_not_ge hnsmall)))
    simp [suzukiChebyshevMellinSupportedWeightedLogAtom, hnot]

private theorem summable_suzukiChebyshevMellinSupportedWeightedLogAtom_at
    (sigma x : ℝ) :
    Summable (fun n : ℕ => suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x) := by
  by_cases hx : 1 ≤ x
  · apply summable_of_ne_finset_zero (s := Finset.Ioc 1 ⌊x⌋₊)
    intro n hn
    have hnnot : ¬(1 < n ∧ n ≤ ⌊x⌋₊) := by
      simpa only [Finset.mem_Ioc] using hn
    by_cases hnsmall : n ≤ 1
    · interval_cases n <;>
        simp [suzukiChebyshevMellinSupportedWeightedLogAtom, suzukiChebyshevMellinLogAtom]
    · have hfloor : ⌊x⌋₊ < n := by omega
      have hnx : ¬((n : ℝ) ≤ x) := by
        intro hle
        exact (not_le_of_gt hfloor) (Nat.le_floor hle)
      simp [suzukiChebyshevMellinSupportedWeightedLogAtom, hnx]
  · have hxle : x ≤ 1 := le_of_not_ge hx
    have hzero : (fun n : ℕ => suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x) = 0 := by
      funext n
      exact suzukiChebyshevMellinSupportedWeightedLogAtom_eq_zero_of_le_one sigma hxle n
    rw [hzero]
    exact summable_zero

private def suzukiChebyshevLogAverageMellinFullTerm (sigma : ℝ) : ℕ → ℝ → ℝ
  | 0, x => Set.indicator (Set.Ioi (1 : ℝ))
      (fun y => -suzukiChebyshevMellinMainTerm sigma y) x
  | n + 1, x => suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x

private theorem tsum_suzukiChebyshevLogAverageMellinFullTerm_eq_head_add_tail
    (sigma x : ℝ) :
    (∑' k : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma k x) =
      Set.indicator (Set.Ioi (1 : ℝ))
          (fun y => -suzukiChebyshevMellinMainTerm sigma y) x +
        ∑' n : ℕ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x := by
  have htail : Summable
      (fun n : ℕ => suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x) := by
    have heq : (fun n : ℕ => suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x) =
        fun n : ℕ => suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x := by
      funext n
      rfl
    rw [heq]
    exact summable_suzukiChebyshevMellinSupportedWeightedLogAtom_at sigma x
  have hsplit :
      (∑ i ∈ Finset.range 1, suzukiChebyshevLogAverageMellinFullTerm sigma i x) +
          ∑' i : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma (i + 1) x =
        ∑' i : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma i x :=
    htail.sum_add_tsum_nat_add' (f := fun i =>
      suzukiChebyshevLogAverageMellinFullTerm sigma i x) (k := 1)
  have hhead :
      (∑ i ∈ Finset.range 1, suzukiChebyshevLogAverageMellinFullTerm sigma i x) =
        Set.indicator (Set.Ioi (1 : ℝ))
          (fun y => -suzukiChebyshevMellinMainTerm sigma y) x := by
    simp [suzukiChebyshevLogAverageMellinFullTerm]
  have htailTsum :
      (∑' i : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma (i + 1) x) =
        ∑' n : ℕ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x := by
    apply tsum_congr
    intro n
    rfl
  rw [hhead, htailTsum] at hsplit
  exact hsplit.symm

private theorem tsum_suzukiChebyshevLogAverageMellinFullTerm_eq_zero_of_le_one
    (sigma : ℝ) {x : ℝ} (hx : x ≤ 1) :
    (∑' k : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma k x) = 0 := by
  rw [tsum_suzukiChebyshevLogAverageMellinFullTerm_eq_head_add_tail]
  simp [show x ∉ Set.Ioi (1 : ℝ) by exact not_lt_of_ge hx]
  simp_rw [suzukiChebyshevMellinSupportedWeightedLogAtom_eq_zero_of_le_one sigma hx]
  simp

private theorem indicator_suzukiChebyshevLogAverageMellin_eq_tsum_full
    (sigma x : ℝ) :
    Set.indicator (Set.Ioi (1 : ℝ))
        (fun y => suzukiChebyshevLogAverageError y *
          y ^ (-sigma - 1 / 2 : ℝ)) x =
      ∑' k : ℕ, suzukiChebyshevLogAverageMellinFullTerm sigma k x := by
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem hx]
    rw [tsum_suzukiChebyshevLogAverageMellinFullTerm_eq_head_add_tail]
    rw [Set.indicator_of_mem hx]
    rw [tsum_suzukiChebyshevMellinSupportedWeightedLogAtom_eq_finite sigma hx.le]
    rw [suzukiChebyshevLogAverageError_eq_sum_log_div_of_one_le hx.le]
    unfold suzukiChebyshevMellinMainTerm
    rw [Real.sqrt_eq_rpow]
    ring
  · have hleft : Set.indicator (Set.Ioi (1 : ℝ))
        (fun y => suzukiChebyshevLogAverageError y *
          y ^ (-sigma - 1 / 2 : ℝ)) x = 0 := by
      simp [hx]
    rw [hleft]
    exact (tsum_suzukiChebyshevLogAverageMellinFullTerm_eq_zero_of_le_one sigma (le_of_not_gt hx)).symm

private theorem integrable_suzukiChebyshevLogAverageMellinFullTerm
    {sigma : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    Integrable (suzukiChebyshevLogAverageMellinFullTerm sigma k) := by
  cases k with
  | zero =>
      unfold suzukiChebyshevLogAverageMellinFullTerm
      rw [integrable_indicator_iff measurableSet_Ioi]
      exact (integrableOn_suzukiChebyshevMellinMainTerm_Ioi hsigma).neg
  | succ n =>
      exact integrable_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n

private theorem summable_integral_norm_suzukiChebyshevLogAverageMellinFullTerm
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun k : ℕ => ∫ x : ℝ,
      ‖suzukiChebyshevLogAverageMellinFullTerm sigma k x‖) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [suzukiChebyshevLogAverageMellinFullTerm] using
    summable_integral_norm_suzukiChebyshevMellinSupportedWeightedLogAtom hsigma

private theorem integral_suzukiChebyshevLogAverageMellinFullTerm_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ x : ℝ, suzukiChebyshevLogAverageMellinFullTerm sigma 0 x) =
      -4 / (sigma - 1) := by
  unfold suzukiChebyshevLogAverageMellinFullTerm
  rw [integral_indicator measurableSet_Ioi, integral_neg,
    integral_suzukiChebyshevMellinMainTerm_Ioi hsigma]
  ring

private theorem tsum_integral_suzukiChebyshevLogAverageMellinFullTerm
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' k : ℕ, ∫ x : ℝ, suzukiChebyshevLogAverageMellinFullTerm sigma k x) =
      (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
          (sigma - 1 / 2 : ℝ) ^ 2 -
        4 / (sigma - 1) := by
  have htail : Summable
      (fun n : ℕ => ∫ x : ℝ,
        suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x) := by
    refine ((summable_vonMangoldt_mul_rpow_neg_of_one_lt hsigma).div_const
      ((sigma - 1 / 2 : ℝ) ^ 2)).congr fun n => ?_
    change ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-sigma : ℝ) /
            (sigma - 1 / 2 : ℝ) ^ 2 =
      ∫ x : ℝ, suzukiChebyshevMellinSupportedWeightedLogAtom sigma n x
    exact (integral_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n).symm
  have hsplit :
      (∫ x : ℝ, suzukiChebyshevLogAverageMellinFullTerm sigma 0 x) +
          ∑' n : ℕ, ∫ x : ℝ,
            suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x =
        ∑' k : ℕ, ∫ x : ℝ, suzukiChebyshevLogAverageMellinFullTerm sigma k x := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
      htail.sum_add_tsum_nat_add' (f := fun k =>
        ∫ x : ℝ, suzukiChebyshevLogAverageMellinFullTerm sigma k x) (k := 1)
  rw [← hsplit, integral_suzukiChebyshevLogAverageMellinFullTerm_zero hsigma]
  rw [show (∑' n : ℕ, ∫ x : ℝ,
      suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x) =
      (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
        (sigma - 1 / 2 : ℝ) ^ 2 by
    calc
      (∑' n : ℕ, ∫ x : ℝ,
          suzukiChebyshevLogAverageMellinFullTerm sigma (n + 1) x) =
          ∑' n : ℕ,
            (ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (-sigma : ℝ)) /
                (sigma - 1 / 2 : ℝ) ^ 2 := by
        apply tsum_congr
        intro n
        exact integral_suzukiChebyshevMellinSupportedWeightedLogAtom (by linarith) n
      _ = (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (-sigma : ℝ)) /
          (sigma - 1 / 2 : ℝ) ^ 2 := by rw [tsum_div_const]]
  ring

/-- Exact real Mellin transform of Suzuki's logarithmic-average error on the half-plane `sigma > 1`. -/
theorem integral_suzukiChebyshevLogAverageError_mul_mellinWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ x in Set.Ioi (1 : ℝ),
        suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ)) =
      (∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-sigma : ℝ)) /
          (sigma - 1 / 2 : ℝ) ^ 2 -
        4 / (sigma - 1) := by
  rw [← integral_indicator measurableSet_Ioi]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
    indicator_suzukiChebyshevLogAverageMellin_eq_tsum_full sigma x)]
  rw [← integral_tsum_of_summable_integral_norm
    (fun k => integrable_suzukiChebyshevLogAverageMellinFullTerm hsigma k)
    (summable_integral_norm_suzukiChebyshevLogAverageMellinFullTerm hsigma)]
  exact tsum_integral_suzukiChebyshevLogAverageMellinFullTerm hsigma

/-- The cast of the real von-Mangoldt power series is Mathlib's complex `LSeries`. -/
theorem ofReal_tsum_vonMangoldt_mul_rpow_neg
    (sigma : ℝ) :
    ((∑' n : ℕ,
        ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-sigma : ℝ) : ℝ) : ℂ) =
      LSeries
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (sigma : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  apply tsum_congr
  intro n
  exact ofReal_vonMangoldt_mul_rpow_neg_eq_LSeries_term sigma n

/-- On `sigma > 1`, the Mellin transform of `A` is the negative zeta logarithmic derivative term minus the square-root pole. -/
theorem ofReal_integral_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_negLogDeriv
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((∫ x in Set.Ioi (1 : ℝ),
        suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ)) : ℝ) : ℂ) =
      (-deriv riemannZeta (sigma : ℂ) /
          riemannZeta (sigma : ℂ)) /
          (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) -
        ((4 / (sigma - 1) : ℝ) : ℂ) := by
  rw [integral_suzukiChebyshevLogAverageError_mul_mellinWeight hsigma]
  rw [Complex.ofReal_sub, Complex.ofReal_div,
    ofReal_tsum_vonMangoldt_mul_rpow_neg]
  push_cast
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (by simpa using hsigma)]

/-- On `sigma > 1`, the Mellin transform of `-A` is `zeta'/zeta` divided by `(sigma-1/2)^2`, plus `4/(sigma-1)`. -/
theorem ofReal_integral_neg_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_logDeriv
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((∫ x in Set.Ioi (1 : ℝ),
        -suzukiChebyshevLogAverageError x *
          x ^ (-sigma - 1 / 2 : ℝ)) : ℝ) : ℂ) =
      (deriv riemannZeta (sigma : ℂ) /
          riemannZeta (sigma : ℂ)) /
          (((sigma - 1 / 2 : ℝ) ^ 2 : ℝ) : ℂ) +
        ((4 / (sigma - 1) : ℝ) : ℂ) := by
  rw [show (fun x : ℝ =>
      -suzukiChebyshevLogAverageError x *
        x ^ (-sigma - 1 / 2 : ℝ)) =
      fun x : ℝ => -(suzukiChebyshevLogAverageError x *
        x ^ (-sigma - 1 / 2 : ℝ)) by
    funext x
    ring]
  rw [integral_neg]
  rw [Complex.ofReal_neg]
  rw [ofReal_integral_suzukiChebyshevLogAverageError_mul_mellinWeight_eq_negLogDeriv hsigma]
  ring

end

end RiemannGaussian
