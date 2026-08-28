import RiemannGaussian.RiemannXiSuzukiArithmeticFormula
import RiemannGaussian.ScrewTransport

/-!
# Suzuki's pointwise arithmetic screw function

Suzuki's pointwise function `Psi` is defined in equation (1.1) of
"Aspects of the screw function corresponding to the Riemann zeta-function".
Its nonnegative-time formula consists of an Archimedean term and the finite
von-Mangoldt sum

`sum_{n <= exp t} (Lambda n / sqrt n) * (t - log n)`.

This file defines that literal real-valued formula.  It then proves that its
finite prime sum is exactly the locally finite negative-hinge model already
used by the transport modules.  In particular, the Archimedean normalization,
the cutoff, and the `n + 2` event enumeration are no longer an assumed seam.

The global positivity of this function remains equivalent to RH; no such
positivity is asserted here.
-/

namespace RiemannGaussian

noncomputable section

open scoped BigOperators Topology

/-! ## The order-two Hurwitz--Lerch value -/

/-- One real summand of `Phi(q, 2, 1/4)`. -/
def suzukiHurwitzLerchTwoSummand (q : ℝ) (n : ℕ) : ℝ :=
  q ^ n / ((n : ℝ) + 1 / 4) ^ 2

/-- The defining real series `Phi(q, 2, 1/4)`. -/
def suzukiHurwitzLerchTwo (q : ℝ) : ℝ :=
  ∑' n : ℕ, suzukiHurwitzLerchTwoSummand q n

/-- The order-two Hurwitz--Lerch series is summable throughout the closed
real unit interval.  This includes both the moving nome `exp (-2 t)` and the
endpoint value `Phi(1, 2, 1/4)` used as Suzuki's constant `C`. -/
theorem summable_suzukiHurwitzLerchTwoSummand
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (suzukiHurwitzLerchTwoSummand q) := by
  have hbase : Summable
      (fun n : ℕ => 1 / ((n : ℝ) + 1 / 4) ^ 2) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2
        (by norm_num)
    apply h.congr
    intro n
    rw [abs_of_pos (by positivity), Real.rpow_two]
  apply hbase.of_nonneg_of_le
  · intro n
    unfold suzukiHurwitzLerchTwoSummand
    positivity
  · intro n
    unfold suzukiHurwitzLerchTwoSummand
    apply div_le_div_of_nonneg_right
    · exact pow_le_one₀ hq0 hq1
    · positivity

/-! ## Suzuki's literal arithmetic formula -/

/-- The finite real von-Mangoldt summand in Suzuki's pointwise formula. -/
def suzukiPointwisePrimeTerm (t : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * (t - Real.log n)

/-- The source-exact finite prime contribution, with cutoff
`1 <= n <= exp t`. -/
def suzukiPointwisePrimeContribution (t : ℝ) : ℝ :=
  ∑ n ∈ suzukiArithmeticPrimeWindow t,
    suzukiPointwisePrimeTerm t n

/-- The complete non-prime part of Suzuki's pointwise formula.  The real part
of the quarter-point digamma is used because the formula is real-valued. -/
def suzukiPointwiseArchimedean (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    t / 2 * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) +
      1 / 4 *
        (suzukiHurwitzLerchTwo 1 -
          Real.exp (-t / 2) *
            suzukiHurwitzLerchTwo (Real.exp (-2 * t)))

/-- Suzuki's pointwise arithmetic `Psi` on nonnegative screw time, defined
by the literal prime formula.  The expression is total, but its source
interpretation is used on `t >= 0`. -/
def riemannXiSuzukiPsiNonnegative (t : ℝ) : ℝ :=
  suzukiPointwiseArchimedean t - suzukiPointwisePrimeContribution t

/-- The even extension of Suzuki's pointwise arithmetic `Psi` to the real
line. -/
def riemannXiSuzukiPsi (t : ℝ) : ℝ :=
  riemannXiSuzukiPsiNonnegative |t|

/-- Unfolding the Lean definition gives Suzuki's corrected equation (1.1),
including the `-(t/2) log pi` normalization. -/
theorem riemannXiSuzukiPsiNonnegative_eq_explicit (t : ℝ) :
    riemannXiSuzukiPsiNonnegative t =
      4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) -
        (∑ n ∈ suzukiArithmeticPrimeWindow t,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (t - Real.log n)) +
        t / 2 * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) +
        1 / 4 *
          (suzukiHurwitzLerchTwo 1 -
            Real.exp (-t / 2) *
              suzukiHurwitzLerchTwo (Real.exp (-2 * t))) := by
  unfold riemannXiSuzukiPsiNonnegative suzukiPointwiseArchimedean
    suzukiPointwisePrimeContribution suzukiPointwisePrimeTerm
  ring

/-- Suzuki's even extension is definitionally even. -/
@[simp] theorem riemannXiSuzukiPsi_neg (t : ℝ) :
    riemannXiSuzukiPsi (-t) = riemannXiSuzukiPsi t := by
  simp [riemannXiSuzukiPsi]

/-- The arithmetic formula has its prescribed zero value at the origin. -/
@[simp] theorem riemannXiSuzukiPsi_zero :
    riemannXiSuzukiPsi 0 = 0 := by
  simp [riemannXiSuzukiPsi, riemannXiSuzukiPsiNonnegative,
    suzukiPointwiseArchimedean, suzukiPointwisePrimeContribution,
    suzukiArithmeticPrimeWindow, suzukiPointwisePrimeTerm]
  norm_num

/-! ## Exact finite-window / hinge identification -/

private theorem sum_Icc_one_eq_sum_range_add_two
    (f : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (hf : f 1 = 0) :
    (∑ n ∈ Finset.Icc 1 N, f n) =
      ∑ k ∈ Finset.range (N - 1), f (k + 2) := by
  rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons, hf, zero_add,
    ← Finset.Icc_succ_left_eq_Ioc 1 N]
  change (∑ n ∈ Finset.Icc 2 N, f n) = _
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  have hcount : N + 1 - 2 = N - 1 := by omega
  rw [hcount]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.add_comm]

/-- On nonnegative time, Suzuki's source prime window is exactly the finite
prefix of the `n + 2` event enumeration used by the hinge model. -/
theorem suzukiPointwisePrimeContribution_eq_sum_range
    {t : ℝ} (ht : 0 ≤ t) :
    suzukiPointwisePrimeContribution t =
      ∑ k ∈ Finset.range (⌊Real.exp t⌋₊ - 1),
        suzukiPointwisePrimeTerm t (k + 2) := by
  have hexpOne : (1 : ℝ) ≤ Real.exp t := by
    simpa using Real.exp_le_exp.mpr ht
  have hfloorOne : 1 ≤ ⌊Real.exp t⌋₊ :=
    (Nat.le_floor_iff (Real.exp_nonneg t)).2 (by
      exact_mod_cast hexpOne)
  unfold suzukiPointwisePrimeContribution suzukiArithmeticPrimeWindow
  exact sum_Icc_one_eq_sum_range_add_two
    (suzukiPointwisePrimeTerm t) ⌊Real.exp t⌋₊ hfloorOne (by
      simp [suzukiPointwisePrimeTerm])

/-- The locally finite infinite sum of Suzuki's negative prime hinges is
exactly the negative of the literal finite von-Mangoldt contribution. -/
theorem tsum_suzukiPrimeNegativeHinge_eq_neg_pointwisePrimeContribution
    {t : ℝ} (ht : 0 ≤ t) :
    (∑' n : ℕ, screwNegativeHinge (suzukiPrimeWeight n)
        (suzukiPrimeLocation n) t) =
      -suzukiPointwisePrimeContribution t := by
  let N : ℕ := ⌊Real.exp t⌋₊
  have hfinite :
      (∑' n : ℕ, screwNegativeHinge (suzukiPrimeWeight n)
          (suzukiPrimeLocation n) t) =
        ∑ n ∈ Finset.range (N - 1),
          screwNegativeHinge (suzukiPrimeWeight n)
            (suzukiPrimeLocation n) t := by
    apply tsum_eq_sum
    intro n hn
    have hnLower : N - 1 ≤ n := by
      simpa [Finset.mem_range, not_lt] using hn
    have hfloorLt : N < n + 2 := by omega
    have hexpLt : Real.exp t < ((n + 2 : ℕ) : ℝ) := by
      exact (Nat.floor_lt (Real.exp_nonneg t)).1 hfloorLt
    apply screwNegativeHinge_eq_zero_of_le_location
    unfold suzukiPrimeLocation
    exact (Real.le_log_iff_exp_le (by positivity)).2 hexpLt.le
  rw [hfinite, suzukiPointwisePrimeContribution_eq_sum_range ht]
  change
    (∑ n ∈ Finset.range (N - 1),
      screwNegativeHinge (suzukiPrimeWeight n)
        (suzukiPrimeLocation n) t) =
      -(∑ k ∈ Finset.range (N - 1),
        suzukiPointwisePrimeTerm t (k + 2))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnUpper : n + 2 ≤ N := by
    have hnLt : n < N - 1 := Finset.mem_range.mp hn
    omega
  have hcastFloor : (((n + 2 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hnUpper
  have hfloorExp : (N : ℝ) ≤ Real.exp t := by
    exact Nat.floor_le (Real.exp_nonneg t)
  have hlog : Real.log ((n + 2 : ℕ) : ℝ) ≤ t :=
    (Real.log_le_iff_le_exp (by positivity)).2
      (hcastFloor.trans hfloorExp)
  unfold screwNegativeHinge suzukiPrimeWeight suzukiPrimeLocation
    suzukiPointwisePrimeTerm
  rw [max_eq_left (sub_nonneg.mpr hlog)]

/-- The literal arithmetic pointwise function is exactly the previously
formalized Suzuki hinge model, with its full Archimedean background now
fixed rather than supplied as an arbitrary parameter. -/
theorem riemannXiSuzukiPsiNonnegative_eq_screwHingeModel
    {t : ℝ} (ht : 0 ≤ t) :
    riemannXiSuzukiPsiNonnegative t =
      screwHingeModel suzukiPointwiseArchimedean
        suzukiPrimeLocation suzukiPrimeWeight t := by
  unfold riemannXiSuzukiPsiNonnegative screwHingeModel
  rw [tsum_suzukiPrimeNegativeHinge_eq_neg_pointwisePrimeContribution ht]
  ring

end

end RiemannGaussian
