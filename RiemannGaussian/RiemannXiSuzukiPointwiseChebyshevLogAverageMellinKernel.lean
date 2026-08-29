import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageDrift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin kernels for the Suzuki logarithmic average

Suzuki's weighted Chebyshev logarithmic-average error was previously exposed
as a literal von-Mangoldt sum only at natural endpoints.  This file first
proves the corresponding formula at every real endpoint `b >= 1`, with the
finite prefix cut at `floor b`.

It then evaluates the two improper integrals needed to Mellin transform that
literal formula.  For `sigma > 1 / 2`, each logarithmic atom has integral

`integral_n^infinity log(x / n) * x^(-sigma - 1/2) dx
  = n^(-sigma + 1/2) / (sigma - 1/2)^2`.

After multiplication by `Lambda(n) / sqrt(n)`, this is exactly the real
von-Mangoldt Dirichlet term `Lambda(n) * n^(-sigma)` divided by the square of
the Mellin parameter.  For `sigma > 1`, the square-root main term has integral
`4 / (sigma - 1)`.  Integrability is proved separately, so the next stage can
justify the infinite sum--integral exchange rather than assuming it.

No estimate for the logarithmic average, analytic continuation, or
zero-location conclusion is asserted here.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Literal real-endpoint formula -/

/-- At every real endpoint `b >= 1`, the logarithmic average is the literal
finite weighted von-Mangoldt prefix through `floor b`. -/
theorem
    suzukiChebyshevLogAverageError_eq_sum_log_sub_log_of_one_le
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevLogAverageError b =
      (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (Real.log b - Real.log n)) -
        4 * b ^ (1 / 2 : ℝ) := by
  unfold suzukiChebyshevLogAverageError
  unfold suzukiChebyshevWeightedMass suzukiChebyshevWeightedLogMoment
  rw [← suzukiChebyshevMassAbel_eq hb,
    ← suzukiChebyshevLogMomentAbel_eq hb]
  simp_rw [suzukiChebyshevMassKernel_nat_eq,
    suzukiChebyshevLogMomentKernel_nat_eq]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply congrArg (fun value : ℝ => value - 4 * b ^ (1 / 2 : ℝ))
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The real-endpoint formula in Suzuki's quotient-log kernel. -/
theorem suzukiChebyshevLogAverageError_eq_sum_log_div_of_one_le
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevLogAverageError b =
      (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            Real.log (b / n)) -
        4 * b ^ (1 / 2 : ℝ) := by
  rw [suzukiChebyshevLogAverageError_eq_sum_log_sub_log_of_one_le hb]
  apply congrArg (fun value : ℝ => value - 4 * b ^ (1 / 2 : ℝ))
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by
      have := (Finset.mem_Ioc.mp hn).1
      omega)
  have hbPos : 0 < b := zero_lt_one.trans_le hb
  rw [Real.log_div hbPos.ne' hnPos.ne']

/-! ## Logarithmic Mellin atom -/

/-- The real logarithmic Mellin atom associated with a prefix event at `n`. -/
def suzukiChebyshevMellinLogAtom (sigma n x : ℝ) : ℝ :=
  Real.log (x / n) * x ^ (-sigma - 1 / 2 : ℝ)

private def suzukiChebyshevMellinLogAtomAntiderivative
    (sigma n x : ℝ) : ℝ :=
  x ^ (-sigma + 1 / 2 : ℝ) *
    (Real.log (x / n) / (-sigma + 1 / 2 : ℝ) -
      1 / (-sigma + 1 / 2 : ℝ) ^ 2)

private theorem suzukiChebyshevMellinLogAtomAntiderivative_hasDerivAt
    {sigma n x : ℝ} (hsigma : 1 / 2 < sigma) (hn : 0 < n)
    (hx : n ≤ x) :
    HasDerivAt (suzukiChebyshevMellinLogAtomAntiderivative sigma n)
      (suzukiChebyshevMellinLogAtom sigma n x) x := by
  have hxpos : 0 < x := hn.trans_le hx
  have hexp : (-sigma + 1 / 2 : ℝ) ≠ 0 := by linarith
  have hpow := Real.hasDerivAt_rpow_const (x := x)
    (p := (-sigma + 1 / 2 : ℝ)) (Or.inl hxpos.ne')
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y / n)) x⁻¹ x := by
    have hh := ((hasDerivAt_id x).div_const n).log
      (div_ne_zero hxpos.ne' hn.ne')
    have hcoefficient : 1 / n / (x / n) = x⁻¹ := by
      field_simp
    simpa only [Function.comp_apply, id_eq] using
      hh.congr_deriv hcoefficient
  unfold suzukiChebyshevMellinLogAtomAntiderivative
  have hbracket :=
    (hlog.div_const (-sigma + 1 / 2 : ℝ)).sub_const
      (1 / (-sigma + 1 / 2 : ℝ) ^ 2)
  have hh := hpow.mul hbracket
  have hpower :
      x ^ (-sigma + 1 / 2 : ℝ) * x⁻¹ =
        x ^ (-sigma - 1 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hcoefficient :
      (-sigma + 1 / 2) * x ^ (-sigma + 1 / 2 - 1) *
            (Real.log (x / n) / (-sigma + 1 / 2) -
              1 / (-sigma + 1 / 2) ^ 2) +
          x ^ (-sigma + 1 / 2) *
            (x⁻¹ / (-sigma + 1 / 2)) =
        Real.log (x / n) * x ^ (-sigma - 1 / 2) := by
    rw [show -sigma + 1 / 2 - 1 = -sigma - 1 / 2 by ring]
    rw [show x ^ (-sigma + 1 / 2) *
        (x⁻¹ / (-sigma + 1 / 2)) =
        x ^ (-sigma - 1 / 2) / (-sigma + 1 / 2) by
      calc
        x ^ (-sigma + 1 / 2) *
              (x⁻¹ / (-sigma + 1 / 2)) =
            (x ^ (-sigma + 1 / 2) * x⁻¹) /
              (-sigma + 1 / 2) := by ring
        _ = x ^ (-sigma - 1 / 2) /
              (-sigma + 1 / 2) := by rw [hpower]]
    have halgebra (p X L : ℝ) (hp : p ≠ 0) :
        p * X * (L / p - 1 / p ^ 2) + X / p = L * X := by
      field_simp [hp]
      ring
    exact halgebra (-sigma + 1 / 2)
      (x ^ (-sigma - 1 / 2)) (Real.log (x / n)) hexp
  exact hh.congr_deriv hcoefficient

private theorem tendsto_suzukiChebyshevMellinRpow_mul_log_div_atTop
    {sigma n : ℝ} (hsigma : 1 / 2 < sigma) (hn : 0 < n) :
    Tendsto (fun x : ℝ =>
      x ^ (-sigma + 1 / 2 : ℝ) * Real.log (x / n))
      atTop (𝓝 0) := by
  have hq : 0 < sigma - 1 / 2 := by linarith
  have hlog : Tendsto
      (fun x : ℝ => Real.log x / x ^ (sigma - 1 / 2 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hq).tendsto_div_nhds_zero
  have hconst : Tendsto
      (fun x : ℝ => Real.log n / x ^ (sigma - 1 / 2 : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hq)
  have hdiff : Tendsto
      (fun x : ℝ =>
        Real.log x / x ^ (sigma - 1 / 2 : ℝ) -
          Real.log n / x ^ (sigma - 1 / 2 : ℝ))
      atTop (𝓝 0) := by
    simpa only [sub_zero] using hlog.sub hconst
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [show -sigma + 1 / 2 = -(sigma - 1 / 2) by ring,
    Real.rpow_neg hx.le, Real.log_div hx.ne' hn.ne']
  ring

private theorem
    tendsto_suzukiChebyshevMellinLogAtomAntiderivative_atTop
    {sigma n : ℝ} (hsigma : 1 / 2 < sigma) (hn : 0 < n) :
    Tendsto (suzukiChebyshevMellinLogAtomAntiderivative sigma n)
      atTop (𝓝 0) := by
  have hlog :=
    tendsto_suzukiChebyshevMellinRpow_mul_log_div_atTop hsigma hn
  have hpow : Tendsto (fun x : ℝ => x ^ (-sigma + 1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have hq : 0 < sigma - 1 / 2 := by linarith
    convert tendsto_rpow_neg_atTop hq using 1
    funext x
    congr 1
    ring
  unfold suzukiChebyshevMellinLogAtomAntiderivative
  convert (hlog.div_const (-sigma + 1 / 2 : ℝ)).sub
    (hpow.div_const ((-sigma + 1 / 2 : ℝ) ^ 2)) using 1
  · funext x
    ring
  · simp

private theorem suzukiChebyshevMellinLogAtom_nonneg_on_Ioi
    {sigma n x : ℝ} (hn : 0 < n) (hx : x ∈ Set.Ioi n) :
    0 ≤ suzukiChebyshevMellinLogAtom sigma n x := by
  have hxpos : 0 < x := hn.trans hx
  have hratio : 1 ≤ x / n := by
    apply (le_div_iff₀ hn).2
    simpa only [one_mul] using hx.le
  exact mul_nonneg (Real.log_nonneg hratio)
    (Real.rpow_nonneg hxpos.le _)

/-- Every logarithmic Mellin atom is integrable on its natural half-line
when `sigma > 1 / 2`. -/
theorem integrableOn_suzukiChebyshevMellinLogAtom_Ioi
    {sigma n : ℝ} (hsigma : 1 / 2 < sigma) (hn : 0 < n) :
    IntegrableOn (suzukiChebyshevMellinLogAtom sigma n)
      (Set.Ioi n) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := suzukiChebyshevMellinLogAtomAntiderivative sigma n)
  · intro x hx
    exact
      suzukiChebyshevMellinLogAtomAntiderivative_hasDerivAt
        hsigma hn hx
  · intro x hx
    exact suzukiChebyshevMellinLogAtom_nonneg_on_Ioi hn hx
  · exact
      tendsto_suzukiChebyshevMellinLogAtomAntiderivative_atTop
        hsigma hn

/-- Exact improper integral of one logarithmic Mellin atom. -/
theorem integral_suzukiChebyshevMellinLogAtom_Ioi
    {sigma n : ℝ} (hsigma : 1 / 2 < sigma) (hn : 0 < n) :
    (∫ x in Set.Ioi n, suzukiChebyshevMellinLogAtom sigma n x) =
      n ^ (-sigma + 1 / 2 : ℝ) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
  have hderiv : ∀ x ∈ Set.Ici n,
      HasDerivAt (suzukiChebyshevMellinLogAtomAntiderivative sigma n)
        (suzukiChebyshevMellinLogAtom sigma n x) x := by
    intro x hx
    exact
      suzukiChebyshevMellinLogAtomAntiderivative_hasDerivAt
        hsigma hn hx
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv
    (fun x hx => suzukiChebyshevMellinLogAtom_nonneg_on_Ioi hn hx)
    (tendsto_suzukiChebyshevMellinLogAtomAntiderivative_atTop
      hsigma hn)]
  unfold suzukiChebyshevMellinLogAtomAntiderivative
  rw [div_self hn.ne', Real.log_one]
  have hsquare :
      (-sigma + 1 / 2 : ℝ) ^ 2 = (sigma - 1 / 2 : ℝ) ^ 2 := by
    ring
  rw [hsquare]
  ring

/-- Including the literal Suzuki coefficient turns the atom integral into
the corresponding real von-Mangoldt Dirichlet term. -/
theorem integral_suzukiChebyshevMellinWeightedLogAtom_Ioi
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) {n : ℕ} (hn : 0 < n) :
    (∫ x in Set.Ioi (n : ℝ),
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          suzukiChebyshevMellinLogAtom sigma n x) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ) /
        (sigma - 1 / 2 : ℝ) ^ 2 := by
  rw [integral_const_mul,
    integral_suzukiChebyshevMellinLogAtom_Ioi
      hsigma (Nat.cast_pos.mpr hn)]
  have hnPos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale :
      (1 / Real.sqrt n) * (n : ℝ) ^ (-sigma + 1 / 2 : ℝ) =
        (n : ℝ) ^ (-sigma : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div,
      ← Real.rpow_neg hnPos.le, ← Real.rpow_add hnPos]
    congr 1
    ring
  rw [show ArithmeticFunction.vonMangoldt n / Real.sqrt n =
      ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt n) by ring]
  calc
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt n) *
          ((n : ℝ) ^ (-sigma + 1 / 2 : ℝ) /
            (sigma - 1 / 2 : ℝ) ^ 2) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt n) *
            (n : ℝ) ^ (-sigma + 1 / 2 : ℝ)) /
          (sigma - 1 / 2 : ℝ) ^ 2 := by ring
    _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma : ℝ) /
          (sigma - 1 / 2 : ℝ) ^ 2 := by rw [hscale]

/-! ## Square-root main term -/

/-- The square-root main term in the real Mellin integrand. -/
def suzukiChebyshevMellinMainTerm (sigma x : ℝ) : ℝ :=
  4 * Real.sqrt x * x ^ (-sigma - 1 / 2 : ℝ)

private theorem suzukiChebyshevMellinMainTerm_eq_rpow
    {sigma x : ℝ} (hx : 0 < x) :
    suzukiChebyshevMellinMainTerm sigma x =
      4 * x ^ (-sigma : ℝ) := by
  unfold suzukiChebyshevMellinMainTerm
  rw [Real.sqrt_eq_rpow]
  calc
    4 * x ^ (1 / 2 : ℝ) * x ^ (-sigma - 1 / 2 : ℝ) =
        4 * (x ^ (1 / 2 : ℝ) *
          x ^ (-sigma - 1 / 2 : ℝ)) := by ring
    _ = 4 * x ^ ((1 / 2 : ℝ) + (-sigma - 1 / 2 : ℝ)) := by
      rw [Real.rpow_add hx]
    _ = 4 * x ^ (-sigma : ℝ) := by congr 2; ring

/-- The square-root Mellin main term is integrable on `(1, infinity)` for
`sigma > 1`. -/
theorem integrableOn_suzukiChebyshevMellinMainTerm_Ioi
    {sigma : ℝ} (hsigma : 1 < sigma) :
    IntegrableOn (suzukiChebyshevMellinMainTerm sigma)
      (Set.Ioi 1) := by
  have hbase : IntegrableOn (fun x : ℝ => 4 * x ^ (-sigma : ℝ))
      (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (a := -sigma) (by linarith)
      zero_lt_one).const_mul 4
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact (suzukiChebyshevMellinMainTerm_eq_rpow
    (zero_lt_one.trans hx)).symm

/-- The square-root main term contributes the exact pole `4 / (sigma - 1)`
to the real Mellin transform. -/
theorem integral_suzukiChebyshevMellinMainTerm_Ioi
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∫ x in Set.Ioi (1 : ℝ),
        suzukiChebyshevMellinMainTerm sigma x) =
      4 / (sigma - 1) := by
  rw [show (∫ x in Set.Ioi (1 : ℝ),
      suzukiChebyshevMellinMainTerm sigma x) =
      ∫ x in Set.Ioi (1 : ℝ), 4 * x ^ (-sigma : ℝ) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact suzukiChebyshevMellinMainTerm_eq_rpow
      (zero_lt_one.trans hx)]
  rw [integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  simp only [Real.one_rpow]
  have hdenom : sigma - 1 ≠ 0 := by linarith
  have hnegDenom : -sigma + 1 ≠ 0 := by linarith
  field_simp [hdenom, hnegDenom]
  ring

end

end RiemannGaussian
