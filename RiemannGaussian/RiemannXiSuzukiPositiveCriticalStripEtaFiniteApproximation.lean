import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaBoundaryHeatLogNorm

/-!
# Finite arithmetic approximation of the paired-eta logarithmic derivative

The preceding detector is a radial variation of the log norm of the literal
paired Dirichlet-eta series. This module makes that arithmetic description
finite. It defines the finite odd-even eta polynomials and proves locally
uniform convergence to the eta core on the entire positive half-plane.

Every finite eta polynomial is entire. Applying the Cauchy derivative theorem
to the locally uniform convergence proves that its explicit differentiated
polynomial converges locally uniformly to the genuine eta derivative. Division
then gives locally uniform convergence of the finite logarithmic quotients on
the exact open set where the limiting eta core is nonzero.

No nonvanishing or convergence assertion is extended through the divisor. The
result is instead a rigorous interface for approximating each zero-free circle
in the heat-flux detector by completely finite Dirichlet-polynomial data.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The finite odd-even Dirichlet polynomial formed from the first `N`
paired-eta summands. -/
def pairedEtaCorePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaCoreSummand s n

/-- The finite polynomial formed by explicitly differentiating the first `N`
paired-eta summands. -/
def pairedEtaCoreDerivativePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaCoreDerivativeSummand s n

/-- The finite paired-eta polynomials converge locally uniformly to the
literal paired-eta core throughout the positive half-plane. -/
theorem tendstoLocallyUniformlyOn_pairedEtaCorePartialSum :
    TendstoLocallyUniformlyOn pairedEtaCorePartialSum pairedEtaCore
      atTop {s : ℂ | 0 < s.re} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0 < z.re at hz
  let delta : ℝ := z.re / 2
  let radius : ℝ := z.re / 2
  let K : ℝ := ‖z‖ + radius
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hbase : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (delta + 1)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (delta + 1)).mpr
        (by linarith)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  have hodd : Summable
      (fun n : ℕ =>
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) := by
    simpa [Function.comp_def] using
      hbase.comp_injective (i := fun n : ℕ => 2 * n) (by
        intro n m h
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  have hmajor : Summable
      (fun n : ℕ => K *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹) :=
    hodd.mul_left K
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball z radius) :
      ‖pairedEtaCoreSummand w n‖ ≤
        K * ((((2 * n + 1 : ℕ) : ℝ) ^ (delta + 1)))⁻¹ := by
    have hdist : dist w z < radius := by
      simpa [Metric.mem_ball] using hw
    have hreNorm : |w.re - z.re| ≤ dist w z := by
      calc
        |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ = dist w z := by rw [dist_eq_norm]
    have hwre : delta < w.re := by
      dsimp [delta, radius] at *
      linarith [neg_le_abs (w.re - z.re)]
    have hwNorm : ‖w‖ ≤ K := by
      calc
        ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ K := by
          dsimp [K]
          linarith
    have hraw := norm_pairedEtaCoreSummand_le
      (s := w) (hdelta.trans hwre) n
    let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by
      dsimp [a]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have ha0 : 0 ≤ a := zero_le_one.trans ha1
    have hpow : a ^ (-w.re - 1) ≤ a ^ (-delta - 1) :=
      Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
    rw [← Real.rpow_neg ha0,
      show -(w.re + 1) = -w.re - 1 by ring] at hraw
    rw [← Real.rpow_neg ha0,
      show -(delta + 1) = -delta - 1 by ring]
    calc
      ‖pairedEtaCoreSummand w n‖ ≤ ‖w‖ * a ^ (-w.re - 1) := by
        simpa [a] using hraw
      _ ≤ K * a ^ (-delta - 1) :=
        mul_le_mul hwNorm hpow (Real.rpow_nonneg ha0 _) hK
  refine ⟨Metric.ball z radius,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hradius), ?_⟩
  change TendstoUniformlyOn
    (fun N w => ∑ n ∈ Finset.range N, pairedEtaCoreSummand w n)
    (fun w => ∑' n : ℕ, pairedEtaCoreSummand w n)
    atTop (Metric.ball z radius)
  exact tendstoUniformlyOn_tsum_nat hmajor hbound

/-- Every finite paired-eta polynomial is entire. -/
theorem differentiable_pairedEtaCorePartialSum (N : ℕ) :
    Differentiable ℂ (pairedEtaCorePartialSum N) := by
  intro s
  unfold pairedEtaCorePartialSum
  exact DifferentiableAt.fun_sum fun n _ =>
    (hasDerivAt_pairedEtaCoreSummand s n).differentiableAt

/-- The derivative of a finite paired-eta polynomial is its explicit finite
derivative polynomial. -/
theorem deriv_pairedEtaCorePartialSum (N : ℕ) (s : ℂ) :
    deriv (pairedEtaCorePartialSum N) s =
      pairedEtaCoreDerivativePartialSum N s := by
  unfold pairedEtaCorePartialSum pairedEtaCoreDerivativePartialSum
  rw [deriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro n _
    exact deriv_pairedEtaCoreSummand s n
  · intro n _
    exact (hasDerivAt_pairedEtaCoreSummand s n).differentiableAt

/-- The explicit finite derivative polynomials converge locally uniformly to
the literal arithmetic derivative of paired eta on the positive half-plane. -/
theorem tendstoLocallyUniformlyOn_pairedEtaCoreDerivativePartialSum :
    TendstoLocallyUniformlyOn pairedEtaCoreDerivativePartialSum
      pairedEtaArithmeticDerivativeValue atTop {s : ℂ | 0 < s.re} := by
  have hderiv :=
    tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.deriv
      (Eventually.of_forall fun N =>
        (differentiable_pairedEtaCorePartialSum N).differentiableOn)
      (Complex.isOpen_re_gt 0)
  have hpartial :
      TendstoLocallyUniformlyOn pairedEtaCoreDerivativePartialSum
        (deriv pairedEtaCore) atTop {s : ℂ | 0 < s.re} := by
    apply hderiv.congr
    intro N s _
    simp only [Function.comp_apply]
    exact deriv_pairedEtaCorePartialSum N s
  apply hpartial.congr_right
  intro s hs
  change 0 < s.re at hs
  exact (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hs).deriv

/-- The exact positive-half-plane domain on which the paired-eta logarithmic
derivative has no divisor singularity. -/
def pairedEtaArithmeticQuotientDomain : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ pairedEtaCore s ≠ 0}

/-- The quotient of the explicit finite derivative polynomial by the finite
paired-eta polynomial. -/
def pairedEtaArithmeticQuotientPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  pairedEtaCoreDerivativePartialSum N s /
    pairedEtaCorePartialSum N s

/-- Away from the limiting eta divisor, the completely finite arithmetic
quotients converge locally uniformly to the literal eta logarithmic
derivative. -/
theorem tendstoLocallyUniformlyOn_pairedEtaArithmeticQuotientPartialSum :
    TendstoLocallyUniformlyOn pairedEtaArithmeticQuotientPartialSum
      (fun s => pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)
      atTop pairedEtaArithmeticQuotientDomain := by
  have hsubset :
      pairedEtaArithmeticQuotientDomain ⊆ {s : ℂ | 0 < s.re} :=
    fun _ hs => hs.1
  have hE :=
    tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.mono hsubset
  have hD :=
    tendstoLocallyUniformlyOn_pairedEtaCoreDerivativePartialSum.mono hsubset
  have hEcontinuous : ContinuousOn pairedEtaCore
      pairedEtaArithmeticQuotientDomain :=
    (analyticOnNhd_pairedEtaCore.mono hsubset).continuousOn
  have hDcontinuous : ContinuousOn pairedEtaArithmeticDerivativeValue
      pairedEtaArithmeticQuotientDomain := by
    intro s hs
    have hanalytic := (analyticOnNhd_pairedEtaCore s hs.1).deriv
    have hpositive : ∀ᶠ w in nhds s, 0 < w.re :=
      (Complex.isOpen_re_gt 0).mem_nhds hs.1
    have heq : pairedEtaArithmeticDerivativeValue =ᶠ[nhds s]
        deriv pairedEtaCore := by
      filter_upwards [hpositive] with w hw
      exact
        (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv.symm
    exact
      (hanalytic.continuousAt.congr_of_eventuallyEq heq).continuousWithinAt
  exact hD.div₀ hE hDcontinuous hEcontinuous (fun s hs => hs.2)

end

end RiemannGaussian
