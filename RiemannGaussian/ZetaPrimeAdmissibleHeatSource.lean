/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFermiHeatTransport

/-!
# The original prime source at admissible moving Gaussian scales

The actual global Fermi margin tends to zero. At each fixed moment order,
its squared margin therefore removes the Gaussian regulator and its Fermi
parameter tends to one. A diagonal choice of proved height witnesses makes
both the source-normalized error and the complete zero-tail allowance less
than `1/(N+1)`, while keeping the Gaussian width at the admissible squared
margin. The original negative-multiplicity source survives along this
moving family, with the original complex polynomial and prime sieve.

Every height above the chosen floor has the proved tolerances. Thus every
moving family eventually above those floors preserves the original source.
The heights are chosen from proved convergence statements, with no assumed
arithmetic bound. Their rate is not estimated. This does not give the
surviving signed prime moment an independent lower bound.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Topology
open scoped Classical
open EtaGammaSmoothing GaussianFermiSpectralWeight GaussianFermiDerivativeBounds
open GaussianFermiZeroPair GaussianFermiMovingAllowance

/-- The proved all-height Fermi margin tends to zero along positive
heights, using its exact eventual logarithmic formula. -/
theorem tendsto_zetaFermiZeroMargin :
    Tendsto zetaFermiZeroMargin atTop (𝓝 0) := by
  obtain ⟨T, hT, he⟩ := exists_eventual_fermiZeroMargin_eq
  have h : Tendsto (fun H : ℝ => (3 / 20 : ℝ) * (Real.log H)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (3 / 20 : ℝ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop T] with H hH
  have hH0 : 0 ≤ H := by linarith
  rw [(he H (by simpa only [abs_of_nonneg hH0] using hH)).1, abs_of_nonneg hH0]
  ring

/-- The squared improved margin is a positive Gaussian width in the
whole-zero allowance's admissible range at every real height. -/
theorem fermi_margin_square_admissible (H : ℝ) :
    0 < zetaFermiZeroMargin H ^ 2 ∧
      zetaPoleReserveZeroMargin H ^ 2 ≤ zetaFermiZeroMargin H ^ 2 ∧
      zetaFermiZeroMargin H ^ 2 ≤ 1 := by
  have hm := zetaFermiZeroMargin_bounds H
  refine ⟨sq_pos_of_pos hm.1, ?_, ?_⟩
  · exact pow_le_pow_left₀ (zetaPoleReserveZeroMargin_bounds H).1.le
      (zetaPoleReserve_margin_le_fermi H) 2
  · nlinarith

/-- The complete existing zero-tail allowance vanishes when the Gaussian
width is exactly the square of the improved all-height margin. -/
theorem tendsto_allowance_fermi_margin_square :
    Tendsto (fun H : ℝ => allowance (zetaFermiZeroMargin H ^ 2) H) atTop (𝓝 0) :=
  tendsto_allowance_of_admissible _
    (Eventually.of_forall fun H => (fermi_margin_square_admissible H).2)

namespace SquarefreeEulerQuadratic

/-- Joint removal of the Gaussian regulator and variation of the Fermi
parameter preserve the full Euler moment at each fixed order. The original
unweighted complex moment supplies a common summable dominator. -/
theorem tendsto_gaussianFermiPrimeLogResponse_joint (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re)
    {ι : Type*} {l : Filter ι} {A B : ι → ℝ} {a : ℝ}
    (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 0))
    (hB0 : ∀ᶠ j in l, 0 ≤ B j) :
    Tendsto (fun j => gaussianFermiPrimeLogResponse (A j) (B j) p D S N s) l
      (𝓝 (fermiPrimeLogResponse a p D S N s)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_primeLogResponse p D S hS N hs).norm
  · intro n
    have hw : Tendsto (fun j => window (B j) (Real.log n)) l (𝓝 1) := by
      simpa only [window, neg_zero, zero_mul, Real.exp_zero, Function.comp_def] using
        (Real.continuous_exp.tendsto _).comp (hB.neg.mul_const ((Real.log n) ^ 2))
    have hf : Tendsto (fun j => fermi (-A j * Real.log n)) l
        (𝓝 (fermi (-a * Real.log n))) := by
      exact (continuous_fermi.tendsto _).comp (hA.neg.mul_const (Real.log n))
    have hc := (Complex.continuous_ofReal.tendsto _).comp (hw.mul hf)
    simpa only [one_mul, Function.comp_def] using
      hc.const_mul (primeCorrectionCoefficient D S n * zetaPrimeFilterKernel p N s n)
  · filter_upwards [hB0] with j hj n
    apply (norm_gaussianFermiPrimeLogTerm_le (A j) hj p D S N s n).trans
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fermi_bounds _).1.le]
    exact mul_le_of_le_one_right (norm_nonneg _) (fermi_bounds _).2.le

/-- The actual margin simultaneously supplies an admissible vanishing
Gaussian width and a Fermi parameter tending to one. Every fixed complex
moment converges, without a new arithmetic or zero-free hypothesis. -/
theorem tendsto_margin_gaussianFermiPrimeLogResponse (p : Polynomial ℂ)
    (D : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun H : ℝ => gaussianFermiPrimeLogResponse (1 - 2 * zetaFermiZeroMargin H)
      (zetaFermiZeroMargin H ^ 2) p D S N s) atTop
      (𝓝 (fermiPrimeLogResponse 1 p D S N s)) := by
  apply tendsto_gaussianFermiPrimeLogResponse_joint p D S hS N hs
  · simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (tendsto_zetaFermiZeroMargin.const_mul 2)
  · simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using tendsto_zetaFermiZeroMargin.pow 2
  · exact Eventually.of_forall fun _ => sq_nonneg _

/-- The original source-normalized moment at the actual Fermi parameter
and its admissible squared-margin Gaussian width. The original polynomial,
quadratic prime sieve and `3/2` sample are unchanged. -/
def normalizedMarginHeatPrimeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) (H : ℝ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    gaussianFermiPrimeLogResponse (1 - 2 * zetaFermiZeroMargin H)
      (zetaFermiZeroMargin H ^ 2) (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)

/-- At each order the exact original normalization survives the joint
height limit. This fixed-order theorem is the input to the proved
diagonal choice below, rather than an asserted exchange of limits. -/
theorem tendsto_normalizedMarginHeatPrimeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) :
    Tendsto (normalizedMarginHeatPrimeResponse rho hrho N D) atTop
      (𝓝 (normalizedFermiPrimeLogResponse 1 rho hrho N D)) := by
  exact (tendsto_margin_gaussianFermiPrimeLogResponse (zetaRightHalfPoleJetFilter rho hrho) D
    (zetaRightHalfPrimePatternPrimes rho N)
    (fun r hr => (zetaRightHalfPrimePatternPrimes_eligible rho N r hr).1) N
    (s := 3 / 2 + I * rho.1.im) (by norm_num)).const_mul _

/-- A genuine height witness pays both the normalized smoothing error and
the full zero-tail allowance at the same admissible Gaussian width.
The height also encloses the target ordinate and dominates the order. -/
theorem exists_primeMomentHeatHeight (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) :
    ∃ H : ℝ, (N : ℝ) ≤ H ∧ 1 ≤ H ∧ 2 * |rho.1.im| ≤ H ∧ ∀ T : ℝ, H ≤ T →
      ‖normalizedMarginHeatPrimeResponse rho hrho N D T -
        normalizedFermiPrimeLogResponse 1 rho hrho N D‖ < 1 / ((N : ℝ) + 1) ∧
      allowance (zetaFermiZeroMargin T ^ 2) T < 1 / ((N : ℝ) + 1) := by
  have he : Tendsto (fun H => ‖normalizedMarginHeatPrimeResponse rho hrho N D H -
      normalizedFermiPrimeLogResponse 1 rho hrho N D‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_normalizedMarginHeatPrimeResponse rho hrho N D).sub_const
        (normalizedFermiPrimeLogResponse 1 rho hrho N D)).norm
  have htol : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hgood : ∀ᶠ H : ℝ in atTop, (N : ℝ) ≤ H ∧ 1 ≤ H ∧ 2 * |rho.1.im| ≤ H ∧
      ‖normalizedMarginHeatPrimeResponse rho hrho N D H -
        normalizedFermiPrimeLogResponse 1 rho hrho N D‖ < 1 / ((N : ℝ) + 1) ∧
      allowance (zetaFermiZeroMargin H ^ 2) H < 1 / ((N : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (N : ℝ), eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (2 * |rho.1.im|), he.eventually_lt_const htol,
      tendsto_allowance_fermi_margin_square.eventually_lt_const htol] with H hN hH ht he htail
    exact ⟨hN, hH, ht, he, htail⟩
  obtain ⟨H, hH⟩ := eventually_atTop.mp hgood
  have h := hH H le_rfl
  exact ⟨H, h.1, h.2.1, h.2.2.1, fun T hT => (hH T hT).2.2.2⟩

/-- A mathematically defined admissible height, selected from the proved
simultaneous error and whole-divisor allowance theorem. It assumes no
lower bound for the surviving prime sum. -/
def primeMomentHeatHeight (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) : ℝ := Classical.choose (exists_primeMomentHeatHeight rho hrho N D)

/-- The selected height retains every bound supplied by its proved
existence theorem, including both separate `1/(N+1)` tolerances. -/
theorem primeMomentHeatHeight_spec (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) :
    let H := primeMomentHeatHeight rho hrho N D;
    (N : ℝ) ≤ H ∧ 1 ≤ H ∧ 2 * |rho.1.im| ≤ H ∧
      ‖normalizedMarginHeatPrimeResponse rho hrho N D H -
        normalizedFermiPrimeLogResponse 1 rho hrho N D‖ < 1 / ((N : ℝ) + 1) ∧
      allowance (zetaFermiZeroMargin H ^ 2) H < 1 / ((N : ℝ) + 1) := by
  have h := Classical.choose_spec (exists_primeMomentHeatHeight rho hrho N D)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 _ le_rfl⟩

/-- Every height beyond the selected floor satisfies both tolerances.
The construction therefore supports all sufficiently large height choices
at each order, rather than only its canonical sequence of witnesses. -/
theorem primeMomentHeatHeight_tail_spec (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N D : ℕ) {H : ℝ}
    (hH : primeMomentHeatHeight rho hrho N D ≤ H) :
    ‖normalizedMarginHeatPrimeResponse rho hrho N D H -
      normalizedFermiPrimeLogResponse 1 rho hrho N D‖ < 1 / ((N : ℝ) + 1) ∧
      allowance (zetaFermiZeroMargin H ^ 2) H < 1 / ((N : ℝ) + 1) :=
  (Classical.choose_spec (exists_primeMomentHeatHeight rho hrho N D)).2.2.2 H hH

/-- The diagonal height tends to infinity for every moving cutoff,
independently of any size bound on that cutoff. -/
theorem tendsto_primeMomentHeatHeight (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) :
    Tendsto (fun N => primeMomentHeatHeight rho hrho N (D N)) atTop atTop :=
  tendsto_atTop_mono (fun N => (primeMomentHeatHeight_spec rho hrho N (D N)).1)
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The selected Gaussian widths tend to zero even as the moment order
and original cutoff vary. Admissibility is retained at every order. -/
theorem tendsto_primeMomentHeatWidth (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) :
    Tendsto (fun N => zetaFermiZeroMargin (primeMomentHeatHeight rho hrho N (D N)) ^ 2)
      atTop (𝓝 0) := by
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Function.comp_def] using
    (tendsto_zetaFermiZeroMargin.comp (tendsto_primeMomentHeatHeight rho hrho D)).pow 2

/-- The full original prime response along the selected admissible
Gaussian family. This is a retained filtered arithmetic sum, not a
definition in terms of its desired limiting value. -/
def admissibleHeatPrimeResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) (N : ℕ) : ℂ :=
  normalizedMarginHeatPrimeResponse rho hrho N (D N) (primeMomentHeatHeight rho hrho N (D N))

/-- Every moving height family eventually above the proved floor has
vanishing source-normalized smoothing error, including arbitrary faster
growth and every moving cutoff. -/
theorem tendsto_marginHeat_sub_fermi_of_height (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (H : ℕ → ℝ)
    (hH : ∀ᶠ N in atTop, primeMomentHeatHeight rho hrho N (D N) ≤ H N) :
    Tendsto (fun N => normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N) -
      normalizedFermiPrimeLogResponse 1 rho hrho N (D N)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ tendsto_one_div_add_atTop_nhds_zero_nat
  exact hH.mono fun N hN => (primeMomentHeatHeight_tail_spec rho hrho N (D N) hN).1.le

/-- The selected simultaneous limit has independently vanishing
source-normalized smoothing error for every moving cutoff. -/
theorem tendsto_admissibleHeat_sub_fermi (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) :
    Tendsto (fun N => admissibleHeatPrimeResponse rho hrho D N -
      normalizedFermiPrimeLogResponse 1 rho hrho N (D N)) atTop (𝓝 0) :=
  tendsto_marginHeat_sub_fermi_of_height rho hrho D _ (Eventually.of_forall fun _ => le_rfl)

/-- Every family eventually above the proved height floor also has a
vanishing complete zero-tail allowance at the same squared-margin widths. -/
theorem tendsto_marginHeat_allowance_of_height (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (H : ℕ → ℝ)
    (hH : ∀ᶠ N in atTop, primeMomentHeatHeight rho hrho N (D N) ≤ H N) :
    Tendsto (fun N => allowance (zetaFermiZeroMargin (H N) ^ 2) (H N)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun N => allowance_nonneg (fermi_margin_square_admissible _).1 _
  · exact hH.mono fun N hN => (primeMomentHeatHeight_tail_spec rho hrho N (D N) hN).2.le

/-- The complete zero-tail allowance also vanishes along the same
selected heights and the same admissible Gaussian widths. -/
theorem tendsto_admissibleHeat_allowance (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) :
    Tendsto (fun N => allowance (zetaFermiZeroMargin (primeMomentHeatHeight rho hrho N (D N)) ^ 2)
      (primeMomentHeatHeight rho hrho N (D N))) atTop (𝓝 0) :=
  tendsto_allowance_fermi_margin_square.comp (tendsto_primeMomentHeatHeight rho hrho D)

/-- The unchanged original prime tail and the selected admissible heat
family have independently vanishing difference at the original source
normalization. Only eventual positivity of the cutoff is required. -/
theorem tendsto_actual_prime_sub_admissibleHeat (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (hD : ∀ᶠ N in atTop, 1 ≤ D N) :
    Tendsto (fun N => normalizedPrimeLogResponse rho hrho N (D N) -
      admissibleHeatPrimeResponse rho hrho D N) atTop (𝓝 0) := by
  have hp := tendsto_actual_prime_sub_fermi rho hrho D (fun _ => 1) hD
    (Eventually.of_forall fun _ => by norm_num)
  have hg := tendsto_admissibleHeat_sub_fermi rho hrho D
  have h := hp.sub hg
  convert h using 1
  · funext N
    ring
  · simp

/-- The unchanged source and every Gaussian family above the proved
height floor have independently vanishing difference. The original
cutoff needs no upper bound in this comparison. -/
theorem tendsto_actual_prime_sub_marginHeat (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (H : ℕ → ℝ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N)
    (hH : ∀ᶠ N in atTop, primeMomentHeatHeight rho hrho N (D N) ≤ H N) :
    Tendsto (fun N => normalizedPrimeLogResponse rho hrho N (D N) -
      normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N)) atTop (𝓝 0) := by
  have hp := tendsto_actual_prime_sub_fermi rho hrho D (fun _ => 1) hD
    (Eventually.of_forall fun _ => by norm_num)
  have hg := tendsto_marginHeat_sub_fermi_of_height rho hrho D H hH
  have h := hp.sub hg
  convert h using 1
  · funext N
    ring
  · simp

/-- One constant controls the difference between the unchanged original
prime tail and every Gaussian family above the proved height floor, for
every moving cutoff. The independently proved error is an explicit geometric term
plus `1/(N+1)`, with no source limit used in its proof. -/
theorem exists_actual_prime_marginHeat_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    let u : ℝ := 3 / 2 - rho.1.re;
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℕ → ℕ, ∀ H : ℕ → ℝ, ∀ N : ℕ, 1 ≤ D N →
      primeMomentHeatHeight rho hrho N (D N) ≤ H N →
      ‖normalizedPrimeLogResponse rho hrho N (D N) -
        normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N)‖ ≤
        C * (2 * u / (1 + u)) ^ N + 1 / ((N : ℝ) + 1) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := exists_normalized_primeFermi_bound (zetaRightHalfPoleJetFilter rho hrho)
    (u := 3 / 2 - rho.1.re) (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro D H N hD hH
  have hp : ‖normalizedPrimeLogResponse rho hrho N (D N) -
      normalizedFermiPrimeLogResponse 1 rho hrho N (D N)‖ ≤
        C * (2 * (3 / 2 - rho.1.re) / (1 + (3 / 2 - rho.1.re))) ^ N := by
    simpa only [normalizedPrimeLogResponse, normalizedFermiPrimeLogResponse, mul_sub] using
      hbound rho.1.im N (D N) hD (zetaRightHalfPrimePatternPrimes rho N)
        (fun r hr => (zetaRightHalfPrimePatternPrimes_eligible rho N r hr).1) 1 (by norm_num)
  have he : ‖normalizedFermiPrimeLogResponse 1 rho hrho N (D N) -
      normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N)‖ ≤ 1 / ((N : ℝ) + 1) := by
    rw [norm_sub_rev]
    exact (primeMomentHeatHeight_tail_spec rho hrho N (D N) hH).1.le
  have ht := dist_triangle (normalizedPrimeLogResponse rho hrho N (D N))
    (normalizedFermiPrimeLogResponse 1 rho hrho N (D N))
    (normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N))
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add hp he)

/-- The original hypothetical negative-multiplicity source persists for
every height family eventually above the proved floor, at admissible
Gaussian widths. No independent lower bound for that moment is assumed. -/
theorem tendsto_marginHeatPrimeResponse_of_height (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (H : ℕ → ℝ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2)
    (hH : ∀ᶠ N in atTop, primeMomentHeatHeight rho hrho N (D N) ≤ H N) :
    Tendsto (fun N => normalizedMarginHeatPrimeResponse rho hrho N (D N) (H N)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hp := tendsto_normalizedPrimeLogResponse rho hrho D hD
  have he := tendsto_actual_prime_sub_marginHeat rho hrho D H (hD.mono fun _ h => h.1) hH
  simpa only [sub_sub_cancel, sub_zero] using hp.sub he

/-- The original hypothetical negative-multiplicity source survives
on the selected admissible Gaussian family. No independent signed lower
bound for that surviving response is supplied by this theorem. -/
theorem tendsto_admissibleHeatPrimeResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 2) :
    Tendsto (admissibleHeatPrimeResponse rho hrho D) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hp := tendsto_normalizedPrimeLogResponse rho hrho D hD
  have he := tendsto_actual_prime_sub_admissibleHeat rho hrho D (hD.mono fun _ h => h.1)
  simpa only [sub_sub_cancel, sub_zero] using hp.sub he

/-- The selected arithmetic response is exactly the full positive-density
spectral average of the original complex prime moment on `1+m_F(H)`.
The normalization, polynomial, phase and ordinary-prime sieve all remain. -/
theorem admissibleHeatPrimeResponse_eq_integral (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (D : ℕ → ℕ) (N : ℕ) :
    let H := primeMomentHeatHeight rho hrho N (D N);
    let m := zetaFermiZeroMargin H;
    admissibleHeatPrimeResponse rho hrho D N =
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) / 2) *
        ∫ y : ℝ, (density (1 - 2 * m) (m ^ 2) y : ℂ) *
          primeLogResponse (zetaRightHalfPoleJetFilter rho hrho) (D N)
            (zetaRightHalfPrimePatternPrimes rho N) N (1 + (m : ℂ) + I * rho.1.im - I * y) := by
  dsimp only
  rw [integral_margin_density_primeLogResponse
    (primeMomentHeatHeight rho hrho N (D N))
    (fermi_margin_square_admissible _).1 _ _ _
    (fun r hr => (zetaRightHalfPrimePatternPrimes_eligible rho N r hr).1)]
  unfold admissibleHeatPrimeResponse normalizedMarginHeatPrimeResponse
  ring

end SquarefreeEulerQuadratic
end
end RiemannGaussian
