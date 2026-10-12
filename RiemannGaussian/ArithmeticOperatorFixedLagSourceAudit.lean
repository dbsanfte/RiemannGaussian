/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorNonlinearSourceAudit
import RiemannGaussian.ZetaFiniteDirichlet

/-!
# A linear Mellin source does not force any finite fixed-lag detector

For every finite set of positive lags, a periodic concentration of the
power row retains EXACTLY the same nonzero Mellin residue and has no
density pole, yet kills the entire joined off-diagonal lag packet at
every physical cutoff, with arbitrary complex masks and phases.

The model lives on literal integer divisor incidence by Möbius inversion.
It is not the actual Mangoldt array, does not satisfy all exact actual
Gamma observations, and is not a generalized-prime Euler product.
The no-go concerns inference of a nonlinear source from a linear pole
alone. Growing unbounded lag families require a separate uniform gate.
-/

namespace RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit
noncomputable section
open Complex Filter ArithmeticOperatorNonlinearSourceAudit
open ArithmeticOperatorSuccessorSourceAudit ArithmeticOperatorIncidenceFreedom
open ArithmeticOperatorKummerCutoff
open scoped BigOperators Topology ComplexConjugate

/-- Exact concentration normalization; its Mellin multiplier equals
one at the matched real exponent. No numerical normalization is used. -/
def amplification (M : ℕ) (beta : ℝ) : ℂ :=
  Complex.exp ((beta : ℂ)*(Real.log M : ℂ))

private def base (M : ℕ) (v : ℂ) (beta : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else amplification M beta*matchedRow v beta n

/-- Periodic sparse integer row, retaining the zero endpoint exactly. -/
def sparseRow (M : ℕ) (v : ℂ) (beta : ℝ) : ℕ → ℂ :=
  zetaDilationCoefficient M (base M v beta)

/-- Dilation multiplier normalized to one at the prescribed source exponent. -/
def multiplier (M : ℕ) (beta : ℝ) (s : ℂ) : ℂ :=
  amplification M beta*zetaPrimeFeature s M

/-- Exact meromorphic response of the periodic diagnostic row. -/
def response (M : ℕ) (v : ℂ) (beta : ℝ) (s : ℂ) : ℂ :=
  multiplier M beta s*smoothResponse v beta s

/-- Literal jointly weighted off-diagonal packet: no lag, prime phase,
mask or cutoff is independently norm-paid. -/
def lagPacket (S : Finset ℕ) (X : ℕ) (W : ℕ → ℕ → ℂ) (g : ℕ → ℂ) : ℂ :=
  ∑ h ∈ S, ∑ n ∈ Finset.Icc 1 X, W n h*g n*conj (g (n+h))

/-- First gate: divisibility compatibility is exact for every complex
profile. It annihilates a pair whenever its lag is not a multiple of M. -/
theorem sparse_pair_zero {M h : ℕ} (hh : ¬M ∣ h) (v : ℂ) (beta : ℝ) (n : ℕ) :
    sparseRow M v beta n*conj (sparseRow M v beta (n+h)) = 0 := by
  by_cases hn : M ∣ n
  · have hnext : ¬M ∣ n+h := by
      intro he
      exact hh ((Nat.dvd_add_iff_right hn).mpr he)
    simp only [sparseRow, zetaDilationCoefficient, ite_eq_right hnext, map_zero, mul_zero]
  · simp only [sparseRow, zetaDilationCoefficient, ite_eq_right hn, zero_mul]

/-- Complete signed joining does not repair the invisible source:
EVERY coefficient packet vanishes, with all finite endpoints unchanged. -/
theorem lagPacket_zero {M : ℕ} (S : Finset ℕ) (hS : ∀ h ∈ S, ¬M ∣ h)
    (v : ℂ) (beta : ℝ) (X : ℕ) (W : ℕ → ℕ → ℂ) :
    lagPacket S X W (sparseRow M v beta) = 0 := by
  unfold lagPacket
  apply Finset.sum_eq_zero
  intro h hh
  apply Finset.sum_eq_zero
  intro n _
  rw [mul_assoc, sparse_pair_zero (hS h hh), mul_zero]

private theorem base_hasSum (M : ℕ) (v : ℂ) (beta : ℝ) {s : ℂ} (hs : beta < s.re) :
    LSeriesHasSum (base M v beta) s (amplification M beta*smoothResponse v beta s) := by
  have hh := (matched_summable v beta hs).LSeriesHasSum.smul (amplification M beta)
  rw [smooth_euler_response v beta hs] at hh
  apply (LSeriesHasSum_congr s _ (f := base M v beta)
    (g := fun n => amplification M beta*matchedRow v beta n)
    (fun {n} hn => by simp [base, hn])).mpr
  exact hh

/-- Actual absolute convergence of the model series on its exact
half-plane. Its continuation is never called a convergent Euler sum. -/
theorem sparse_hasSum {M : ℕ} (hM : 0 < M) (v : ℂ) (beta : ℝ)
    {s : ℂ} (hs : beta < s.re) :
    LSeriesHasSum (sparseRow M v beta) s (response M v beta s) := by
  have hh := LSeriesHasSum_zetaDilationCoefficient hM (a := base M v beta)
    (by simp [base]) (base_hasSum M v beta hs)
  unfold sparseRow
  convert hh using 1
  unfold response multiplier
  ring

theorem multiplier_at_source (M : ℕ) (beta : ℝ) : multiplier M beta (beta : ℂ) = 1 := by
  unfold multiplier amplification zetaPrimeFeature
  rw [← Complex.exp_add]
  simp

private theorem analytic_multiplier (M : ℕ) (beta : ℝ) (s : ℂ) :
    AnalyticAt ℂ (multiplier M beta) s := by
  unfold multiplier amplification zetaPrimeFeature
  fun_prop

/-- Second gate: same exact matched residue at EVERY positive period,
with no approximation or loss of the prescribed source amplitude. -/
theorem tendsto_sparse_source (M : ℕ) (v : ℂ) (beta : ℝ) :
    Tendsto (fun s : ℂ => (s-(beta : ℂ))*response M v beta s)
      (𝓝[≠] (beta : ℂ)) (𝓝 v) := by
  have hf : Tendsto (multiplier M beta) (𝓝[≠] (beta : ℂ))
      (𝓝 (multiplier M beta (beta : ℂ))) :=
    (analytic_multiplier M beta (beta : ℂ)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh := hf.mul (tendsto_smooth_source v beta)
  rw [multiplier_at_source, one_mul] at hh
  convert hh using 1
  funext s
  unfold response
  ring

/-- Third gate: no hidden density pole remains at one. -/
theorem analyticAt_density (M : ℕ) (v : ℂ) {beta : ℝ} (hb : beta < 1) :
    AnalyticAt ℂ (response M v beta) 1 :=
  (analytic_multiplier M beta 1).mul
    (ArithmeticOperatorNonlinearSourceAudit.analyticAt_density v hb).1

theorem hasDensityFreeSource {M : ℕ} (hM : 0 < M) {v : ℂ} (hv : v ≠ 0)
    {beta : ℝ} (hb : beta < 1) :
    HasDensityFreeSource (sparseRow M v beta) beta v :=
  ⟨hv, response M v beta,
    (fun _ hs => (sparse_hasSum hM v beta hs).LSeriesSummable),
    (fun _ hs => (sparse_hasSum hM v beta hs).LSeries_eq),
    analyticAt_density M v hb, tendsto_sparse_source M v beta⟩

/-- The same source-preserving model obeys literal divisor incidence
at EVERY positive row, not merely one sampled packet. Its columns are
not required to be the actual positive prime/Gamma coefficients. -/
theorem divisor_realization (M : ℕ) (v : ℂ) (beta : ℝ) {n : ℕ} (hn : 0 < n) :
    divisorObservation (inverseRows (sparseRow M v beta)) n = sparseRow M v beta n :=
  observation_inverseRows _ hn

/-- One finite period makes every chosen positive lag invisible, while
the SAME nonzero source and density removal persist. This applies even
to arbitrary correlated weights depending on both endpoints. -/
theorem exists_invisible_fixed_lag_model (S : Finset ℕ) (hS : ∀ h ∈ S, 0 < h)
    {v : ℂ} (hv : v ≠ 0) {beta : ℝ} (hb : beta < 1) :
    ∃ g : ℕ → ℂ, HasDensityFreeSource g beta v ∧
      (∀ X : ℕ, ∀ W : ℕ → ℕ → ℂ, lagPacket S X W g = 0) ∧
      ∀ n > 0, divisorObservation (inverseRows g) n = g n := by
  let M := S.sup id+1
  have hM : 0 < M := by dsimp [M]; omega
  have hdiv : ∀ h ∈ S, ¬M ∣ h := by
    intro h hh hd
    have ha : M ≤ h := Nat.le_of_dvd (hS h hh) hd
    have hb : h ≤ S.sup id := Finset.le_sup (f := id) hh
    dsimp [M] at ha
    omega
  refine ⟨sparseRow M v beta,hasDensityFreeSource hM hv hb,
    fun X W => lagPacket_zero S hdiv v beta X W,?_⟩
  intro n hn
  exact divisor_realization M v beta hn

/-- A linear Mellin pole alone cannot certify a nonlinear source for
ANY finite fixed-lag code, regardless of its masks or phase choices. -/
theorem source_alone_does_not_force_fixed_lag_response (S : Finset ℕ)
    (hS : ∀ h ∈ S, 0 < h) {v : ℂ} (hv : v ≠ 0) {beta : ℝ} (hb : beta < 1) :
    ¬ (∀ g : ℕ → ℂ, HasDensityFreeSource g beta v →
      ∃ X : ℕ, ∃ W : ℕ → ℕ → ℂ, lagPacket S X W g ≠ 0) := by
  obtain ⟨g,hg,hzero,_⟩ := exists_invisible_fixed_lag_model S hS hv hb
  intro hh
  obtain ⟨X,W,he⟩ := hh g hg
  exact he (hzero X W)

private theorem sparse_pattern_zero {M : ℕ} (P : Finset ℕ)
    (hP : ∀ a ∈ P, a < M) {a b : ℕ} (ha : a ∈ P) (hb : b ∈ P) (hab : a < b)
    (v : ℂ) (beta : ℝ) (n : ℕ) (leg : ℕ → ℂ → ℂ)
    (hleg : ∀ i ∈ P, leg i 0 = 0) :
    (∏ i ∈ P, leg i (sparseRow M v beta (n+i))) = 0 := by
  classical
  by_contra hprod
  have hn (i : ℕ) (hi : i ∈ P) : sparseRow M v beta (n+i) ≠ 0 := by
    intro hz
    have hh := (Finset.prod_ne_zero_iff.mp hprod) i hi
    exact hh (by rw [hz, hleg i hi])
  have hdiv : ¬M ∣ b-a := by
    intro hd
    have hh := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hd
    have hbM := hP b hb
    omega
  have hp := sparse_pair_zero hdiv v beta (n+a)
  have he : n+a+(b-a) = n+b := by omega
  rw [he] at hp
  apply mul_ne_zero (hn a ha) (show conj (sparseRow M v beta (n+b)) ≠ 0 from
    fun he => hn b hb (by simpa using he))
  exact hp

/-- The same obstruction covers every fixed finite additive hyperedge,
not only a quadratic pair. Conjugations, positive powers and extra
phase factors are permitted through any zero-preserving leg function. -/
theorem exists_invisible_finite_pattern_model (S : Finset ℕ)
    {v : ℂ} (hv : v ≠ 0) {beta : ℝ} (hb : beta < 1) :
    ∃ g : ℕ → ℂ, HasDensityFreeSource g beta v ∧
      (∀ P : Finset ℕ, P ⊆ S → 1 < P.card → ∀ n : ℕ,
        ∀ leg : ℕ → ℂ → ℂ, (∀ i ∈ P, leg i 0 = 0) →
          (∏ i ∈ P, leg i (g (n+i))) = 0) ∧
      ∀ n > 0, divisorObservation (inverseRows g) n = g n := by
  let M := S.sup id+1
  have hM : 0 < M := by dsimp [M]; omega
  refine ⟨sparseRow M v beta,hasDensityFreeSource hM hv hb,?_,?_⟩
  · intro P hPS hcard n leg hleg
    obtain ⟨a,ha,b,hb,hne⟩ := Finset.one_lt_card.mp hcard
    have hP : ∀ a ∈ P, a < M := by
      intro a ha
      have hh : a ≤ S.sup id := Finset.le_sup (f := id) (hPS ha)
      dsimp [M]
      omega
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact sparse_pattern_zero P hP ha hb hab v beta n leg hleg
    · exact sparse_pattern_zero P hP hb ha hba v beta n leg hleg
  · intro n hn
    exact divisor_realization M v beta hn

/-- The amplitude can be the EXACT actual matched zeta residue, not
merely an arbitrary floating diagnostic constant. This remains a
countermodel to source inference, not an actual-prime replacement. -/
theorem matched_zero_does_not_force_fixed_lag_response (S : Finset ℕ)
    (hS : ∀ h ∈ S, 0 < h) (rho : NontrivialZetaZero) :
    ¬ (∀ g : ℕ → ℂ,
      HasDensityFreeSource g rho.1.re
        (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)) →
      ∃ X : ℕ, ∃ W : ℕ → ℕ → ℂ, lagPacket S X W g ≠ 0) :=
  source_alone_does_not_force_fixed_lag_response S hS
    (ArithmeticOperatorTwistSourceAudit.commutator_source_ne_zero rho)
    (NontrivialZetaZero.re_lt_one rho)

end
end RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit
