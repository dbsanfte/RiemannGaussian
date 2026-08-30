import RiemannGaussian.EtaEnergyFiniteWindowIntervalCorrelation

/-!
# Endpoint arithmetic expansion of finite eta interval correlations

This module evaluates each retained centered eta interval atom at its two
arithmetic endpoints.  Repeated integration by parts is encoded by a finite
recursive polynomial.  At a nonzero spectral parameter, the interval atom is
exactly an odd-endpoint complex power minus an even-endpoint complex power,
with the corresponding endpoint polynomials as coefficients.

The resulting finite cutoff/interval correlation is therefore rewritten as a
literal finite arithmetic correlation in the frequencies `log (2n+1)` and
`log (2n+2)`.  This expansion is propagated through the completion weights,
the diagonal and distinct-zero masses, and the terminal multiplicity-aware
rank--trace ledger.  No off-diagonal estimate is assumed or proved here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder ENNReal Interval Matrix
  Topology

namespace RiemannGaussian

noncomputable section

/-- The finite polynomial produced by repeatedly integrating the centered
monomial against a nonzero exponential rate. -/
def pairedEtaCenteredMomentEndpointPolynomial : ℕ → ℂ → ℝ → ℝ → ℂ
  | 0, s, _a, _t => s⁻¹
  | k + 1, s, a, t =>
      (((t - a : ℝ) : ℂ) ^ (k + 1)) / s +
        (((k + 1 : ℕ) : ℂ) / s) *
          pairedEtaCenteredMomentEndpointPolynomial k s a t

/-- The endpoint polynomial solves the differential recurrence needed for
the centered exponential antiderivative. -/
theorem hasDerivAt_pairedEtaCenteredMomentEndpointPolynomial
    (k : ℕ) {s : ℂ} (hs : s ≠ 0) (a t : ℝ) :
    HasDerivAt
      (fun x : ℝ => pairedEtaCenteredMomentEndpointPolynomial k s a x)
      (s * pairedEtaCenteredMomentEndpointPolynomial k s a t -
        (((t - a : ℝ) : ℂ) ^ k)) t := by
  induction k generalizing t with
  | zero =>
      simpa [pairedEtaCenteredMomentEndpointPolynomial, hs] using
        (hasDerivAt_const (x := t) (c := s⁻¹))
  | succ k ih =>
      have hu : HasDerivAt (fun x : ℝ => ((x - a : ℝ) : ℂ)) 1 t := by
        convert ((hasDerivAt_id t).sub_const a).ofReal_comp using 1 <;> simp
      have hpow := hu.pow (k + 1)
      have hfirst := hpow.div_const s
      have hsecond :=
        (ih t).const_mul (((k + 1 : ℕ) : ℂ) / s)
      convert hfirst.add hsecond using 1
      · rfl
      · funext x
        rfl
      · simp only [pairedEtaCenteredMomentEndpointPolynomial,
          Nat.add_sub_cancel, mul_one]
        field_simp [hs]
        ring

/-- An explicit antiderivative for a centered monomial times a complex
exponential. -/
def pairedEtaCenteredMomentEndpointPrimitive
    (k : ℕ) (s : ℂ) (a t : ℝ) : ℂ :=
  -Complex.exp (-s * t) *
    pairedEtaCenteredMomentEndpointPolynomial k s a t

/-- The endpoint primitive differentiates to the centered complex Laplace
integrand at every nonzero rate. -/
theorem hasDerivAt_pairedEtaCenteredMomentEndpointPrimitive
    (k : ℕ) {s : ℂ} (hs : s ≠ 0) (a t : ℝ) :
    HasDerivAt
      (fun x : ℝ => pairedEtaCenteredMomentEndpointPrimitive k s a x)
      ((((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)) t := by
  have hinner : HasDerivAt (fun x : ℝ => -s * (x : ℂ)) (-s) t := by
    simpa only [mul_one] using!
      ((hasDerivAt_id (t : ℂ)).const_mul (-s)).comp_ofReal
  have hexp := (Complex.hasDerivAt_exp _).comp t hinner
  have hmul := hexp.neg.mul
    (hasDerivAt_pairedEtaCenteredMomentEndpointPolynomial k hs a t)
  convert hmul using 1
  · rfl
  · funext x
    rfl
  · simp [Function.comp_apply, neg_mul]
    ring

/-- A centered exponential moment on a finite interval is the exact
difference of its two explicit endpoint primitives. -/
theorem intervalIntegral_centered_cpow_mul_cexp_neg_mul_eq_endpointPrimitive_sub
    (k : ℕ) {s : ℂ} (hs : s ≠ 0) (a lower upper : ℝ) :
    (∫ t : ℝ in lower..upper,
      (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)) =
        pairedEtaCenteredMomentEndpointPrimitive k s a upper -
          pairedEtaCenteredMomentEndpointPrimitive k s a lower := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _ht
    exact hasDerivAt_pairedEtaCenteredMomentEndpointPrimitive k hs a t
  · exact (show Continuous (fun t : ℝ =>
        (((t - a : ℝ) : ℂ) ^ k) * Complex.exp (-s * t)) by
      fun_prop).intervalIntegrable _ _

/-- Exponentiating minus a complex rate times the logarithm of a positive
natural number gives its literal complex power. -/
theorem cexp_neg_mul_log_nat_eq_cpow
    (s : ℂ) {q : ℕ} (hq : 0 < q) :
    Complex.exp (-s * Real.log q) = ((q : ℝ) : ℂ) ^ (-s) := by
  have hqNonneg : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hqNe : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  rw [Complex.cpow_def_of_ne_zero hqNe,
    ← Complex.ofReal_log hqNonneg]
  congr 1
  push_cast
  ring

/-- The fully evaluated arithmetic form of one centered retained eta
interval atom. -/
def pairedEtaLogLaplaceCenteredMomentArithmeticAtom
    (k : ℕ) (s : ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  (((2 * n + 1 : ℕ) : ℝ) : ℂ) ^ (-s) *
      pairedEtaCenteredMomentEndpointPolynomial k s a
        (Real.log (2 * n + 1)) -
    (((2 * n + 2 : ℕ) : ℝ) : ℂ) ^ (-s) *
      pairedEtaCenteredMomentEndpointPolynomial k s a
        (Real.log (2 * n + 2))

/-- Every centered retained eta interval integral equals its explicit odd
minus even arithmetic endpoint form at a nonzero rate. -/
theorem pairedEtaLogLaplaceCenteredMomentIntervalAtom_eq_arithmeticAtom
    (k : ℕ) {s : ℂ} (hs : s ≠ 0) (a : ℝ) (n : ℕ) :
    pairedEtaLogLaplaceCenteredMomentIntervalAtom k s a n =
      pairedEtaLogLaplaceCenteredMomentArithmeticAtom k s a n := by
  unfold pairedEtaLogLaplaceCenteredMomentIntervalAtom
  rw [
    intervalIntegral_centered_cpow_mul_cexp_neg_mul_eq_endpointPrimitive_sub
      k hs]
  unfold pairedEtaCenteredMomentEndpointPrimitive
    pairedEtaLogLaplaceCenteredMomentArithmeticAtom
  have hodd :=
    cexp_neg_mul_log_nat_eq_cpow s (show 0 < 2 * n + 1 by omega)
  have heven :=
    cexp_neg_mul_log_nat_eq_cpow s (show 0 < 2 * n + 2 by omega)
  norm_num [Nat.cast_add, Nat.cast_mul] at hodd heven
  simp only [neg_mul]
  rw [hodd, heven]
  push_cast
  ring

/-- The arithmetic endpoint atom for the top-prefix centered moment at one
genuine nontrivial zeta zero. -/
def pairedEtaTopPrefixFiniteCenteredArithmeticAtom
    (rho : NontrivialZetaZero) (N n : ℕ) : ℂ :=
  pairedEtaLogLaplaceCenteredMomentArithmeticAtom
    (analyticZetaZeroMultiplicity rho - 1) rho.1
      (pairedEtaLogTailCutoff (N + 1)) n

/-- A top-prefix interval atom equals its explicit arithmetic endpoint form.
-/
theorem pairedEtaTopPrefixFiniteCenteredIntervalAtom_eq_arithmeticAtom
    (rho : NontrivialZetaZero) (N n : ℕ) :
    pairedEtaTopPrefixFiniteCenteredIntervalAtom rho N n =
      pairedEtaTopPrefixFiniteCenteredArithmeticAtom rho N n := by
  unfold pairedEtaTopPrefixFiniteCenteredIntervalAtom
    pairedEtaTopPrefixFiniteCenteredArithmeticAtom
  exact pairedEtaLogLaplaceCenteredMomentIntervalAtom_eq_arithmeticAtom
    (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.coe_ne_zero rho)
      (pairedEtaLogTailCutoff (N + 1)) n

/-- Every top-prefix centered moment is a finite sum of explicit odd--even
endpoint arithmetic atoms. -/
theorem pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_arithmeticAtoms
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaTopPrefixFiniteCenteredMoment rho N =
      ∑ n ∈ Finset.range (N + 1),
        pairedEtaTopPrefixFiniteCenteredArithmeticAtom rho N n := by
  rw [pairedEtaTopPrefixFiniteCenteredMoment_eq_sum_intervalAtoms]
  apply Finset.sum_congr rfl
  intro n _hn
  exact pairedEtaTopPrefixFiniteCenteredIntervalAtom_eq_arithmeticAtom
    rho N n

/-- The explicit odd--even endpoint expansion of the uncompleted finite eta
moment correlation. -/
def pairedEtaTopPrefixFiniteCutoffFamilyArithmeticCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  ∑ j,
    ∑ n ∈ Finset.range (cutoff j + 1),
      ∑ m ∈ Finset.range (cutoff j + 1),
        starRingEnd ℂ
            (pairedEtaTopPrefixFiniteCenteredArithmeticAtom
              sigma (cutoff j) n) *
          pairedEtaTopPrefixFiniteCenteredArithmeticAtom
            rho (cutoff j) m

/-- The literal interval correlation equals its fully evaluated finite
odd--even endpoint arithmetic correlation. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation_eq_arithmeticCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyArithmeticCorrelation
        cutoff sigma rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyArithmeticCorrelation
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  rw [pairedEtaTopPrefixFiniteCenteredIntervalAtom_eq_arithmeticAtom,
    pairedEtaTopPrefixFiniteCenteredIntervalAtom_eq_arithmeticAtom]

/-- The reflection coupling after evaluating every retained interval at its
odd and even arithmetic endpoints. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionArithmeticCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) : ℂ :=
  starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCompletionWeight
          (NontrivialZetaZero.conjugatePartner sigma)) *
      pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho) *
      pairedEtaTopPrefixFiniteCutoffFamilyArithmeticCorrelation cutoff
        (NontrivialZetaZero.conjugatePartner sigma)
        (NontrivialZetaZero.conjugatePartner rho) +
    pairedEtaTopPrefixFiniteCompletionWeight sigma *
      starRingEnd ℂ (pairedEtaTopPrefixFiniteCompletionWeight rho) *
      starRingEnd ℂ
        (pairedEtaTopPrefixFiniteCutoffFamilyArithmeticCorrelation
          cutoff sigma rho)

/-- The interval-expanded reflection coupling equals its fully evaluated
arithmetic endpoint form. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation_eq_arithmeticCorrelation
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (sigma rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
        cutoff sigma rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionArithmeticCorrelation
        cutoff sigma rho := by
  unfold
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionArithmeticCorrelation
  rw [
    pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation_eq_arithmeticCorrelation,
    pairedEtaTopPrefixFiniteCutoffFamilyIntervalCorrelation_eq_arithmeticCorrelation]

/-- The completion-weighted self-mass with each centered moment displayed as
a finite sum of evaluated odd--even endpoint atoms. -/
def pairedEtaTopPrefixFiniteCutoffFamilyWeightedArithmeticSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) : ℝ :=
  ∑ j,
    (‖pairedEtaTopPrefixFiniteCompletionWeight
        (NontrivialZetaZero.conjugatePartner rho)‖ ^ 2 *
      ‖∑ n ∈ Finset.range (cutoff j + 1),
        pairedEtaTopPrefixFiniteCenteredArithmeticAtom
          (NontrivialZetaZero.conjugatePartner rho) (cutoff j) n‖ ^ 2 +
    ‖pairedEtaTopPrefixFiniteCompletionWeight rho‖ ^ 2 *
      ‖∑ n ∈ Finset.range (cutoff j + 1),
        pairedEtaTopPrefixFiniteCenteredArithmeticAtom
          rho (cutoff j) n‖ ^ 2)

/-- The interval-expanded self-mass equals its evaluated arithmetic endpoint
form. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass_eq_arithmeticSelfMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ)
    (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass cutoff rho =
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedArithmeticSelfMass
        cutoff rho := by
  unfold pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedArithmeticSelfMass
  simp_rw [pairedEtaTopPrefixFiniteCenteredIntervalAtom_eq_arithmeticAtom]

/-- The diagonal finite-window mass in fully evaluated odd--even arithmetic
endpoint form. -/
def pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  4 * ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℝ) ^ 2 *
      pairedEtaTopPrefixFiniteCutoffFamilyWeightedArithmeticSelfMass
        cutoff rho ^ 2

/-- The signed distinct-zero mass in fully evaluated odd--even arithmetic
endpoint correlation form. -/
def pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ∑ sigma ∈ (spectralZetaZeroWindow T).erase rho,
      ((((analyticZetaZeroMultiplicity rho : ℝ) *
          (analyticZetaZeroMultiplicity sigma : ℝ) : ℝ) : ℂ) *
        (2 *
          pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionArithmeticCorrelation
            cutoff sigma rho) ^ 2).re

/-- The interval-expanded diagonal mass equals its evaluated arithmetic
endpoint form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass_eq_arithmeticMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
        cutoff T := by
  unfold pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
  apply congrArg (4 * ·)
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedIntervalSelfMass_eq_arithmeticSelfMass]

/-- The interval-expanded distinct-zero mass equals its evaluated arithmetic
endpoint correlation form. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass_eq_arithmeticMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
        cutoff T := by
  unfold
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  rw [
    pairedEtaTopPrefixFiniteCutoffFamilyWeightedReflectionIntervalCorrelation_eq_arithmeticCorrelation]

/-- The coherent finite eta Frobenius mass is exactly the sum of its fully
evaluated arithmetic endpoint diagonal and distinct-zero terms. -/
theorem pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_arithmeticDiagonal_add_offDiagonal
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
          cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
          cutoff T := by
  rw [
    pairedEtaTopPrefixFiniteZeroWindowCoherentFrobeniusMass_eq_intervalDiagonal_add_offDiagonal,
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass_eq_arithmeticMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass_eq_arithmeticMass]

/-- The multiplicity-aware eta rank--trace ledger with every retained
interval evaluated into explicit odd--even endpoint complex powers and finite
polynomial coefficients. -/
theorem pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_arithmeticCorrelation_ledger
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    4 * (pairedEtaTopPrefixFiniteZeroWindowOnLineTraceMass cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineTraceMass cutoff T) -
      pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedArithmeticMass
        cutoff T -
      pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedArithmeticMass
        cutoff T ≤
        pairedEtaTopPrefixFiniteZeroWindowCriticalMultiplicityPenalty
          cutoff T 2 +
        4 * (spectralUpperZetaZeroWindow T).card := by
  have h :=
    pairedEtaTopPrefixFiniteZeroWindow_multiplicityRankTrace_two_intervalCorrelation_ledger
      cutoff hT
  rw [
    pairedEtaTopPrefixFiniteZeroWindowDiagonalWeightedIntervalMass_eq_arithmeticMass,
    pairedEtaTopPrefixFiniteZeroWindowOffDiagonalWeightedIntervalMass_eq_arithmeticMass]
    at h
  exact h

end

end RiemannGaussian
