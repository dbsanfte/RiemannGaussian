/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianFermiPoleFormula

/-!
# A Fermi zero budget for every finite nonnegative phase test

The common positive Fermi prime amplitude lets every nonnegative cosine
test remove the entire prime series with its sign intact. A selected finite
set of genuine zeros stays in the resulting budget, with every other zero
in the known height band nonnegative and the full outside divisor paid for
by the proved allowance. No coefficients or improved exclusion constants
are selected in this general theorem.
-/

namespace RiemannGaussian.GaussianFermiPhaseBudget

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology Classical
open GaussianFermiSpectralWeight GaussianFermiCosineAverage GaussianFermiPrimeFormula
open GaussianFermiPoleFormula GaussianFermiZeroTail GaussianFermiMovingAllowance

/-- All frequencies retain one common positive prime amplitude. The
`HasSum` statement also justifies the finite-phase/infinite-prime exchange. -/
theorem hasSum_prime_phase {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (t : ℝ) :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      signal a B (Real.log n) *
        (∑ j ∈ J, w j * Real.cos (ω j * (t * Real.log n))))
      (∑ j ∈ J, w j * primeSum a B (ω j * t)) := by
  have hs := hasSum_sum (s := J) fun j _ =>
    ((summable_primeSummand ha hB (ω j * t)).hasSum).mul_left (w j)
  apply hs.congr_fun
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold primeSummand
  rw [mul_assoc (ω j) t (Real.log n)]
  ring

/-- Every finite nonnegative cosine test gives a nonnegative literal
Fermi prime combination. Positivity is used after phase recombination. -/
theorem prime_phase_nonneg {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x)) (t : ℝ) :
    0 ≤ ∑ j ∈ J, w j * primeSum a B (ω j * t) := by
  rw [← (hasSum_prime_phase J w ω ha hB t).tsum_eq]
  apply tsum_nonneg
  intro n
  exact mul_nonneg (mul_nonneg (by positivity) (signal_pos a B _).le) (hphase _)

/-- The repository's exact contact family is an available instance of the
general prime-positivity theorem, with no numerical fitting. -/
theorem exact_contact_prime_phase_nonneg {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (t : ℝ) :
    0 ≤ ∑ j : Fin 9, phaseContactExactCoefficients j *
      primeSum a B ((phaseContactFrequency j : ℝ) * t) := by
  apply prime_phase_nonneg Finset.univ phaseContactExactCoefficients
    (fun j => (phaseContactFrequency j : ℝ)) ha hB ?_ t
  intro x
  have h := phaseContactExactFamily_kernel_nonneg x
  rwa [phaseContactExactFamily, phaseContactFrequencyFamily_kernel] at h

/-- The full actual zero sum splits exactly into its finite band and
outside divisor, before either is estimated. -/
theorem zero_sum_eq_inside_add_outside {B σ H t : ℝ} (hB : 0 < B)
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hscale : (1 - σ) ^ 2 ≤ B)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H) :
    (∑' ρ : NontrivialZetaZero, contribution B σ t ρ) =
      (∑' ρ : NontrivialZetaZero, inside B σ t H ρ) +
      (∑' ρ : NontrivialZetaZero, outside B σ t H ρ) := by
  have hin : Summable (inside B σ t H) :=
    summable_of_hasFiniteSupport (finite_support_inside B σ t (by linarith))
  have hout := summable_outside hB hσ0 hσ1 hscale ht hH
  rw [← hin.tsum_add hout]
  apply tsum_congr
  intro ρ
  dsimp [inside, outside]
  by_cases hρ : |ρ.1.im| ≤ H
  · simp [hρ, not_lt.mpr hρ]
  · simp [hρ, lt_of_not_ge hρ]

/-- Any finite collection of genuine zeros in the height band remains
visible, with analytic multiplicity, while the entire omitted divisor is
bounded by the existing allowance. -/
theorem selected_zero_sum_le_full_add_allowance {B H t : ℝ} (hB : 0 < B)
    (ht : 2 * |t| ≤ H) (hH : 1 ≤ H)
    (hscale : zetaPoleReserveZeroMargin H ^ 2 ≤ B)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    (∑ ρ ∈ S, contribution B (1 - zetaPoleReserveZeroMargin H) t ρ) ≤
      (∑' ρ : NontrivialZetaZero, contribution B (1 - zetaPoleReserveZeroMargin H) t ρ) +
        allowance B H := by
  let σ := 1 - zetaPoleReserveZeroMargin H
  have hm := zetaPoleReserveZeroMargin_bounds H
  have hσ0 : 1 / 2 ≤ σ := by dsimp [σ]; linarith [hm.2]
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith [hm.1]
  have hscale' : (1 - σ) ^ 2 ≤ B := by simpa [σ] using hscale
  have hin : Summable (inside B σ t H) :=
    summable_of_hasFiniteSupport (finite_support_inside B σ t (by linarith))
  have hsel : (∑ ρ ∈ S, contribution B σ t ρ) ≤
      ∑' ρ : NontrivialZetaZero, inside B σ t H ρ := by
    calc
      _ = ∑ ρ ∈ S, inside B σ t H ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        simp only [inside, if_pos (hS ρ hρ)]
      _ ≤ _ := hin.sum_le_tsum S (fun ρ _ => inside_nonneg hB H t ρ)
  have htail := (abs_le.mp (abs_tsum_outside_le hB hσ0 hσ1 hscale' ht hH)).1
  have he : 4 * GaussianFermiDerivativeBounds.integralCost (2 * σ - 1) B (1 - σ) *
      divisorTail H = allowance B H := by
    unfold allowance
    dsimp only [σ]
    rw [show 2 * (1 - zetaPoleReserveZeroMargin H) - 1 =
      1 - 2 * zetaPoleReserveZeroMargin H by ring, sub_sub_cancel]
  rw [he] at htail
  have hsplit := zero_sum_eq_inside_add_outside hB hσ0 hσ1 hscale' ht hH
  change (∑ ρ ∈ S, contribution B σ t ρ) ≤ _
  change _ ≤ (∑' ρ : NontrivialZetaZero, contribution B σ t ρ) + allowance B H
  linarith

/-- A general finite-phase budget for any retained finite zero set. The
entire prime series has the favorable sign by the actual common Fermi
weight. Every remaining term is an explicit pole, gamma average, or proved
outside allowance; no arithmetic cancellation estimate is assumed. -/
theorem selected_zero_phase_budget {ι : Type*} (J : Finset ι) (w ω : ι → ℝ)
    (hw : ∀ j ∈ J, 0 ≤ w j)
    (hphase : ∀ x : ℝ, 0 ≤ ∑ j ∈ J, w j * Real.cos (ω j * x))
    {H b c t : ℝ} (hH : 1 ≤ H) (hb : 0 < b) (hc : 0 < c)
    (hscale : zetaPoleReserveZeroMargin H ^ 2 ≤ b + c)
    (ht : ∀ j ∈ J, 2 * |ω j * t| ≤ H)
    (S : Finset NontrivialZetaZero) (hS : ∀ ρ ∈ S, |ρ.1.im| ≤ H) :
    let σ := 1 - zetaPoleReserveZeroMargin H;
    (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤
      (∑ j ∈ J, w j * (polePair (b + c) σ (ω j * t) - Real.log Real.pi / 4 +
        digammaAverage (2 * σ - 1) b c (ω j * t))) +
      (∑ j ∈ J, w j) * allowance (b + c) H := by
  let σ := 1 - zetaPoleReserveZeroMargin H
  change (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤ _
  have hσ : 1 / 2 ≤ σ := by
    dsimp [σ]
    linarith [(zetaPoleReserveZeroMargin_bounds H).2]
  have ha : 0 ≤ 2 * σ - 1 := by linarith
  have hbound : (∑ j ∈ J, w j * (∑ ρ ∈ S, contribution (b + c) σ (ω j * t) ρ)) ≤
      ∑ j ∈ J, w j * ((∑' ρ : NontrivialZetaZero, contribution (b + c) σ (ω j * t) ρ) +
        allowance (b + c) H) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (selected_zero_sum_le_full_add_allowance (add_pos hb hc) (ht j hj) hH hscale S hS)
      (hw j hj)
  simp_rw [zero_side_eq_poles_digamma_sub_prime hb hc hσ, mul_add, mul_sub] at hbound
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul] at hbound
  have hp := prime_phase_nonneg J w ω ha (add_pos hb hc) hphase t
  linarith

end
end RiemannGaussian.GaussianFermiPhaseBudget
