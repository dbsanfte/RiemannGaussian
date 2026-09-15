/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMatchedMiddle

/-!
# Retaining the endpoint cancellation in reflected head/pair orders

The exact reflected pair exposes a linearly vanishing prime weight. Its
independent norm estimate saves the physical length before the remaining
prime phase or completion errors are discarded.
-/

namespace RiemannGaussian.ZetaRieszEndpointTaper
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint ZetaExposedPrimeMoments
open ZetaRieszMatchedMiddle ZetaPrimeCofactorCompletion
open ZetaRieszHeadOrders

/-- The signed endpoint weight before restricting to physical primes. -/
def endpointWeight (L x : ℝ) : ℝ := 1 - x / L

/-- The exact physical endpoint is a zero of the retained weight. -/
theorem endpointWeight_self {L : ℝ} (hL : L ≠ 0) : endpointWeight L L = 0 := by
  simp [endpointWeight, hL]

/-- Every actual intermediate prime has a positive endpoint weight
bounded by one, with both original physical endpoints retained. -/
theorem actual_endpointWeight_bounds (u : ℝ) (N p : ℕ)
    (hp : p ∈ intermediatePrimes u N) :
    0 < endpointWeight (SquarefreeVaughanLogSource.length u N) (Real.log p) ∧
      endpointWeight (SquarefreeVaughanLogSource.length u N) (Real.log p) ≤ 1 := by
  obtain ⟨hprime, _, hpX⟩ := (mem_intermediatePrimes u N p).mp hp
  have hlog : Real.log p < SquarefreeVaughanLogSource.length u N :=
    Real.log_lt_log (by exact_mod_cast hprime.pos)
      (by exact_mod_cast hpX)
  have hL := SquarefreeVaughanLogSource.length_pos u N
  unfold endpointWeight
  constructor
  · have h := (div_lt_one hL).mpr hlog
    linarith
  · exact sub_le_self _ (div_nonneg (Real.log_natCast_nonneg p) hL.le)

/-- The literal finite prime moment with the head's vanishing endpoint
weight, preserving the full complex phase of each prime. -/
def taperedMoment (A : Finset ℕ) (k : ℕ) (s : ℂ) (L : ℝ) : ℂ :=
  ∑ p ∈ A, (endpointWeight L (Real.log p) : ℂ) * zetaPrimeLogKernel k s p

/-- The adjacent derivative subtraction is exactly endpoint tapering,
including its factorial multiplier and original physical length. -/
theorem taperedMoment_eq (A : Finset ℕ) (k : ℕ) (s : ℂ) (L : ℝ) :
    taperedMoment A k s L = finiteMoment A k s -
      ((k + 1 : ℕ) : ℂ) / (L : ℂ) * finiteMoment A (k + 1) s := by
  calc
    _ = finiteMoment A k s - (1 / (L : ℂ)) * cofactorMoment A k s := by
      simp only [taperedMoment, finiteMoment, cofactorMoment, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      unfold endpointWeight
      push_cast
      ring
    _ = _ := by rw [cofactorMoment_eq_succ]; ring

/-- Reflecting the two orders retains a tapered high leg, a complete
head product, and the two exact low-leg completion errors. No error term
or prime product phase is silently dropped. -/
theorem reflected_sharedAtom_eq (u y : ℝ) (N k l : ℕ) :
    sharedAtom u y N k l + sharedAtom u y N l k =
      ordinaryPrimeMoment k (3 / 2 + Complex.I * y) *
        taperedMoment (intermediatePrimes u N) l (3 / 2 + Complex.I * y)
          (SquarefreeVaughanLogSource.length u N) -
      ((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
        ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y) *
          ordinaryPrimeMoment l (3 / 2 + Complex.I * y) +
      (finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) -
        ordinaryPrimeMoment k (3 / 2 + Complex.I * y)) *
          finiteMoment (intermediatePrimes u N) l (3 / 2 + Complex.I * y) -
      ((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
        (finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) -
          ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y)) *
            ordinaryPrimeMoment l (3 / 2 + Complex.I * y) := by
  rw [taperedMoment_eq]
  unfold sharedAtom
  ring

/-- A vanishing endpoint weight saves one factor of the physical
length in every positive exponential tilt, without using oscillation. -/
theorem endpointWeight_mul_exp_le {a L : ℝ} (ha : 0 < a) (hL : 0 < L) (x : ℝ) :
    endpointWeight L x * Real.exp (a * x) ≤ Real.exp (a * L) / (a * L) := by
  have h : a * (L - x) ≤ Real.exp (a * (L - x)) := by
    linarith [Real.add_one_le_exp (a * (L - x))]
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (a * x)).le
  have he : Real.exp (a * (L - x)) * Real.exp (a * x) = Real.exp (a * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  apply (le_div_iff₀ (mul_pos ha hL)).mpr
  have hi : endpointWeight L x * Real.exp (a * x) * (a * L) =
      a * (L - x) * Real.exp (a * x) := by
    unfold endpointWeight
    field_simp
  rw [hi]
  exact hm

/-- An independent height-uniform norm bound for the whole tapered
moment. The inverse physical-length saving comes from the retained head
subtraction, before any prime phases are bounded. -/
theorem norm_taperedMoment_le (A : Finset ℕ) (k : ℕ) (y : ℝ)
    {L q sigma : ℝ} (hL : 0 < L) (hq : 0 < q) (hsigma : 1 < sigma)
    (ha : 0 < q + sigma - 3 / 2) (hA : ∀ p ∈ A, Real.log p ≤ L) :
    ‖taperedMoment A k (3 / 2 + Complex.I * y) L‖ ≤
      (q⁻¹ ^ k * (Real.exp ((q + sigma - 3 / 2) * L) /
        ((q + sigma - 3 / 2) * L))) * ∑' n, zetaPrimeExpWeight sigma n := by
  let a : ℝ := q + sigma - 3 / 2
  have ha0 : 0 < a := ha
  have hs : (3 / 2 + Complex.I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have hb (p : ℕ) (hp : p ∈ A) :
      ‖(endpointWeight L (Real.log p) : ℂ) * zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p‖ ≤
        (q⁻¹ ^ k * (Real.exp (a * L) / (a * L))) * zetaPrimeExpWeight sigma p := by
    have hw : 0 ≤ endpointWeight L (Real.log p) := by
      have h := (div_le_one hL).mpr (hA p hp)
      dsimp only [endpointWeight]
      linarith
    have hk := norm_zetaPrimeLogKernel_le k (3 / 2 + Complex.I * (y : ℂ)) p hq
    rw [hs] at hk
    have he : zetaPrimeExpWeight (3 / 2 - q) p =
        Real.exp (a * Real.log p) * zetaPrimeExpWeight sigma p := by
      unfold zetaPrimeExpWeight
      rw [← Real.exp_add]
      congr 1
      dsimp only [a]
      ring
    rw [he] at hk
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    calc
      _ ≤ endpointWeight L (Real.log p) *
          (q⁻¹ ^ k * (Real.exp (a * Real.log p) * zetaPrimeExpWeight sigma p)) :=
        mul_le_mul_of_nonneg_left hk hw
      _ = (q⁻¹ ^ k * (endpointWeight L (Real.log p) * Real.exp (a * Real.log p))) *
          zetaPrimeExpWeight sigma p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (endpointWeight_mul_exp_le ha0 hL (Real.log p)) (by positivity))
        (Real.exp_pos _).le
  unfold taperedMoment
  calc
    _ ≤ ∑ p ∈ A, ‖(endpointWeight L (Real.log p) : ℂ) *
        zetaPrimeLogKernel k (3 / 2 + Complex.I * y) p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ A, (q⁻¹ ^ k * (Real.exp (a * L) / (a * L))) * zetaPrimeExpWeight sigma p :=
      Finset.sum_le_sum hb
    _ = (q⁻¹ ^ k * (Real.exp (a * L) / (a * L))) * ∑ p ∈ A, zetaPrimeExpWeight sigma p := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight hsigma).sum_le_tsum A (fun p _ => (Real.exp_pos _).le)) (by positivity)

/-- The taper bound applies to the actual physical prime array without
changing a cutoff or adding any hypothetical-zero premise. -/
theorem norm_actual_taperedMoment_le (u y : ℝ) (N k : ℕ)
    {q sigma : ℝ} (hq : 0 < q) (hsigma : 1 < sigma) (ha : 0 < q + sigma - 3 / 2) :
    ‖taperedMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y)
      (SquarefreeVaughanLogSource.length u N)‖ ≤
      (q⁻¹ ^ k * (Real.exp ((q + sigma - 3 / 2) * SquarefreeVaughanLogSource.length u N) /
        ((q + sigma - 3 / 2) * SquarefreeVaughanLogSource.length u N))) *
          ∑' n, zetaPrimeExpWeight sigma n := by
  apply norm_taperedMoment_le _ _ _ (SquarefreeVaughanLogSource.length_pos u N) hq hsigma ha
  intro p hp
  have hw := (actual_endpointWeight_bounds u N p hp).1
  dsimp only [endpointWeight] at hw
  exact ((div_lt_one (SquarefreeVaughanLogSource.length_pos u N)).mp (by linarith)).le

end
end RiemannGaussian.ZetaRieszEndpointTaper
