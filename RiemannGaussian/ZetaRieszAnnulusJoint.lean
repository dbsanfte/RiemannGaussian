/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAnnulusCompletion

/-!
# The joint completed Riesz carrier with its full signed source

The whole actual annulus splits exactly into the all-subcutoff class
and the cross-prime class. Completing the latter retains the finite
physical prefix beside the first class. The total representation error
has an independent geometric bound on 1/2<=u<exp(-2/3). At exposed zeros
in this interval, the full negative multiplicity source survives.
The independent joint cofinal floor remains open; RH is not proved.
-/

namespace RiemannGaussian.ZetaRieszAnnulusJoint
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszCrossSupport
open ZetaRieszAnnulusCompletion ZetaRieszLowerDegreeBounds
open ZetaRieszPhysicalAnnulus

/-- All prime cofactors strictly between the quadratic and physical
cutoffs, with no selection of numerical coefficients or frequencies. -/
def intermediatePrimes (u : ℝ) (N : ℕ) : Finset ℕ :=
  (Nat.primesLE ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 - 1)).filter
    (fun a => N ^ 2 < a)

/-- The full intermediate prime set has exactly its declared strict
endpoints; the physical prime cutoff is not rounded a second time. -/
theorem mem_intermediatePrimes (u : ℝ) (N a : ℕ) :
    a ∈ intermediatePrimes u N ↔ a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  have hX : 0 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by positivity
  simp only [intermediatePrimes, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hNa⟩
    have h := Nat.mem_primesLE.mp ha
    exact ⟨h.2, hNa, by omega⟩
  · rintro ⟨ha, hNa, haX⟩
    exact ⟨Nat.mem_primesLE.mpr ⟨by omega, ha⟩, hNa⟩

/-- At each original annular label the coefficient splits exactly into
its all-subcutoff class and its uniquely counted cross-prime class. -/
theorem coefficient_eq_subcutoff_add_cross {u : ℝ} {N n : ℕ}
    (hu : u < Real.exp (-(2 / 3 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : n ∈ annulusBand u N) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n =
      (if ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 then
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0) +
      crossCoefficient (intermediatePrimes u N) u N n := by
  by_cases hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n = 0
  · simp only [hc, ite_self, crossCoefficient, zero_add]
  by_cases hs : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  · have hcross : ¬ (crossIncidences (intermediatePrimes u N) u N n).Nonempty := by
      rintro ⟨a, ha⟩
      obtain ⟨haA, had, hp, hXp⟩ := Finset.mem_filter.mp ha
      have ha' := (mem_intermediatePrimes u N a).mp haA
      have he : n / a * a = n := Nat.div_mul_cancel had
      have hn0 : n ≠ 0 := by rw [← he]; exact mul_ne_zero hp.ne_zero ha'.1.ne_zero
      have hd : n / a ∣ n := (dvd_mul_right (n / a) a).trans (dvd_of_eq he)
      exact (hs (n / a) (Nat.mem_primeFactors.mpr ⟨hp, hd, hn0⟩)).not_ge hXp
    simp only [if_pos hs, crossCoefficient, if_neg hcross, add_zero]
  · obtain ⟨a, p, ha, hp, hNa, haX, hXp, he, _⟩ :=
      (annulus_support_dichotomy hu hNX hn hc).resolve_left hs
    have haA := (mem_intermediatePrimes u N a).mpr ⟨ha, hNa, haX⟩
    have had : a ∣ n := by rw [he]; exact dvd_mul_left a p
    have hquot : n / a = p := by rw [he, mul_comm p a, Nat.mul_div_cancel_left _ ha.pos]
    have hcross : (crossIncidences (intermediatePrimes u N) u N n).Nonempty := by
      refine ⟨a, Finset.mem_filter.mpr ⟨haA, had, ?_, ?_⟩⟩ <;> simpa only [hquot]
    simp only [if_neg hs, crossCoefficient, if_pos hcross, zero_add]

/-- The surviving all-subcutoff contribution keeps every prior support
cut, the original coefficient and the full phase of its actual integer. -/
def subcutoffResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (annulusBand u N).filter (fun n => ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2),
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The whole original annular response is the exact sum of the two
surviving prime classes, with no norm or phase loss between them. -/
theorem annulusResponse_eq_split (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    (hu : u < Real.exp (-(2 / 3 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u =
      subcutoffResponse P u y N + ∑ n ∈ annulusBand u N,
        crossCoefficient (intermediatePrimes u N) u N n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  simp only [annulusResponse, subcutoffResponse, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  conv_lhs => rw [coefficient_eq_subcutoff_add_cross hu hNX hn, add_mul]
  congr 1
  split_ifs <;> simp

/-- The completed whole carrier keeps the all-subcutoff contribution
coupled to the completed prime head MINUS its full physical prefix. -/
def jointResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  subcutoffResponse P u y N + completedCross (intermediatePrimes u N) P u y N

/-- The complete change of representation has an independent geometric
error, uniformly in height and every fixed polynomial filter. The joint
signed floor is still an arithmetic obligation, not a hypothesis here. -/
theorem eventually_norm_joint_sub_annulus_le (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      ‖(u : ℂ) ^ (N + 1) * (jointResponse P u y N -
        annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u)‖ ≤
      degreeRate 2 (2 / 3) (3 / 8) (257 / 256) ^ N *
        (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256)) := by
  have hA := fun N a ha => (mem_intermediatePrimes u N a).mp ha
  have hb := eventually_norm_annulus_completion_error_le (intermediatePrimes u) P y hu huh hA
  have hu0 : 0 < u := by linarith
  have hu1 : u < 1 := huh.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  filter_upwards [hb, ZetaRieszSemiprimeSupport.eventually_quadratic_head_lt_physical hu0 hu1]
    with N hN hNX
  rw [annulusResponse_eq_split P u y N huh hNX, jointResponse]
  convert hN using 1
  congr 1
  ring

/-- Completing the entire cross-prime class, while retaining its prefix
beside the all-subcutoff contribution, has vanishing source-normalized error. -/
theorem tendsto_joint_sub_annulus (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * (jointResponse P u y N -
      annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_joint_sub_annulus_le P y hu huh)
  have hr0 : 0 ≤ degreeRate 2 (2 / 3) (3 / 8) (257 / 256) := by unfold degreeRate; positivity
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 two_degree_rate_lt_one).mul_const
      (u * ZetaArithmeticLogWindow.tiltConstant P (3 / 8) (257 / 256))

/-- At an exposed right-half zero in the physical-annulus source range,
the completed JOINT arithmetic response retains exactly the whole negative
multiplicity source. No floor or cancellation for its separate parts follows. -/
theorem tendsto_jointResponse_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      jointResponse 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_joint_sub_annulus 1 rho.1.im hu huh).add
    (tendsto_normalizedAnnulus rho hrho hexposed)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedAnnulus
  ring

end
end RiemannGaussian.ZetaRieszAnnulusJoint
