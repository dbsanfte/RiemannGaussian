/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOffDiagonalJoint
import RiemannGaussian.ZetaRieszMixedPrefix

/-!
# Removing the mixed prefix from the whole signed carrier

The mixed and diagonal integer classes are disjoint and lie in the
actual finite prefix. Their exact deletion preserves the full exposed-zero
source in the annular interval. The completed head and the remaining
subcutoff and distinct-prime contributions stay coupled.
-/

namespace RiemannGaussian.ZetaRieszMixedPrefixTransport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszAnnulusJoint
open ZetaRieszMixedPrefix ZetaRieszOffDiagonalJoint

/-- Every mixed product is in the literal finite physical prefix. -/
theorem mixedLabels_subset_range (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    mixedLabels A N ⊆
      Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) := by
  intro n hn
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  obtain ⟨hpN, _hp⟩ := Nat.mem_primesLE.mp hp
  have ha' := hA a ha
  have hpX := hpN.trans_lt (ha'.2.1.trans ha'.2.2)
  have hX0 : 0 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by positivity
  have hprod := (Nat.mul_lt_mul_of_pos_left hpX ha'.1.pos).trans
    (Nat.mul_lt_mul_of_pos_right ha'.2.2 hX0)
  apply Finset.mem_range.mpr
  simpa only [pow_two] using hprod

/-- A mixed product cannot be a selected prime square: its small prime
divisor would then equal a prime strictly above the same head. -/
theorem mixedLabels_disjoint_diagonal (A : Finset ℕ) (u : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    Disjoint (mixedLabels A N) (A.image (fun p => p ^ 2)) := by
  apply Finset.disjoint_left.mpr
  intro n hn hd
  obtain ⟨⟨a, p⟩, hap, he⟩ := Finset.mem_image.mp hn
  obtain ⟨_ha, hp⟩ := Finset.mem_product.mp hap
  obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
  obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hd
  have hpd : p ∣ b ^ 2 := by
    rw [hbe, ← he]
    exact dvd_mul_left p a
  have hpb := (Nat.prime_dvd_prime_iff_eq hp (hA b hb).1).mp (hp.dvd_of_dvd_pow hpd)
  have hbN := (hA b hb).2.1
  omega

/-- The finite prefix after deleting both independently paid classes:
prime squares and mixed small/intermediate prime products. -/
def remainingPrefix (A : Finset ℕ) (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) \
      A.image (fun p => p ^ 2)) \ mixedLabels A N,
    prefixCoefficient A u N n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The actual off-diagonal prefix is the remaining prefix plus precisely
the mixed response, with every signed integer coefficient unchanged. -/
theorem offDiagonalPrefix_eq_remaining_add_mixed (A : Finset ℕ) (P : Polynomial ℂ)
    (u y : ℝ) (N : ℕ)
    (hA : ∀ a ∈ A, a.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    offDiagonalPrefix A P u y N = remainingPrefix A P u y N + mixedResponse A P u y N := by
  have hsub : mixedLabels A N ⊆
      Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) \
        A.image (fun p => p ^ 2) := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨mixedLabels_subset_range A u N hA hn,
      fun hd => Finset.disjoint_left.mp (mixedLabels_disjoint_diagonal A u N hA) hn hd⟩
  exact (Finset.sum_sdiff hsub).symm

/-- The complete signed carrier after the diagonal and mixed prefix
corrections are independently paid. The shared surviving terms remain coupled. -/
def refinedJoint (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  subcutoffResponse P u y N +
    ZetaPrimeCofactorCompletion.completedCofactorHead (intermediatePrimes u N) P N
      (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N) -
    remainingPrefix (intermediatePrimes u N) P u y N

/-- Removing the mixed correction adds its full signed response, with
the subtraction sign of the completed physical prefix preserved. -/
theorem refinedJoint_eq_offDiagonal_add_mixed (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    refinedJoint P u y N = offDiagonalJoint P u y N +
      mixedResponse (intermediatePrimes u N) P u y N := by
  have hA := fun a ha => (mem_intermediatePrimes u N a).mp ha
  unfold refinedJoint offDiagonalJoint
  rw [offDiagonalPrefix_eq_remaining_add_mixed _ P u y N hA]
  ring

/-- This entire extra deletion has independent vanishing source error
throughout 1/2<u<exp(-1/2), for every fixed polynomial and height. -/
theorem tendsto_refined_sub_offDiagonal (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (refinedJoint P u y N - offDiagonalJoint P u y N)) atTop (nhds 0) := by
  have h := tendsto_mixedResponse (intermediatePrimes u) P y hu hcontact
    (fun N a ha => (mem_intermediatePrimes u N a).mp ha)
  apply h.congr'
  filter_upwards [] with N
  rw [refinedJoint_eq_offDiagonal_add_mixed, add_sub_cancel_left]

/-- At an exposed zero in the existing annular range, the refined joint
response still has the WHOLE negative multiplicity source. The independent
floor for its completed head, two-intermediate-prime prefix and higher-degree
subcutoff terms remains open. No zero-free enlargement is asserted. -/
theorem tendsto_refinedJoint_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      refinedJoint 1 (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (1 / 2 : ℝ) < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcontact : 3 / 2 - rho.1.re < Real.exp (-(1 / 2 : ℝ)) :=
    huh.trans (Real.exp_lt_exp.mpr (by norm_num))
  have h := (tendsto_refined_sub_offDiagonal 1 rho.1.im hu hcontact).add
    (tendsto_offDiagonalJoint_exposed rho hrho hexposed huh)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end

end RiemannGaussian.ZetaRieszMixedPrefixTransport
