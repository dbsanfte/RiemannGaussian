/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius inversion leaves arbitrary signed divisor rows unrestricted

Literal divisor incidence has no extra rank/PSD restriction on arbitrary
complex column arrays: every finite positive-index row vector is realized
exactly by a finite column array. In particular successor correlation has
both arbitrarily large signs, even with unit column zero.

These arrays are NOT actual Mangoldt weights, positive prime measures, or
measures satisfying the complete integer Gamma observations. Those special
constraints remain essential. This is a no-go for free-weight matrix or
Möbius reindexing proofs, not for a prime-specific signed estimate.
-/

namespace RiemannGaussian.ArithmeticOperatorIncidenceFreedom
noncomputable section
open Complex ArithmeticOperatorKummerCutoff ArithmeticOperatorCrtBoundaryAudit
open scoped BigOperators ComplexConjugate

/-- Exact inverse on the ordinary integer divisor lattice. -/
def inverseRows (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℂ)*g p.2

/-- Every positive-index divisor row can be prescribed independently.
No zero-index endpoint enters Möbius inversion. -/
theorem observation_inverseRows (g : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    divisorObservation (inverseRows g) n = g n := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := inverseRows g) (g := g)).mpr (fun _ _ => rfl) n hn

/-- Finite support, so this is a finite-cutoff countermodel as well. -/
def inversePrefix (X : ℕ) (g : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 X then inverseRows g n else 0

theorem inversePrefix_zero_outside (X : ℕ) (g : ℕ → ℂ) {n : ℕ}
    (hn : n ∉ Finset.Icc 1 X) : inversePrefix X g n = 0 := by
  simp only [inversePrefix, ite_eq_right hn]

/-- Every positive-index row in the entire prefix is recovered exactly,
retaining every divisor and both literal endpoints. -/
theorem observation_inversePrefix (X : ℕ) (g : ℕ → ℂ) {n : ℕ}
    (hn : 0 < n) (hnX : n ≤ X) :
    divisorObservation (inversePrefix X g) n = g n := by
  rw [← observation_inverseRows g hn]
  unfold divisorObservation
  apply Finset.sum_congr rfl
  intro d hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hmem : d ∈ Finset.Icc 1 X := Finset.mem_Icc.mpr
    ⟨Nat.pos_of_dvd_of_pos hdvd hn, (Nat.le_of_dvd hn hdvd).trans hnX⟩
  simp only [inversePrefix, ite_eq_left hmem]

/-- The literal finite divisor operator is surjective, not merely
injective. Thus reindexing several rows supplies no free rank constraint. -/
theorem exists_finite_array_with_rows (X : ℕ) (g : ℕ → ℂ) :
    ∃ w : ℕ → ℂ, (∀ n ∉ Finset.Icc 1 X, w n = 0) ∧
      ∀ n ∈ Finset.Icc 1 X, divisorObservation w n = g n := by
  refine ⟨inversePrefix X g, fun _ hn => inversePrefix_zero_outside X g hn, ?_⟩
  intro n hn
  obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
  exact observation_inversePrefix X g hn0 hnX

/-- A completely joined row quadratic, with arbitrary fixed matrix,
including Gaussian, modular, cutoff or lag features. -/
def rowQuadratic (X : ℕ) (w : ℕ → ℂ) (K : ℕ → ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
    K n m*divisorObservation w n*conj (divisorObservation w m)

/-- Exact inverse transports the ENTIRE quadratic, not an allowance. -/
theorem rowQuadratic_inversePrefix (X : ℕ) (g : ℕ → ℂ) (K : ℕ → ℕ → ℂ) :
    rowQuadratic X (inversePrefix X g) K =
      ∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, K n m*g n*conj (g m) := by
  unfold rowQuadratic
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [observation_inversePrefix X g (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
    observation_inversePrefix X g (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2]

/-- Any all-weight PSD claim is exactly ordinary matrix PSD on arbitrary
row vectors. Divisor/Möbius geometry adds no independent restriction. -/
theorem rowQuadratic_nonnegative_forall_iff (X : ℕ) (K : ℕ → ℕ → ℂ) :
    (∀ w : ℕ → ℂ, 0 ≤ (rowQuadratic X w K).re) ↔
      ∀ g : ℕ → ℂ,
        0 ≤ (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, K n m*g n*conj (g m)).re := by
  constructor
  · intro hh g
    simpa only [rowQuadratic_inversePrefix] using hh (inversePrefix X g)
  · intro hh w
    exact hh (divisorObservation w)

private theorem observation_conj (w : ℕ → ℂ) (n : ℕ) :
    divisorObservation (fun d => conj (w d)) n = conj (divisorObservation w n) := by
  simp only [divisorObservation, map_sum]

/-- The exact nonlinear successor statistic permits every prescribed
row profile; no CRT compatibility is discarded in this identity. -/
theorem successor_prescribed (X : ℕ) (g : ℕ → ℂ) :
    shiftedRows X 1 (inversePrefix (X+1) g)
      (fun d => conj (inversePrefix (X+1) g d)) =
      ∑ n ∈ Finset.Icc 1 X, g n*conj (g (n+1)) := by
  unfold shiftedRows
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
  rw [observation_conj,
    observation_inversePrefix (X+1) g hn0 (by omega),
    observation_inversePrefix (X+1) g (by omega) (by omega)]

private def twoRows (t sigma : ℝ) (n : ℕ) : ℂ :=
  if n = 2 then (t : ℂ) else if n = 3 then (sigma*t : ℂ) else 0

private theorem twoRows_successor {X : ℕ} (hX : 2 ≤ X) (t sigma : ℝ) :
    (∑ n ∈ Finset.Icc 1 X, twoRows t sigma n*conj (twoRows t sigma (n+1))) =
      (sigma*t^2 : ℂ) := by
  rw [Finset.sum_eq_single 2]
  · simp only [twoRows]
    norm_num
    ring
  · intro n _ hn
    by_cases hn3 : n = 3
    · simp [hn3, twoRows]
    · simp [twoRows, hn, hn3]
  · exact fun hn => False.elim (hn (Finset.mem_Icc.mpr ⟨by omega,hX⟩))

/-- Unbounded negative successor response is possible on the literal
finite integer lattice, even after deleting the unit column. These
arrays fail the special actual-prime/Gamma constraints. -/
theorem exists_successor_below {X : ℕ} (hX : 2 ≤ X) {B : ℝ} (hB : 0 ≤ B) :
    ∃ w : ℕ → ℂ, w 1 = 0 ∧ (∀ n ∉ Finset.Icc 1 (X+1), w n = 0) ∧
      (shiftedRows X 1 w (fun d => conj (w d))).re < -B := by
  let g := twoRows (B+1) (-1)
  refine ⟨inversePrefix (X+1) g, ?_, fun _ hn => inversePrefix_zero_outside _ _ hn, ?_⟩
  · simp [inversePrefix, inverseRows, g, twoRows]
  · rw [successor_prescribed, twoRows_successor hX]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith

/-- The same literal lattice also permits arbitrarily large positive
responses. An independent prime condition is needed for either sign. -/
theorem exists_successor_above {X : ℕ} (hX : 2 ≤ X) {B : ℝ} (hB : 0 ≤ B) :
    ∃ w : ℕ → ℂ, w 1 = 0 ∧ (∀ n ∉ Finset.Icc 1 (X+1), w n = 0) ∧
      B < (shiftedRows X 1 w (fun d => conj (w d))).re := by
  let g := twoRows (B+1) 1
  refine ⟨inversePrefix (X+1) g, ?_, fun _ hn => inversePrefix_zero_outside _ _ hn, ?_⟩
  · simp [inversePrefix, inverseRows, g, twoRows]
  · rw [successor_prescribed, twoRows_successor hX]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith

end
end RiemannGaussian.ArithmeticOperatorIncidenceFreedom
