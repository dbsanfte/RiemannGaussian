/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCellBoundary

/-!
# Coupled adjacent factorial orders on complete cells

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCellOrders
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeCells
open ZetaRieszCellBoundary

/-- Choose the actual divisor cell of a specified original prime; no
uniform-width or missing-breakpoint assumption enters this finite selection. -/
def primeCell (Q : Finset ℕ) (L : ℝ) (n q₀ : ℕ) : Finset ℕ :=
  Q.filter (fun q => activeDivisors L n (Real.log q) = activeDivisors L n (Real.log q₀))

/-- Literal cell membership discharges the affine-profile condition for
every selected prime. -/
theorem primeCell_valid {Q : Finset ℕ} {L : ℝ} {n q₀ q : ℕ}
    (hq : q ∈ primeCell Q L n q₀) :
    q ∈ Q ∧ activeDivisors L n (Real.log q) = activeDivisors L n (Real.log q₀) := by
  simpa only [primeCell, Finset.mem_filter] using hq

/-- Every literal prime cell has an exact two-moment full-filter identity,
without a profile-error allowance or independent cancellation premise. -/
theorem prime_cell_exact_moments (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) (n q₀ : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n) :
    (∑ q ∈ primeCell Q L n q₀, eta q * bandWeight L P N t (q * n)) =
      (targetProfile L n (Real.log q₀) : ℂ) *
        primePacketMoment L (Real.log q₀) P N t (primeCell Q L n q₀) eta n 0 +
      (cellSlope L n (Real.log q₀) : ℂ) *
        primePacketMoment L (Real.log q₀) P N t (primeCell Q L n q₀) eta n 1 := by
  have h := prime_packet_eq_moment_pair L (Real.log q₀) P N t (primeCell Q L n q₀) eta n
    (fun q hq => hQ q (primeCell_valid hq).1)
  have hb : primePacketBoundary L (Real.log q₀) P N t (primeCell Q L n q₀) eta n = 0 := by
    unfold primePacketBoundary
    apply Finset.sum_eq_zero
    intro q hq
    rw [boundaryCorrection_eq_zero_of_cell L n (Real.log q₀) (Real.log q) (primeCell_valid hq).2]
    simp only [Complex.ofReal_zero, mul_zero]
  simpa only [hb, sub_zero] using h

/-- Raise the factorial kernel while keeping the original order's
support mask. No new-band boundary term is silently introduced. -/
def raisedBandAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (m : ℕ) : ℂ :=
  if m ∈ zetaPrimeLogBand N ∧ Squarefree m ∧ ¬ m.Prime then
    ((-Real.log m / L : ℝ) : ℂ) *
      zetaPrimeFilterKernel (SquarefreeEulerLog.raisedPolynomial P N) (N + 1)
        (3 / 2 + Complex.I * t) m else 0

/-- The existing exact factorial raising operator controls the physical
logarithm on every original-band amplitude. -/
theorem log_mul_bandAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (m : ℕ) :
    (Real.log m : ℂ) * bandAmplitude L P N t m = raisedBandAmplitude L P N t m := by
  unfold bandAmplitude raisedBandAmplitude
  split_ifs
  · rw [← SquarefreeEulerLog.log_mul_kernel P N (3 / 2 + Complex.I * t) m]
    ring
  · exact mul_zero _

/-- The first centred prime moment is an exact adjacent factorial-order
response minus its logarithmic centre, with the same original support. -/
theorem first_moment_eq_raised (L x : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    primePacketMoment L x P N t Q eta n 1 =
      (∑ q ∈ Q, eta q * raisedBandAmplitude L P N t (q * n)) -
        ((Real.log n + x : ℝ) : ℂ) * primePacketMoment L x P N t Q eta n 0 := by
  unfold primePacketMoment
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have hlog : Real.log (q * n : ℕ) = Real.log q + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hQ q hq) (by exact_mod_cast hn)]
  rw [← log_mul_bandAmplitude, hlog]
  push_cast
  ring

/-- The exact cell response is governed by two canonically determined
coefficients and adjacent factorial orders. This introduces no searched
weights and takes no separate norms of the two coupled responses. -/
theorem prime_cell_eq_adjacent_orders (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (Q : Finset ℕ) (eta : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (q₀ : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ n) :
    (∑ q ∈ primeCell Q L n q₀, eta q * bandWeight L P N t (q * n)) =
      ((targetProfile L n (Real.log q₀) -
        (Real.log n + Real.log q₀) * cellSlope L n (Real.log q₀) : ℝ) : ℂ) *
          primePacketMoment L (Real.log q₀) P N t (primeCell Q L n q₀) eta n 0 +
      (cellSlope L n (Real.log q₀) : ℂ) *
        (∑ q ∈ primeCell Q L n q₀, eta q * raisedBandAmplitude L P N t (q * n)) := by
  rw [prime_cell_exact_moments L P N t Q eta n q₀ hQ,
    first_moment_eq_raised L (Real.log q₀) P N t (primeCell Q L n q₀) eta hn
      (fun q hq => (hQ q (primeCell_valid hq).1).1.ne_zero)]
  push_cast
  ring

/-- The literal finite partition contains every active-divisor pattern
attained by the original prime list. -/
def attainedCells (Q : Finset ℕ) (L : ℝ) (n : ℕ) : Finset (Finset ℕ) :=
  Q.image (fun q : ℕ => activeDivisors L n (Real.log q))

/-- All original prime terms are retained once in the exact cell partition. -/
theorem sum_eq_sum_cells (Q : Finset ℕ) (L : ℝ) (n : ℕ) (f : ℕ → ℂ) :
    (∑ q ∈ Q, f q) = ∑ D ∈ attainedCells Q L n,
      ∑ q ∈ Q with activeDivisors L n (Real.log (q : ℕ)) = D, f q := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩) f

/-- Distinct divisor cells cannot compete for the same original prime. -/
theorem different_cells_disjoint (Q : Finset ℕ) (L : ℝ) (n : ℕ)
    {D E : Finset ℕ} (hDE : D ≠ E) :
    Disjoint (Q.filter (fun q : ℕ => activeDivisors L n (Real.log q) = D))
      (Q.filter (fun q : ℕ => activeDivisors L n (Real.log q) = E)) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  exact hDE ((Finset.mem_filter.mp hq).2.symm.trans (Finset.mem_filter.mp hq').2)

end
end RiemannGaussian.ZetaRieszCellOrders
