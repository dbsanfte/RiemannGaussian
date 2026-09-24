/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleGeometry
import RiemannGaussian.ZetaRieszRectangleTailRates

/-!
# Exact finite mask comparison for the three separate prime legs

The prime sets remain finite and physical. The total order remains in the
concrete rectangle. Every omitted literal mask is a named finite error,
not an assumed negligible completion of the composite cofactor.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszWideOwnerAudit ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszPrimePairConvolution

/-- Three separate primes, in their original physical prime set. -/
def rectangleCube (u : ℝ) (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  intermediatePrimes u N ×ˢ (intermediatePrimes u N ×ˢ intermediatePrimes u N)

/-- Literal mask on the ordered prime triple, including its canonical owner. -/
def rectangleLiteralMask (u : ℝ) (N K : ℕ) (a : ℕ × ℕ × ℕ) : Prop :=
  let n := a.1 * (a.2.1 * a.2.2)
  n ∈ tripleBand u N K ∧ largestPrime n = a.1 ∧
    a.2.1 ∈ rectangleIncidences u N n ∧ smallPrime n a.2.1 = a.2.2

/-- Exact derivative-weighted kernel, before any mask or source limit. -/
def rectangleKernel (y : ℝ) (N j h : ℕ) (a : ℕ × ℕ × ℕ) : ℂ :=
  ((h + 1 : ℕ) : ℂ) * zetaPrimeLogKernel j (3 / 2 + Complex.I * y) a.1 *
    zetaPrimeLogKernel (N + 1 - j - h) (3 / 2 + Complex.I * y) a.2.1 *
    zetaPrimeLogKernel (h + 1) (3 / 2 + Complex.I * y) a.2.2

/-- The finite rectangle amplitude on one ordered triple. -/
def rectangleCubeAtom (u y : ℝ) (N : ℕ) (a : ℕ × ℕ × ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j, rectangleKernel y N j h a

/-- Separate finite prime legs with the correlated order rectangle intact. -/
def separatePrimeRectangle (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ a ∈ rectangleCube u N, rectangleCubeAtom u y N a

/-- Exactly the failures of the original masks in that finite comparison. -/
def rectangleMaskError (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ a ∈ (rectangleCube u N).filter (fun a => ¬ rectangleLiteralMask u N K a),
    rectangleCubeAtom u y N a

/-- The five leg cuts and total window imply every literal mask,
including the strict prime ordering and exactly two reflected-large primes. -/
theorem rectangleLiteralMask_of_good (t : ℕ) (ht : 32 ≤ t) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t))
    {a : ℕ × ℕ × ℕ} (ha : a ∈ rectangleCube u (dyadicMomentOrder t))
    (hbox : rectangleLogBox (dyadicMomentOrder t) a.1 a.2.1 a.2.2)
    (hwindow : (39 / 20 : ℝ) * dyadicMomentOrder t < Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ∧
      Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ≤ (41 / 20 : ℝ) * dyadicMomentOrder t) :
    rectangleLiteralMask u (dyadicMomentOrder t) (dyadicPrimeCount t) a := by
  let N := dyadicMomentOrder t
  obtain ⟨hpA, hqrA⟩ := Finset.mem_product.mp ha
  obtain ⟨hqA, hrA⟩ := Finset.mem_product.mp hqrA
  have hp := ((mem_intermediatePrimes u N a.1).mp hpA).1
  have hq := ((mem_intermediatePrimes u N a.2.1).mp hqA).1
  have hr := ((mem_intermediatePrimes u N a.2.2).mp hrA).1
  have hN : 2 ≤ N := by
    dsimp [N, dyadicMomentOrder]
    nlinarith [four_le_dyadicPrimeCount t]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hplo, hphi, hqlo, hqhi, hrhi⟩ := hbox
  have hqp : a.2.1 < a.1 := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hq.pos)
      (by exact_mod_cast hp.pos)).mp (by linarith : Real.log (a.2.1 : ℝ) < Real.log a.1)
  have hrq : a.2.2 < a.2.1 := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hr.pos)
      (by exact_mod_cast hq.pos)).mp (by nlinarith : Real.log (a.2.2 : ℝ) < Real.log a.2.1)
  obtain ⟨hs, hf, hc, hmax, hsmall⟩ := ordered_triple_data hp hq hr hqp hrq
  have hmem := rectangle_mem_tripleBand t ht hu huU hL hs hc hwindow (by
    intro p hp'
    rw [hf] at hp'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact hpA
    · exact hqA
    · exact hrA) (by
    intro p hp'
    rw [hf] at hp'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
    rcases hp' with rfl | rfl | rfl <;> linarith)
  have hLhi : SquarefreeVaughanLogSource.length u N ≤ (139 / 100 : ℝ) * N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    nlinarith [Real.log_two_lt_d9]
  exact ⟨hmem, hmax, rectangle_good_incidence (by omega : 0 < N) hpA hqA hrA
    ⟨hplo, hphi, hqlo, hqhi, hrhi⟩ hwindow hL hLhi, hsmall⟩

/-- The map from integer labels and their unique second incidence is
bijective onto the literally masked ordered triples. -/
theorem rawRectangleResponse_eq_cube (t : ℕ) (ht : 32 ≤ t) (u y : ℝ) :
    rawRectangleResponse u y (dyadicMomentOrder t) (dyadicPrimeCount t) =
      ∑ a ∈ (rectangleCube u (dyadicMomentOrder t)).filter
        (rectangleLiteralMask u (dyadicMomentOrder t) (dyadicPrimeCount t)),
          rectangleCubeAtom u y (dyadicMomentOrder t) a := by
  let N := dyadicMomentOrder t
  let K := dyadicPrimeCount t
  unfold rawRectangleResponse
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun a _ => (largestPrime a.1, a.2, smallPrime a.1 a.2)) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hn, hq⟩ := Finset.mem_sigma.mp ha
    have hq' := (Finset.mem_filter.mp hq).1
    have hn' := (Finset.mem_filter.mp hn).2.1
    have hfactor := (second_factorization hn' hq').1
    have he : largestPrime a.1 * (a.2 * smallPrime a.1 a.2) = a.1 := by
      rw [← hfactor]
      exact Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors
        (largestPrime_mem_of_three (Finset.mem_filter.mp hn).2.2))
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨owner_mem_intermediate t ht u hn,
        Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hq').2.1,
          (Finset.mem_filter.mp hq).2⟩⟩
    · dsimp only [rectangleLiteralMask]
      rw [he]
      exact ⟨hn, rfl, hq, rfl⟩
  · intro a ha b hb he
    obtain ⟨hna, hqa⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hnb, hqb⟩ := Finset.mem_sigma.mp hb
    have efa := (second_factorization (Finset.mem_filter.mp hna).2.1
      (Finset.mem_filter.mp hqa).1).1
    have efb := (second_factorization (Finset.mem_filter.mp hnb).2.1
      (Finset.mem_filter.mp hqb).1).1
    have hprod (n q : ℕ) (hn : n ∈ tripleBand u N K)
        (hf : n / largestPrime n = q * smallPrime n q) :
        largestPrime n * (q * smallPrime n q) = n := by
      rw [← hf]
      exact Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors
        (largestPrime_mem_of_three (Finset.mem_filter.mp hn).2.2))
    have hn : a.1 = b.1 := by
      have h := congrArg (fun c : ℕ × ℕ × ℕ => c.1 * (c.2.1 * c.2.2)) he
      simpa only [hprod _ _ hna efa, hprod _ _ hnb efb] using h
    have hq : a.2 = b.2 := congrArg (fun c : ℕ × ℕ × ℕ => c.2.1) he
    exact Sigma.ext hn (by simpa only [heq_eq_eq] using hq)
  · intro a ha
    have hm := (Finset.mem_filter.mp ha).2
    rcases hm with ⟨hn, hmax, hq, hsmall⟩
    refine ⟨⟨a.1 * (a.2.1 * a.2.2), a.2.1⟩, Finset.mem_sigma.mpr ⟨hn, hq⟩, ?_⟩
    simp only [hmax, hsmall]
  · intro a ha
    obtain ⟨hn, hq⟩ := Finset.mem_sigma.mp ha
    rw [rawRectangleAtom_eq_factorials (Finset.mem_filter.mp hn).2.1
      (Finset.mem_filter.mp hn).2.2 (Finset.mem_filter.mp hq).1]
    rfl

/-- The mask comparison has its exact signed finite error; no source or
norm estimate is used in this identity. -/
theorem separatePrimeRectangle_eq (t : ℕ) (ht : 32 ≤ t) (u y : ℝ) :
    separatePrimeRectangle u y (dyadicMomentOrder t) =
      rawRectangleResponse u y (dyadicMomentOrder t) (dyadicPrimeCount t) +
        rectangleMaskError u y (dyadicMomentOrder t) (dyadicPrimeCount t) := by
  rw [rawRectangleResponse_eq_cube t ht u y]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- Distributing only the finite prime sums gives three separate moments;
the exact order rectangle and log-r derivative remain unchanged. -/
theorem separatePrimeRectangle_eq_moments (u y : ℝ) (N : ℕ) :
    separatePrimeRectangle u y N =
      (((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
          ((h + 1 : ℕ) : ℂ) *
            finiteMoment (intermediatePrimes u N) j (3 / 2 + Complex.I * y) *
            finiteMoment (intermediatePrimes u N) (N + 1 - j - h) (3 / 2 + Complex.I * y) *
            finiteMoment (intermediatePrimes u N) (h + 1) (3 / 2 + Complex.I * y) := by
  unfold separatePrimeRectangle rectangleCubeAtom
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  simp only [rectangleCube, Finset.sum_product, rectangleKernel, finiteMoment,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext q
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end
end RiemannGaussian.ZetaRieszSkewAllocation
