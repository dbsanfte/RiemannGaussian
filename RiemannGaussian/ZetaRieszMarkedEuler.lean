/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszLeastOrderOverflow
import RiemannGaussian.ZetaRieszPrimeFourier
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The marked factorial rectangle in the ordered prime Euler product

The formal coefficients retain every factorial order, both marked slots,
and each prime's full Fourier factor. Completing the middle subsets is an
exact finite algebraic operation. It does not itself pay arithmetic masks.
-/

namespace RiemannGaussian.ZetaRieszMarkedEuler
noncomputable section
open scoped BigOperators Classical
open ZetaRieszSkewAllocation ZetaRieszJointOwnerTransfer
open ZetaRieszPrimeFourier

/-- An ordinary-prime factorial leg with its exact signed Fourier factor.
Order zero remains present. No complete-prime phase limit is used. -/
def leg (s : ℂ) (xi : ℝ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun k =>
    (1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeLogKernel k s p)

@[simp] theorem coeff_leg (s : ℂ) (xi : ℝ) (p k : ℕ) :
    PowerSeries.coeff k (leg s xi p) =
      (1-zetaPrimeFeature (Complex.I*xi) p)*zetaPrimeLogKernel k s p :=
  PowerSeries.coeff_mk _ _

/-- The power-series coefficient uses the same ordinary-function
antidiagonal as the literal factorial allocation. -/
theorem coeff_prod_pi (S : Finset ℕ) (F : ℕ → PowerSeries ℂ) (M : ℕ) :
    PowerSeries.coeff M (∏ q ∈ S, F q) =
      ∑ d ∈ Finset.piAntidiag S M, ∏ q ∈ S, PowerSeries.coeff (d q) (F q) := by
  rw [PowerSeries.coeff_prod, Finset.finsuppAntidiag, Finset.sum_map]
  exact Finset.sum_attach _ (fun d : ℕ → ℕ =>
    ∏ q ∈ S, PowerSeries.coeff (d q) (F q))

/-- Remove one marked coordinate while retaining the selection on both
coordinates and the exact total order. -/
theorem selected_cons (S : Finset ℕ) (p : ℕ) (hp : p ∉ S) {r : ℕ}
    (hrp : r ≠ p) (F : ℕ → PowerSeries ℂ) (M : ℕ)
    (E : ℕ → ℕ → Prop) [DecidableRel E] :
    (∑ d ∈ Finset.piAntidiag (S.cons p hp) M,
      if E (d p) (d r) then ∏ q ∈ S.cons p hp, PowerSeries.coeff (d q) (F q) else 0) =
    ∑ j ∈ Finset.range (M+1), PowerSeries.coeff j (F p)*
      ∑ d ∈ Finset.piAntidiag S (M-j),
        if E j (d r) then ∏ q ∈ S, PowerSeries.coeff (d q) (F q) else 0 := by
  rw [Finset.piAntidiag_cons, Finset.sum_disjiUnion,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Finset.sum_map]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : d p = 0 := by
    by_contra h
    exact hp ((Finset.mem_piAntidiag.mp hd).2 p h)
  simp only [addRightEmbedding_apply, Pi.add_apply, if_true, hdp, zero_add,
    if_neg hrp, add_zero]
  split_ifs with hE
  · rw [Finset.prod_cons]
    simp only [if_true, hdp, zero_add]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    rw [if_neg (ne_of_mem_of_not_mem hq hp), add_zero]
  · simp

theorem selected_single (S : Finset ℕ) {p : ℕ} (hp : p ∈ S)
    (F : ℕ → PowerSeries ℂ) (M : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (∑ d ∈ Finset.piAntidiag S M,
      if E (d p) then ∏ q ∈ S, PowerSeries.coeff (d q) (F q) else 0) =
    ∑ j ∈ Finset.range (M+1), if E j then
      PowerSeries.coeff j (F p)*PowerSeries.coeff (M-j) (∏ q ∈ S.erase p, F q) else 0 := by
  have he : (S.erase p).cons p (Finset.notMem_erase p S) = S := by
    rw [Finset.cons_eq_insert, Finset.insert_erase hp]
  have h := selected_cons (S.erase p) p (Finset.notMem_erase p S)
    (r := p+1) (by omega) F M (fun j _ => E j)
  rw [he] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hj : E j
  · simp only [if_pos hj, coeff_prod_pi]
  · simp only [if_neg hj, Finset.sum_const_zero, mul_zero]

/-- Two-coordinate coefficient extraction is exactly the old factorial
rectangle, not its limiting log-share indicator. -/
theorem selected_rectangle (S : Finset ℕ) {p r : ℕ} (hp : p ∈ S)
    (hr : r ∈ S) (hrp : r ≠ p) (F : ℕ → PowerSeries ℂ) (N : ℕ) :
    (∑ d ∈ (Finset.piAntidiag S (N+1)).filter
      (fun d => d r ∈ rectangleOrders N (d p)),
        ∏ q ∈ S, PowerSeries.coeff (d q) (F q)) =
    ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
      PowerSeries.coeff j (F p)*PowerSeries.coeff h (F r)*
        PowerSeries.coeff (N+1-j-h) (∏ q ∈ (S.erase p).erase r, F q) := by
  have he : (S.erase p).cons p (Finset.notMem_erase p S) = S := by
    rw [Finset.cons_eq_insert, Finset.insert_erase hp]
  have h := selected_cons (S.erase p) p (Finset.notMem_erase p S) hrp F (N+1)
    (fun j h => h ∈ rectangleOrders N j)
  rw [he] at h
  rw [Finset.sum_filter, h]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [selected_single _ (Finset.mem_erase.mpr ⟨hrp,hr⟩), Finset.mul_sum]
  have hsub : rectangleOrders N j ⊆ Finset.range (N+1-j+1) := Finset.filter_subset _ _
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]
  simp only [mul_assoc]

/-- The literal two-slot rectangle acts linearly on the entire middle
series. The remaining order is correlated with BOTH marked orders. -/
def rectangle (N p r : ℕ) (s : ℂ) (xi : ℝ) (F : PowerSeries ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N+2), ∑ h ∈ rectangleOrders N j,
    PowerSeries.coeff j (leg s xi p)*PowerSeries.coeff h (leg s xi r)*
      PowerSeries.coeff (N+1-j-h) F

/-- The existing marked allocation and the new rectangle have exactly
the same prime products and Fourier signs, including all low orders. -/
theorem rectangle_eq_marked (N n p : ℕ) (s : ℂ) (xi : ℝ)
    (hp : p ∈ n.primeFactors) (hr : n.minFac ∈ n.primeFactors)
    (hrp : n.minFac ≠ p) :
    rectangle N p n.minFac s xi
        (∏ q ∈ (n.primeFactors.erase p).erase n.minFac, leg s xi q) =
      primeProduct n xi * ∑ d ∈ markedAllocations N n p,
        ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) s q := by
  rw [rectangle, ← selected_rectangle _ hp hr hrp]
  simp only [coeff_leg, Finset.prod_mul_distrib]
  rw [← Finset.mul_sum]
  rfl

theorem rectangle_sum (N p r : ℕ) (s : ℂ) (xi : ℝ)
    {ι : Type*} (S : Finset ι) (F : ι → PowerSeries ℂ) :
    rectangle N p r s xi (∑ a ∈ S, F a) =
      ∑ a ∈ S, rectangle N p r s xi (F a) := by
  simp only [rectangle, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]

/-- Middle primes are strictly above the canonical least prime and are
distinct from the other marked prime. Their subsets need no ordering. -/
def middlePrimes (A : Finset ℕ) (p r : ℕ) : Finset ℕ :=
  A.filter (fun q => r < q ∧ q ≠ p)

/-- All middle-prime subsets are summed before any norm or order limit. -/
def middleEuler (A : Finset ℕ) (p r : ℕ) (s : ℂ) (xi : ℝ) : PowerSeries ℂ :=
  ∏ q ∈ middlePrimes A p r, (1+leg s xi q)

/-- Exact ordered-least-prime Euler completion at the original factorial
rectangle; this identity alone makes no assertion about removed masks. -/
theorem rectangle_middleEuler (A : Finset ℕ) (N p r : ℕ) (s : ℂ) (xi : ℝ) :
    rectangle N p r s xi (middleEuler A p r s xi) =
      ∑ U ∈ (middlePrimes A p r).powerset,
        rectangle N p r s xi (∏ q ∈ U, leg s xi q) := by
  rw [middleEuler, Finset.prod_one_add, rectangle_sum]

/-- The empty middle subset contributes exactly zero: the two marked
orders alone cannot fill the total order N+1. No semiprime is smuggled
into the completion. -/
theorem rectangle_one (N p r : ℕ) (s : ℂ) (xi : ℝ) :
    rectangle N p r s xi 1 = 0 := by
  apply Finset.sum_eq_zero
  intro j _hj
  apply Finset.sum_eq_zero
  intro h hh
  have hc := (Finset.mem_filter.mp hh).2
  have hz : N+1-j-h ≠ 0 := by omega
  simp [PowerSeries.coeff_one, hz]

/-- The finite completion is ordered only at the least-prime slot.
Every other actual prime incidence keeps its own factorial rectangle. -/
def orderedSymbol (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
    rectangle N p r s xi (middleEuler A p r s xi)

theorem orderedSymbol_subsets (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    orderedSymbol A N s xi =
      ∑ r ∈ A, ∑ p ∈ A.filter (fun p => r < p),
        ∑ U ∈ (middlePrimes A p r).powerset,
          rectangle N p r s xi (∏ q ∈ U, leg s xi q) := by
  simp only [orderedSymbol, rectangle_middleEuler]

/-- Both Fourier frequencies remain coupled in the finite completion. -/
def orderedPair (A : Finset ℕ) (N : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*orderedSymbol A N s xi +
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*orderedSymbol A N s (-xi)

/-- The coincident marked/least slot is identically absent in the
literal allocation set, rather than discarded by a norm estimate. -/
theorem markedAllocations_least (N n : ℕ) : markedAllocations N n n.minFac = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hr := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).2).2
  omega

/-- The finite allocation sum before the Fourier integral. -/
def allocationSum (N n : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ n.primeFactors, ∑ d ∈ markedAllocations N n p,
    ∏ q ∈ n.primeFactors, zetaPrimeLogKernel (d q) s q

/-- The exact marked symbol at an observed label. The least-prime
ordering and the observed middle subset have not been completed here. -/
def labelSymbol (N n : ℕ) (s : ℂ) (xi : ℝ) : ℂ :=
  ∑ p ∈ n.primeFactors.erase n.minFac,
    rectangle N p n.minFac s xi
      (∏ q ∈ (n.primeFactors.erase p).erase n.minFac, leg s xi q)

theorem labelSymbol_eq (N n : ℕ) (s : ℂ) (xi : ℝ)
    (hr : n.minFac ∈ n.primeFactors) :
    labelSymbol N n s xi = primeProduct n xi*allocationSum N n s := by
  unfold labelSymbol allocationSum
  rw [← Finset.sum_erase_add _ _ hr, markedAllocations_least,
    Finset.sum_empty, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact rectangle_eq_marked N n p s xi (Finset.mem_of_mem_erase hp) hr
    (Finset.mem_erase.mp hp).1.symm

/-- The two Fourier signs of one literal label, paired before division
by frequency squared. -/
def labelPair (N n : ℕ) (s : ℂ) (L xi : ℝ) : ℂ :=
  Complex.exp (((xi*L : ℝ) : ℂ)*Complex.I)*labelSymbol N n s xi +
    Complex.exp (((-xi*L : ℝ) : ℂ)*Complex.I)*labelSymbol N n s (-xi)

theorem labelPair_eq (N n : ℕ) (s : ℂ) (L xi : ℝ)
    (hr : n.minFac ∈ n.primeFactors) :
    labelPair N n s L xi = allocationSum N n s*primePair n L xi := by
  rw [labelPair, labelSymbol_eq _ _ _ _ hr, labelSymbol_eq _ _ _ _ hr,
    primePair]
  ring

/-- The completed rectangle's two-frequency quotient is integrable at
each literal squarefree label; no separate singular channel is integrated. -/
theorem integrable_labelPair {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (N : ℕ) (s : ℂ) (L : ℝ) :
    MeasureTheory.IntegrableOn
      (fun xi : ℝ => labelPair N n s L xi/(xi : ℂ)^2) (Set.Ioi 0) := by
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  simp_rw [labelPair_eq _ _ _ _ _ hr, mul_div_assoc]
  exact (integrable_primePair_div_sq hn (by omega) L).const_mul _

/-- Riesz Fourier factorisation and the factorial rectangle commute
exactly at the original arithmetic label and normalization. -/
theorem marked_atom_eq_integral {n : ℕ} (hn : Squarefree n) (hn1 : 1 < n)
    (hnp : ¬n.Prime) (N : ℕ) (s : ℂ) {L : ℝ} (hL : 0 < L) :
    ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N s n) =
      ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(L : ℂ))*
        ∫ xi : ℝ in Set.Ioi 0, labelPair N n s L xi/(xi : ℂ)^2 := by
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime hn1.ne').mem_primeFactors (Nat.minFac_dvd n) hn.ne_zero
  have hk : ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      zetaPrimeLogKernel N s n =
      ((N+1 : ℕ) : ℂ)/(Real.log n : ℂ)*allocationSum N n s := by
    simp only [Complex.ofReal_sum, Finset.sum_mul, allocationSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    simpa only [Finset.mul_sum] using marked_kernel (p := p) hn hn1 N s
  have hl : (Real.log n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn1)).ne'
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show ((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
      (SquarefreeVaughanLogSource.coefficient L n*zetaPrimeLogKernel N s n) =
      SquarefreeVaughanLogSource.coefficient L n*
        (((∑ p ∈ n.primeFactors, markedWeight N n p : ℝ) : ℂ)*
          zetaPrimeLogKernel N s n) by ring, hk,
    coefficient_eq_primePair_integral L n, if_pos ⟨hn,by omega,hnp⟩]
  simp_rw [labelPair_eq _ _ _ _ _ hr, mul_div_assoc]
  rw [MeasureTheory.integral_const_mul]
  field_simp


end
end RiemannGaussian.ZetaRieszMarkedEuler
