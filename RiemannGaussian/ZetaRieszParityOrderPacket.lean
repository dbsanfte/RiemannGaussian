/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityOrderTail

/-!
# Exact good and exceptional allocations of the literal parity packet

The two marked orders in `rectangleMass` are the largest and least prime
coordinates of the full multinomial expansion. Splitting those weights
retains every original arithmetic mask and complex phase.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint

/-- Split the largest-prime coordinate while retaining a joint condition
on the least-prime coordinate. This is a finite multinomial identity. -/
theorem pair_allocation_cons {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι) (hp : p ∉ S)
    {r : ι} (hrp : r ≠ p) (x : ι → ℝ) (M : ℕ) (E : ℕ → ℕ → Prop) [DecidableRel E] :
    (∑ d ∈ Finset.piAntidiag (S.cons p hp) M,
      if E (d p) (d r) then allocationWeight (S.cons p hp) x d else 0) =
    ∑ j ∈ Finset.range (M+1), (M.choose j : ℝ)*x p^j *
      ∑ d ∈ Finset.piAntidiag S (M-j),
        if E j (d r) then allocationWeight S x d else 0 := by
  rw [Finset.piAntidiag_cons, Finset.sum_disjiUnion,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  have hbM : j+(M-j) = M := Nat.add_sub_of_le (by have := Finset.mem_range.mp hj; omega)
  simp only [Finset.sum_map]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdm := Finset.mem_piAntidiag.mp hd
  have hdp : d p = 0 := by
    by_contra h
    exact hp (hdm.2 p h)
  simp only [addRightEmbedding_apply, Pi.add_apply, if_true, hdp, zero_add,
    if_neg hrp, add_zero]
  split_ifs with hE
  · unfold allocationWeight
    rw [Nat.multinomial_cons, Finset.prod_cons]
    simp only [Pi.add_apply, if_true, hdp, zero_add]
    have hsum : (∑ q ∈ S, (d q + if q = p then j else 0)) = (M-j) := by
      simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', hp, if_false, add_zero] using hdm.1
    have hm : Nat.multinomial S (d + fun q => if q = p then j else 0) = Nat.multinomial S d := by
      apply Nat.multinomial_congr
      intro q hq
      simp only [Pi.add_apply, if_neg (ne_of_mem_of_not_mem hq hp), add_zero]
    have hprod : (∏ q ∈ S, x q^(d q+if q = p then j else 0)) = ∏ q ∈ S, x q^d q := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [if_neg (ne_of_mem_of_not_mem hq hp), add_zero]
    rw [hsum, hbM, hm, hprod, Nat.cast_mul]
    ring
  · simp

/-- The remaining single marked coordinate has its exact binomial
marginal, with the total of the other weights left unnormalized. -/
theorem marked_allocation_range {ι : Type*} [DecidableEq ι] (S : Finset ι) {p : ι} (hp : p ∈ S)
    (x : ι → ℝ) (M : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (∑ d ∈ Finset.piAntidiag S M, if E (d p) then allocationWeight S x d else 0) =
      ∑ k ∈ Finset.range (M+1), if E k then
        (M.choose k : ℝ)*x p^k*(∑ q ∈ S.erase p, x q)^(M-k) else 0 := by
  have h := marked_allocation_cons (S.erase p) p (Finset.notMem_erase p S) x M E
  have he : (S.erase p).cons p (Finset.notMem_erase p S) = S := by
    rw [Finset.cons_eq_insert, Finset.insert_erase hp]
  rw [he, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  exact h

/-- Clearing the conditional binomial normalization is exact at every
finite order; no limiting share indicator is inserted. -/
theorem conditional_mass (M h : ℕ) (hh : h ≤ M) (a b : ℝ) (hb : b ≠ 0) :
    b^M*mass M h (a/b) = (M.choose h : ℝ)*a^h*(b-a)^(M-h) := by
  have he : 1-a/b = (b-a)/b := by field_simp
  unfold mass
  rw [he, div_pow, div_pow]
  have hp : b^h*b^(M-h) = b^M := by rw [← pow_add, Nat.add_sub_of_le hh]
  calc
    _ = b^M/(b^h*b^(M-h))*((M.choose h : ℝ)*a^h*(b-a)^(M-h)) := by ring
    _ = _ := by rw [hp, div_self (pow_ne_zero M hb), one_mul]

/-- The two marked coordinates of the complete multinomial expansion
recover exactly the existing finite `rectangleMass`. -/
theorem rectangleMass_eq_allocations {ι : Type*} [DecidableEq ι] (S : Finset ι)
    {p r : ι} (hp : p ∈ S) (hr : r ∈ S) (hrp : r ≠ p)
    (x : ι → ℝ) (hsum : ∑ q ∈ S, x q = 1) (hxp : x p ≠ 1) (N : ℕ) :
    rectangleMass N (1-x p) (x r/(1-x p)) =
      ∑ d ∈ (Finset.piAntidiag S (N+1)).filter
        (fun d => d r ∈ rectangleOrders N (d p)), allocationWeight S x d := by
  have hcons : (S.erase p).cons p (Finset.notMem_erase p S) = S := by
    rw [Finset.cons_eq_insert, Finset.insert_erase hp]
  have hr' : r ∈ S.erase p := Finset.mem_erase.mpr ⟨hrp, hr⟩
  have ht := pair_allocation_cons (S.erase p) p (Finset.notMem_erase p S)
    hrp x (N+1) (fun j h => h ∈ rectangleOrders N j)
  rw [hcons] at ht
  rw [Finset.sum_filter, ht]
  unfold rectangleMass
  simp only [sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  rw [marked_allocation_range _ hr' x (N+1-j)]
  have hrest : (∑ q ∈ (S.erase p).erase r, x q) = 1-x p-x r := by
    have h1 := Finset.sum_erase_add S x hp
    have h2 := Finset.sum_erase_add (S.erase p) x hr'
    rw [hsum] at h1
    linarith
  rw [hrest]
  have hsets : (Finset.range (N+1-j+1)).filter
      (fun h => h ∈ rectangleOrders N j) = rectangleOrders N j := by
    rw [Finset.filter_mem_eq_inter]
    exact Finset.inter_eq_right.mpr
      (show rectangleOrders N j ⊆ Finset.range (N+1-j+1) from Finset.filter_subset _ _)
  have hrect : (∑ h ∈ rectangleOrders N j, mass (N+1-j) h (x r/(1-x p))) =
      ∑ h ∈ Finset.range (N+1-j+1), if h ∈ rectangleOrders N j then
        mass (N+1-j) h (x r/(1-x p)) else 0 := by
    rw [← Finset.sum_filter, hsets]
  rw [hrect]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs with hc
  · have hhM : h ≤ N+1-j := by have := Finset.mem_range.mp hh; omega
    have hcond := conditional_mass (N+1-j) h hhM (x r) (1-x p) (by contrapose! hxp; linarith)
    unfold mass at hcond ⊢
    linear_combination ((N+1).choose j : ℝ)*x p^j*hcond
  · simp

/-- All allocations selected by the original largest/least order box. -/
def rectangleAllocations (N n : ℕ) : Finset (ℕ → ℕ) :=
  (Finset.piAntidiag n.primeFactors (N+1)).filter
    (fun d => d n.minFac ∈ rectangleOrders N (d (largestPrime n)))

/-- The original rectangle mass with all base orders at least N/200. -/
def goodRectangleMass (N n : ℕ) : ℝ :=
  ∑ d ∈ (rectangleAllocations N n).filter (GoodAllocation n.primeFactors N),
    allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d

/-- The complementary original rectangle mass with some base order below N/200. -/
def badRectangleMass (N n : ℕ) : ℝ :=
  ∑ d ∈ (rectangleAllocations N n).filter (fun d => ¬GoodAllocation n.primeFactors N d),
    allocationWeight n.primeFactors (fun p => Real.log p/Real.log n) d

/-- The actual log ratios and canonical marked primes satisfy the
finite multinomial identity, including its exact correlated rectangle. -/
theorem rectangleMass_eq_good_add_bad {n : ℕ} (h : FullParityBox n) (N : ℕ) :
    rectangleMass N (1-Real.log (largestPrime n)/Real.log n)
      (Real.log n.minFac/(Real.log n-Real.log (largestPrime n))) =
        goodRectangleMass N n+badRectangleMass N n := by
  have hn : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.nontrivial)
  have hc : 0 < Real.log n-Real.log (largestPrime n) := by nlinarith [h.largest_upper]
  have hr : n.minFac ∈ n.primeFactors :=
    (Nat.minFac_prime h.nontrivial.ne').mem_primeFactors (Nat.minFac_dvd n) h.squarefree.ne_zero
  have hrp : n.minFac ≠ largestPrime n := by
    intro he
    have hl := h.least_upper
    rw [he] at hl
    nlinarith [h.largest_lower]
  have hp : Real.log (largestPrime n)/Real.log n ≠ 1 := by
    exact ne_of_lt ((div_lt_one hn).mpr (by linarith))
  have he : (Real.log n.minFac/Real.log n)/(1-Real.log (largestPrime n)/Real.log n) =
      Real.log n.minFac/(Real.log n-Real.log (largestPrime n)) := by
    field_simp
  have ht := rectangleMass_eq_allocations n.primeFactors h.largest_mem hr hrp
    (fun p => Real.log p/Real.log n) (fullParityBox_shares h).2 hp N
  rw [he] at ht
  rw [ht, goodRectangleMass, badRectangleMass, Finset.sum_filter_add_sum_filter_not]
  rfl

theorem badRectangleMass_bounds {n : ℕ} (h : FullParityBox n) (N : ℕ) :
    0 ≤ badRectangleMass N n ∧ badRectangleMass N n ≤ 39*Real.exp (-(N : ℝ)/400) := by
  have hx (p : ℕ) (hp : p ∈ n.primeFactors) : 0 ≤ Real.log p/Real.log n := by
    linarith [(fullParityBox_shares h).1 p hp]
  have hw := allocationWeight_nonneg n.primeFactors _ hx
  constructor
  · exact Finset.sum_nonneg (fun d _ => hw d)
  · apply le_trans ?_ (fullParityBox_bad_mass h N)
    unfold badRectangleMass badAllocationMass
    apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hw d)
    intro d hd
    obtain ⟨hdr, hbad⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hdr).1, hbad⟩

/-- The original full-support guard with the good factorial mass. -/
def goodParitySelection (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ fullParityBand u N K then goodRectangleMass N n else 0

/-- The original full-support guard with the exceptional factorial mass. -/
def badParitySelection (u : ℝ) (N K n : ℕ) : ℝ :=
  if n ∈ fullParityBand u N K then badRectangleMass N n else 0

theorem fullParitySelection_split (u : ℝ) (N K n : ℕ) :
    fullParitySelection u N K n = goodParitySelection u N K n+badParitySelection u N K n := by
  unfold fullParitySelection goodParitySelection badParitySelection
  split_ifs with hn
  · exact rectangleMass_eq_good_add_bad (Finset.mem_filter.mp hn).2.1 N
  · norm_num

theorem badParitySelection_bounds (u : ℝ) (N K n : ℕ) :
    0 ≤ badParitySelection u N K n ∧
      badParitySelection u N K n ≤ 39*Real.exp (-(N : ℝ)/400) := by
  unfold badParitySelection
  split_ifs with hn
  · exact badRectangleMass_bounds (Finset.mem_filter.mp hn).2.1 N
  · exact ⟨le_rfl, by positivity⟩

/-- The good and exceptional pieces have the very same coefficient,
allocation factor, physical and support masks, moving length and phase. -/
def goodPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, (goodParitySelection u N K n : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

/-- The literal arithmetic packet carried by exceptional factorial allocations. -/
def badPacket (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, (badParitySelection u N K n : ℂ)*
    (residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeLogKernel N (3/2+Complex.I*y) n)

theorem fullParityPacket_split (u y : ℝ) (N K : ℕ) :
    fullParityPacket u y N K = goodPacket u y N K+badPacket u y N K := by
  unfold fullParityPacket goodPacket badPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [fullParitySelection_split]
  push_cast
  ring

end
end RiemannGaussian.ZetaRieszParityOrderTail
