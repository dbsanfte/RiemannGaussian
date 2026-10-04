/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairPrefixConvolution
import RiemannGaussian.ZetaRieszPairWholeCompletion
import RiemannGaussian.ZetaRieszLowCountSelbergAudit
import RiemannGaussian.ZetaRieszPrefixCorrelation

/-!
# Mask-preserving adjacent factorial orders of the Selberg defect

The exact complex phase and one common literal pair mask are retained in
every shifted order. This file does not complete any prime interval and
does not identify fixed-mask moments with neighbouring native masks.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Real Filter Topology
open Complex (I)
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSelbergAdjacentOrders
open ZetaRieszHeadOrders ZetaRieszLowCountSelbergAudit
open ZetaRieszGlobalHeadPriceAudit ZetaRieszLowCountSignedBoundary
open ZetaRieszGlobalBulkPayment ZetaRieszGlobalPeriodEdgePayment
open ZetaRieszPairPrefixPayment ZetaRieszPairPrefixConvolution

/-- The exact data of the existing balanced box; no new subdivision. -/
theorem balanced_pair_data {N p q : ℕ} (he : (p,q) ∈ balancedPairs N) :
    p.Prime ∧ q.Prime ∧ p<q ∧
      (N : ℝ)<log p ∧ log p≤(N : ℝ)+1 ∧
      (N : ℝ)+1<log q ∧ log q≤(N : ℝ)+2 := by
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp he
  have hpB := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp
  have hqB := ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hq
  exact ⟨hpB.1,hqB.1,ZetaRieszAllowancePrimeBoxes.logPrimes_order le_rfl hp hq,
    hpB.2.1,hpB.2.2,hqB.2.1,by linarith only [hqB.2.2]⟩

/-- The balanced box lies strictly inside the literal completed hinge. -/
theorem balanced_hinge_data {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) :
    log p <= SquarefreeVaughanLogSource.length u N ∧
    log q <= SquarefreeVaughanLogSource.length u N ∧
    SquarefreeVaughanLogSource.length u N <= log (p*q : ℕ) := by
  obtain ⟨hp,hq,_hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have hl := ZetaRieszPostHingeEnergy.length_ge_rational hN (by linarith : 0 < u) hU
  have hh := ZetaRieszSmallTagNativeFloor.length_upper hu (by omega : 2 <= N)
  have hNr : (65536 : ℝ) <= N := by exact_mod_cast hN
  have ht : log (p*q : ℕ) = log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  rw [ht]
  constructor
  · nlinarith only [hl,hpu,hNr]
  · constructor <;> nlinarith only [hl,hh,hpl,hql,hqu,hNr]

/-- The requested scalar identity is exact, including the logarithmic
imbalance. The original joined coefficient supplies all literal flags. -/
theorem balanced_selbergDefect_eq {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) :
    selbergDefect u N (p*q) =
      ((3/2*log (p*q : ℕ)-(log (p*q : ℕ))^2/SquarefreeVaughanLogSource.length u N-
        (log p-log q)^2/(2*log (p*q : ℕ)) : ℝ) : ℂ) := by
  obtain ⟨hp,hq,hpq,_⟩ := balanced_pair_data he
  have hn : p*q ∈ balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  have hs := (Finset.mem_filter.mp (Finset.mem_sdiff.mp
    (balancedProducts_subset_unmatched (u := u) hN hn)).1).2.1
  let L := SquarefreeVaughanLogSource.length u N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have ht : log (p*q : ℕ) = log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hT : 0 < log (p*q : ℕ) := log_pos (by
    exact_mod_cast (show 1 < p*q by nlinarith only [hp.two_le,hq.two_le]))
  obtain ⟨hpl,hql,hlT⟩ := balanced_hinge_data hu hU hN he
  have hr : VaughanLogAverage.riesz L (p*q) = log (p*q : ℕ)-L := by
    rw [ZetaRieszSemiprimePrefixDecay.riesz_semiprime_eq_tent _ hp hq hpq.ne]
    unfold ZetaSquarefreeRieszWindows.primePairTent
    rw [max_eq_right hL.le,max_eq_right (sub_nonneg.mpr hpl),
      max_eq_right (sub_nonneg.mpr hql),max_eq_left (by linarith only [hlT,ht])]
    rw [ht]
    ring
  rw [selbergDefect,balanced_joined_eq_completed hN hn,selbergCoefficient_pair hp hq hpq]
  simp only [completedCoefficient,if_pos hs,<-Complex.ofReal_sub]
  congr 1
  change -log (p*q : ℕ)*VaughanLogAverage.riesz L (p*q)/L-
    (-2*log p*log q/log (p*q : ℕ)) = _
  rw [hr]
  dsimp only [L] at hL ⊢
  field_simp [hL.ne',hT.ne']
  rw [ht]
  ring

/-- Dividing by the product logarithm removes exactly one order, with
no change to the complex prime phase. -/
theorem kernel_div_log {N n : ℕ} (hN : 0 < N)
    (hn : log (n : ℝ) ≠ 0) (s : ℂ) :
    zetaPrimeLogKernel N s n/(log n : ℂ) =
      zetaPrimeLogKernel (N-1) s n/(N : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hTc : (log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have h := log_mul_kernel (N-1) n s
  have he : N-1+1 = N := by omega
  rw [he] at h
  field_simp [hNc,hTc]
  linear_combination -h

/-- The exact adjacent-order identity for any imbalance, before a
single mask or Fourier phase is altered. -/
theorem quadratic_kernel_adjacent {N n : ℕ} (hN : 0 < N)
    (hn : log (n : ℝ) ≠ 0) {L : ℝ} (hL : L ≠ 0) (v : ℝ) (s : ℂ) :
    ((3/2*log n-(log n)^2/L-v^2/(2*log n) : ℝ) : ℂ)*zetaPrimeLogKernel N s n =
      (3/2 : ℂ)*(N+1)*zetaPrimeLogKernel (N+1) s n-
      ((N+1 : ℂ)*(N+2)/(L : ℂ))*zetaPrimeLogKernel (N+2) s n-
      ((v : ℂ)^2/(2*(N : ℂ)))*zetaPrimeLogKernel (N-1) s n := by
  have h1 := log_mul_kernel N n s
  have h2 := log_mul_kernel (N+1) n s
  rw [show N+1+1 = N+2 by omega] at h2
  simp only [Nat.cast_add,Nat.cast_one] at h1 h2
  have hd := kernel_div_log hN hn s
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hTc : (log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  simp only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp [hNc,hTc,hLc] at hd ⊢
  linear_combination
    (3*(L : ℂ)*(N : ℂ)*(log n : ℂ))*h1-
    (2*(N : ℂ)*(log n : ℂ)^2)*h1-
    (2*(N : ℂ)*(log n : ℂ)*(N+1))*h2-
    ((L : ℂ)*(v : ℂ)^2)*hd

/-- The pointwise identity for the actual balanced defect. Every
literal joined mask and the entire `n^(-iy)` phase are retained. -/
theorem balanced_selberg_kernel_adjacent {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) (s : ℂ) :
    selbergDefect u N (p*q)*zetaPrimeLogKernel N s (p*q) =
      (3/2 : ℂ)*(N+1)*zetaPrimeLogKernel (N+1) s (p*q)-
      ((N+1 : ℂ)*(N+2)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        zetaPrimeLogKernel (N+2) s (p*q)-
      (((log p-log q : ℝ) : ℂ)^2/(2*(N : ℂ)))*
        zetaPrimeLogKernel (N-1) s (p*q) := by
  obtain ⟨hp,hq,_⟩ := balanced_pair_data he
  rw [balanced_selbergDefect_eq hu hU hN he]
  exact quadratic_kernel_adjacent (by omega) (log_pos (by
    exact_mod_cast (show 1 < p*q by nlinarith only [hp.two_le,hq.two_le]))).ne'
    (SquarefreeVaughanLogSource.length_pos u N).ne' (log p-log q) s

/-- Two adjacent prime orders, including their exact factorial factors. -/
theorem log_square_mul_kernel (k p : ℕ) (s : ℂ) :
    (log p : ℂ)^2*zetaPrimeLogKernel k s p =
      (k+1 : ℂ)*(k+2)*zetaPrimeLogKernel (k+2) s p := by
  have h1 := log_mul_kernel k p s
  have h2 := log_mul_kernel (k+1) p s
  rw [show k+1+1 = k+2 by omega] at h2
  simp only [Nat.cast_add,Nat.cast_one] at h1 h2
  linear_combination (log p : ℂ)*h1+(k+1 : ℂ)*h2

/-- Expand the imbalance into shifts of the TWO original prime legs.
Every order-zero endpoint and the literal product phase remain present. -/
theorem imbalance_kernel_prime_orders (M p q : ℕ) (hp : 0 < p) (hq : 0 < q) (s : ℂ) :
    ((log p-log q : ℝ) : ℂ)^2*zetaPrimeLogKernel M s (p*q) =
      ∑ k ∈ Finset.range (M+1),
        ((k+1 : ℂ)*(k+2)*zetaPrimeLogKernel (k+2) s p*zetaPrimeLogKernel (M-k) s q+
         ((M-k+1 : ℕ) : ℂ)*((M-k+2 : ℕ) : ℂ)*
           zetaPrimeLogKernel k s p*zetaPrimeLogKernel (M-k+2) s q-
         2*(k+1 : ℂ)*((M-k+1 : ℕ) : ℂ)*
           zetaPrimeLogKernel (k+1) s p*zetaPrimeLogKernel (M-k+1) s q) := by
  rw [pair_kernel_convolution M p q hp hq s,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hp2 := log_square_mul_kernel k p s
  have hq2 := log_square_mul_kernel (M-k) q s
  have hp1 := log_mul_kernel k p s
  have hq1 := log_mul_kernel (M-k) q s
  simp only [Nat.cast_add,Nat.cast_one,Complex.ofReal_sub] at hp2 hq2 hp1 hq1 ⊢
  linear_combination
    (zetaPrimeLogKernel (M-k) s q)*hp2+
    (zetaPrimeLogKernel k s p)*hq2-
    (2*(log q : ℂ)*zetaPrimeLogKernel (M-k) s q)*hp1-
    (2*(k+1 : ℂ)*zetaPrimeLogKernel (k+1) s p)*hq1

/-- One COMMON finite mask, frozen across all factorial orders. -/
def maskedPairMoment (S : Finset (ℕ×ℕ)) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ e ∈ S,zetaPrimeLogKernel k s (e.1*e.2)

/-- The imbalance moment under that same literal mask. -/
def maskedImbalanceMoment (S : Finset (ℕ×ℕ)) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ e ∈ S,((log e.1-log e.2 : ℝ) : ℂ)^2*zetaPrimeLogKernel k s (e.1*e.2)

/-- Sum the actual identity over ANY retained part of the original
balanced mask. No radial, owner, prime, period or diagonal mask is moved. -/
theorem masked_balanced_adjacent {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536 <= N)
    (S : Finset (ℕ×ℕ)) (hS : S ⊆ balancedPairs N) (s : ℂ) :
    (∑ e ∈ S,selbergDefect u N (e.1*e.2)*zetaPrimeLogKernel N s (e.1*e.2)) =
      (3/2 : ℂ)*(N+1)*maskedPairMoment S (N+1) s-
      ((N+1 : ℂ)*(N+2)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        maskedPairMoment S (N+2) s-
      (1/(2*(N : ℂ)))*maskedImbalanceMoment S (N-1) s := by
  unfold maskedPairMoment maskedImbalanceMoment
  simp only [Finset.mul_sum,<-Finset.sum_sub_distrib,mul_assoc]
  exact Finset.sum_congr rfl (fun e he => by
    rw [balanced_selberg_kernel_adjacent hu hU hN (hS he) s]
    ring)

/-- The already joined head/correction flags vanish in the same box;
the full-mass coefficient is still present, rather than rectangle-paid. -/
theorem balanced_completed_kernel {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) (s : ℂ) :
    joinedCoefficient u N (p*q)*zetaPrimeLogKernel N s (p*q) =
      (N+1 : ℂ)*zetaPrimeLogKernel (N+1) s (p*q)-
      ((N+1 : ℂ)*(N+2)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        zetaPrimeLogKernel (N+2) s (p*q) := by
  obtain ⟨hp,hq,hpq,_⟩ := balanced_pair_data he
  have hn : p*q ∈ balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  obtain ⟨hpl,hql,hLT⟩ := balanced_hinge_data hu hU hN he
  have hnot := Nat.not_prime_mul hp.ne_one hq.ne_one
  have hcd : completedCoefficient (SquarefreeVaughanLogSource.length u N) (p*q) =
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) (p*q) := by
    simp only [completedCoefficient,SquarefreeVaughanLogSource.coefficient,
      hnot,not_false_eq_true,and_true]
  rw [balanced_joined_eq_completed hN hn,hcd,
    ZetaRieszPrefixCorrelation.coefficient_semiprime_inner hq hp
      (fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)) hql hpl hLT]
  have h1 := log_mul_kernel N (p*q) s
  have h2 := log_mul_kernel (N+1) (p*q) s
  rw [show N+1+1 = N+2 by omega] at h2
  simp only [Nat.cast_add,Nat.cast_one] at h1 h2
  have hLc : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_sub]
  field_simp [hLc]
  linear_combination
    (SquarefreeVaughanLogSource.length u N : ℂ)*h1-
    (log (p*q : ℕ) : ℂ)*h1-(N+1 : ℂ)*h2

private theorem balanced_prefixCoefficient {u : ℝ} {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) :
    prefixCoefficient u N (p*q) =
      (prefixLogCoefficient N (SquarefreeVaughanLogSource.length u N) (log p) (log q) : ℂ) := by
  obtain ⟨hp,hq,hpq,_⟩ := balanced_pair_data he
  have hn : p*q ∈ balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  have hs := (Finset.mem_sdiff.mp (balancedProducts_subset_unmatched (u := u) hN hn)).1
  have hm : ∀ r ∈ p.primeFactors,r < q := by
    intro r hr
    rw [hp.primeFactors,Finset.mem_singleton] at hr
    subst r
    exact hpq
  have hmax : ZetaRieszPrimeEndpoint.largestPrime (p*q) = q := by
    rw [mul_comm p q]
    exact ZetaRieszPrimeIntervals.largestPrime_mul q p hq hp.ne_zero hm
  have hco : ZetaRieszOwnedCells.ownerCofactor (p*q) = p := by
    rw [mul_comm p q]
    exact ZetaRieszPrimeIntervals.ownerCofactor_mul q p hq hp.ne_zero hm
  rw [prefixCoefficient,hmax,hco,if_pos (Finset.mem_union.mpr (Or.inr hs)),sub_zero]
  congr 1
  unfold prefixLogCoefficient
  rw [add_comm (log q) (log p)]
  ring

/-- Both literal factorial prefixes, kept as one signed expression.
The moving `13*N/32` endpoint is not replaced by a share indicator. -/
def factorialPrefixTerm (N : ℕ) (L : ℝ) (p q : ℕ) (s : ℂ) : ℂ :=
  (N+1 : ℂ)/(L : ℂ)*
    ((L-log p : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
      zetaPrimeLogKernel (N+1-k) s p*zetaPrimeLogKernel k s q)+
     (L-log q : ℂ)*(∑ k ∈ Finset.range (13*N/32+1),
      zetaPrimeLogKernel (N+1-k) s q*zetaPrimeLogKernel k s p))

/-- The ACTUAL prefix defect differs from the requested three-order
identity by exactly the two retained factorial prefixes, with their sign. -/
theorem balanced_prefix_kernel {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536 <= N) (he : (p,q) ∈ balancedPairs N) (s : ℂ) :
    (prefixCoefficient u N (p*q)-selbergCoefficient (p*q))*zetaPrimeLogKernel N s (p*q) =
      selbergDefect u N (p*q)*zetaPrimeLogKernel N s (p*q)-
        factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) p q s := by
  obtain ⟨hp,hq,_⟩ := balanced_pair_data he
  have hprod : 1 < p*q := by nlinarith only [hp.two_le,hq.two_le]
  have hpref := prefix_atom_eq N (SquarefreeVaughanLogSource.length u N)
    p q hp.pos hq.pos hprod s
  rw [<-balanced_prefixCoefficient hN he] at hpref
  have hbulk := balanced_completed_kernel hu hU hN he s
  dsimp only [factorialPrefixTerm,selbergDefect]
  linear_combination hpref-hbulk

/-- Both the requested shifts AND the exact prefix correction are
joined on one common mask. No commutator or prefix is hidden in an error. -/
theorem masked_prefix_adjacent {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536 <= N)
    (S : Finset (ℕ×ℕ)) (hS : S ⊆ balancedPairs N) (s : ℂ) :
    (∑ e ∈ S,(prefixCoefficient u N (e.1*e.2)-selbergCoefficient (e.1*e.2))*
      zetaPrimeLogKernel N s (e.1*e.2)) =
      (3/2 : ℂ)*(N+1)*maskedPairMoment S (N+1) s-
      ((N+1 : ℂ)*(N+2)/(SquarefreeVaughanLogSource.length u N : ℂ))*
        maskedPairMoment S (N+2) s-
      (1/(2*(N : ℂ)))*maskedImbalanceMoment S (N-1) s-
      ∑ e ∈ S,factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) e.1 e.2 s := by
  have he := Finset.sum_congr rfl (fun e he => balanced_prefix_kernel hu hU hN (hS he) s)
  rw [Finset.sum_sub_distrib,masked_balanced_adjacent hu hU hN S hS s] at he
  exact he

/-- Reindexing retains exactly one ordered incidence per original label. -/
theorem sum_balancedProducts (N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ balancedProducts N,f n) = ∑ e ∈ balancedPairs N,f (e.1*e.2) := by
  unfold balancedProducts
  rw [Finset.sum_image]
  intro e he e' he' hh
  exact balanced_pair_injective N he he' hh

/-- The whole literal prefix is split only into the EXISTING balanced
population and its exact remaining mask. No population is norm-paid. -/
theorem prefixPairDefect_adjacent_ledger {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536 <= N)
    {y : ℝ} (hy : 54 <= |y|) :
    prefixPairDefect u y N = (u : ℂ)^(N+1)*
      ((3/2 : ℂ)*(N+1)*maskedPairMoment (balancedPairs N) (N+1) (3/2+I*y)-
       ((N+1 : ℂ)*(N+2)/(SquarefreeVaughanLogSource.length u N : ℂ))*
         maskedPairMoment (balancedPairs N) (N+2) (3/2+I*y)-
       (1/(2*(N : ℂ)))*maskedImbalanceMoment (balancedPairs N) (N-1) (3/2+I*y)-
       (∑ e ∈ balancedPairs N,
         factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) e.1 e.2 (3/2+I*y))+
       ∑ n ∈ ((completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime))\
         balancedProducts N,
         (prefixCoefficient u N n-selbergCoefficient n)*zetaPrimeLogKernel N (3/2+I*y) n) := by
  have hS : balancedProducts N ⊆
      (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime) := by
    intro n hn
    refine Finset.mem_filter.mpr ⟨balancedProducts_subset_periods hN hy hn,?_⟩
    obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hq,_⟩ := balanced_pair_data he
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  have he := Finset.sum_sdiff
    (f := fun n => (prefixCoefficient u N n-selbergCoefficient n)*
      zetaPrimeLogKernel N (3/2+I*y) n) hS
  rw [sum_balancedProducts,
    masked_prefix_adjacent hu hU hN (balancedPairs N) Finset.Subset.rfl (3/2+I*y)] at he
  unfold prefixPairDefect
  congr 1
  linear_combination -he

/-- Only the already-paid coefficient difference is used for the
factorial-prefix error; the three shifted moments stay signed. -/
theorem balanced_factorialPrefix_geometric {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N : ℕ} (hN : 65536 <= N)
    {y : ℝ} (hy : 54 <= |y|) :
    ‖(u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
      factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) e.1 e.2 (3/2+I*y))‖ <=
        prefixBudget N := by
  have hCube : ∀ c : ℝ,c <= (4/3 : ℝ)*N → N^3 <=
      ZetaRieszOwnerLatticePhase.coreFloor N c (39/20) :=
    fun _ hc => cube_below_core hN hc
  have hS : balancedProducts N ⊆
      (completePeriodLabels (joinedLabels u N) N y).filter (fun n => ¬n.Prime) := by
    intro n hn
    refine Finset.mem_filter.mpr ⟨balancedProducts_subset_periods hN hy hn,?_⟩
    obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hp,hq,_⟩ := balanced_pair_data he
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  have hb := source_scaled_coefficient_error_bound hu hU N y (balancedProducts N)
    (by
      intro n hn
      obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hp,hq,_⟩ := balanced_pair_data he
      exact Nat.mul_pos hp.pos hq.pos)
    (joinedCoefficient u N) (prefixCoefficient u N)
    (fun n hn => joined_sub_prefixCoefficient_bound hu hU hN hCube hy (hS hn))
  rw [sum_balancedProducts] at hb
  have he : (∑ e ∈ balancedPairs N,
      (joinedCoefficient u N (e.1*e.2)-prefixCoefficient u N (e.1*e.2))*
        zetaPrimeLogKernel N (3/2+I*y) (e.1*e.2)) =
      ∑ e ∈ balancedPairs N,
        factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) e.1 e.2 (3/2+I*y) := by
    apply Finset.sum_congr rfl
    intro e he
    have h := balanced_prefix_kernel hu hU hN he (3/2+I*y)
    dsimp only [selbergDefect] at h
    linear_combination -h
  rwa [he] at hb

/-- Changing the SAME native balanced box by one order deletes every
old first-prime incidence. It is not a small factorial-order boundary. -/
theorem balancedPairs_disjoint_succ (N : ℕ) :
    Disjoint (balancedPairs N) (balancedPairs (N+1)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have h1 := (balanced_pair_data he).2.2.2.2.1
  have h2 := (balanced_pair_data hf).2.2.2.1
  norm_num only [Nat.cast_add,Nat.cast_one] at h2
  linarith only [h1,h2]

/-- The induced native product masks also have no overlap. -/
theorem balancedProducts_disjoint_succ (N : ℕ) :
    Disjoint (balancedProducts N) (balancedProducts (N+1)) := by
  apply Finset.disjoint_left.mpr
  intro n hn hf
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨⟨a,b⟩,hf,hab⟩ := Finset.mem_image.mp hf
  obtain ⟨hp,hq,_hpq,_hpl,hpu,_hql,hqu⟩ := balanced_pair_data he
  obtain ⟨ha,hb,_hab,hal,_hau,hbl,_hbu⟩ := balanced_pair_data hf
  have ht : log (p*q : ℕ) = log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have ht' : log (a*b : ℕ) = log a+log b := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast ha.ne_zero) (by exact_mod_cast hb.ne_zero)]
  rw [hab,ht] at ht'
  norm_num only [Nat.cast_add,Nat.cast_one] at hal hbl
  linarith only [ht',hpu,hqu,hal,hbl]

/-- The exact signed commutator for replacing a fixed mask by another
mask. Both sides of the set difference are retained before any estimate. -/
theorem masked_moment_commutator (S D : Finset (ℕ×ℕ)) (k : ℕ) (s : ℂ) :
    maskedPairMoment S k s-maskedPairMoment D k s =
      (∑ e ∈ S\D,zetaPrimeLogKernel k s (e.1*e.2))-
      (∑ e ∈ D\S,zetaPrimeLogKernel k s (e.1*e.2)) := by
  have hS : S ∩ D ⊆ S := by intro e he; exact (Finset.mem_inter.mp he).1
  have hD : S ∩ D ⊆ D := by intro e he; exact (Finset.mem_inter.mp he).2
  have heS : S\(S∩D) = S\D := by ext e; simp only [Finset.mem_sdiff,Finset.mem_inter]; tauto
  have heD : D\(S∩D) = D\S := by ext e; simp only [Finset.mem_sdiff,Finset.mem_inter]; tauto
  have hs := Finset.sum_sdiff (f := fun e : ℕ×ℕ => zetaPrimeLogKernel k s (e.1*e.2)) hS
  have hd := Finset.sum_sdiff (f := fun e : ℕ×ℕ => zetaPrimeLogKernel k s (e.1*e.2)) hD
  rw [heS] at hs
  rw [heD] at hd
  unfold maskedPairMoment
  linear_combination hd-hs

/-- The old population is the ENTIRE removed side of a native mask
shift. Cancelling it requires a signed estimate, not an edge allowance. -/
theorem balanced_mask_removed_all (N : ℕ) :
    balancedPairs N\balancedPairs (N+1) = balancedPairs N := by
  ext e
  simp only [Finset.mem_sdiff]
  constructor
  · exact And.left
  · intro he
    exact ⟨he,fun hf => Finset.disjoint_left.mp (balancedPairs_disjoint_succ N) he hf⟩

/-- The analogous product-label statement retains every original label. -/
theorem balanced_product_mask_removed_all (N : ℕ) :
    balancedProducts N\balancedProducts (N+1) = balancedProducts N := by
  ext n
  simp only [Finset.mem_sdiff]
  constructor
  · exact And.left
  · intro hn
    exact ⟨hn,fun hf => Finset.disjoint_left.mp (balancedProducts_disjoint_succ N) hn hf⟩

/-- Every removed label is still in a COMPLETE original phase period.
The commutator does not live in an already-paid radial endpoint strip. -/
theorem balanced_jump_subset_original_periods {u : ℝ} {N : ℕ} (hN : 65536 <= N)
    {y : ℝ} (hy : 54 <= |y|) :
    balancedProducts N\balancedProducts (N+1) ⊆
      completePeriodLabels (joinedLabels u N) N y := by
  rw [balanced_product_mask_removed_all]
  exact balancedProducts_subset_periods hN hy

/-- Diagnostic ABSOLUTE cost of the removed side. This is never
inserted into the signed floor/ceiling ledger. -/
def removedMaskPrice (u y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ balancedProducts N\balancedProducts (N+1),
    ‖(u : ℂ)^(N+1)*selbergDefect u N n*zetaPrimeLogKernel N (3/2+I*y) n‖

private theorem balanced_removed_atom_lower {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {N n : ℕ}
    (hN : 65536 <= N) (hn : n ∈ balancedProducts N) (y : ℝ) :
    u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ)) <=
      ‖(u : ℂ)^(N+1)*selbergDefect u N n*zetaPrimeLogKernel N (3/2+I*y) n‖ := by
  obtain ⟨⟨p,q⟩,he,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp,hq,_hpq,hpl,hpu,hql,hqu⟩ := balanced_pair_data he
  have hn : p*q ∈ balancedProducts N := Finset.mem_image.mpr ⟨(p,q),he,rfl⟩
  have ht : log (p*q : ℕ) = log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  have hNr : (65536 : ℝ) <= N := by exact_mod_cast hN
  have hc : 1 <= ‖selbergDefect u N (p*q)‖ :=
    (show 1 <= (N : ℝ)/20 by linarith only [hNr]).trans
      ((balanced_defect_lower hu hU hN hn).trans (Complex.re_le_norm _))
  have hTlo : 2*(N : ℝ) <= log (p*q : ℕ) := by linarith only [ht,hpl,hql]
  have hThi : log (p*q : ℕ) <= 2*(N : ℝ)+3 := by linarith only [ht,hpu,hqu]
  have hpow := pow_le_pow_left₀ (by positivity : 0 <= 2*(N : ℝ)) hTlo N
  have hex : exp (-(3/2 : ℝ)*(2*N+3)) <= exp (-(3/2 : ℝ)*log (p*q : ℕ)) := by
    apply exp_le_exp.mpr
    linarith only [hThi]
  have hk : exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/(N.factorial : ℝ) <=
      ‖zetaPrimeLogKernel N (3/2+I*y) (p*q)‖ := by
    rw [norm_zetaPrimeLogKernel]
    have hre : (3/2+I*(y : ℂ)).re = (3/2 : ℝ) := by simp
    rw [hre]
    change _ <= (log (p*q : ℕ))^N/(N.factorial : ℝ)*exp (-(3/2 : ℝ)*log (p*q : ℕ))
    have h := mul_le_mul
      (div_le_div_of_nonneg_right hpow (by positivity : 0 <= (N.factorial : ℝ))) hex
      (by positivity) (by positivity)
    calc
      _ = ((2*(N : ℝ))^N/(N.factorial : ℝ))*exp (-(3/2 : ℝ)*(2*N+3)) := by ring
      _ <= _ := h
  have hu0 : 0 <= u := by linarith only [hu]
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hu0]
  have h1 : ‖zetaPrimeLogKernel N (3/2+I*y) (p*q)‖ <=
      ‖selbergDefect u N (p*q)‖*‖zetaPrimeLogKernel N (3/2+I*y) (p*q)‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hc
  have h2 := mul_le_mul_of_nonneg_left (hk.trans h1) (pow_nonneg hu0 (N+1))
  simpa only [mul_assoc] using h2

/-- The entire mask jump retains the already-proved exponential
balanced price. It cannot be discarded by termwise absolute values. -/
theorem eventually_removedMaskPrice_growth {u : ℝ} (hu : 1/2 < u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      growthConstant u*(2*u)^N/((N : ℝ)+1)^3 <= removedMaskPrice u y N := by
  filter_upwards [eventually_balanced_product_count,eventually_ge_atTop (65536 : ℕ)]
    with N hc hN
  let M := u^(N+1)*(exp (-(3/2 : ℝ)*(2*N+3))*(2*N)^N/N.factorial)
  have hu0 : 0 <= u := by linarith only [hu]
  have hm : 0 <= M := by dsimp only [M]; positivity
  rw [removedMaskPrice,balanced_product_mask_removed_all]
  calc
    _ <= (exp (2*(N : ℝ))/(36*((N : ℝ)+1)^2))*M :=
      balanced_box_scalar_lower hu0 (by omega : 1 <= N)
    _ <= ((balancedProducts N).card : ℝ)*M := mul_le_mul_of_nonneg_right hc hm
    _ = ∑ _n ∈ balancedProducts N,M := by simp
    _ <= _ := Finset.sum_le_sum (fun n hn => balanced_removed_atom_lower
      (by linarith only [hu]) hU hN hn y)

/-- A clean no-go for ABSOLUTE payment of this mask commutator.
This says nothing negative about a future joint signed estimate. -/
theorem removedMaskPrice_tendsto_atTop {u : ℝ} (hu : 1/2 < u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Tendsto (removedMaskPrice u y) atTop atTop := by
  have hk : 0 < growthConstant u := by unfold growthConstant; positivity
  have ht := ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto
    (show 1 < 2*u by linarith only [hu])
  have hkht : Tendsto (fun N : ℕ => growthConstant u*((2*u)^N/((N : ℝ)+1)^4))
      atTop atTop := ht.const_mul_atTop hk
  refine tendsto_atTop_mono' atTop ?_ hkht
  filter_upwards [eventually_removedMaskPrice_growth hu hU y] with N hN
  apply le_trans _ hN
  rw [<-mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hn : 1 <= (N : ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) N]
  simpa only [pow_succ] using le_mul_of_one_le_right (pow_nonneg (by positivity) 3) hn

/-- Even a cofinal absolute budget on the original dyadic schedule is
impossible. The signed fixed-mask identity remains available. -/
theorem not_frequently_dyadic_removedMaskPrice_le {u : ℝ} (hu : 1/2 < u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) (y M : ℝ) :
    ¬ ∃ᶠ j : ℕ in atTop,
      removedMaskPrice u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) <= M := by
  intro h
  have ht := (removedMaskPrice_tendsto_atTop hu hU y).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually (ht.eventually_gt_atTop M)).exists
  exact hgt.not_ge hle

/-- The original balanced mask factors into its TWO one-prime windows.
This is a finite masked convolution, not a complete-prime moment. -/
theorem balanced_moment_prime_orders (N M : ℕ) (s : ℂ) :
    maskedPairMoment (balancedPairs N) M s =
      ∑ k ∈ Finset.range (M+1),
        ZetaRieszPrimePairConvolution.finiteMoment
          (ZetaRieszAllowancePrimeBoxes.logPrimes N 1) k s*
        ZetaRieszPrimePairConvolution.finiteMoment
          (ZetaRieszAllowancePrimeBoxes.logPrimes ((N : ℝ)+1) 1) (M-k) s := by
  unfold maskedPairMoment balancedPairs
  rw [Finset.product_eq_sprod,Finset.sum_product]
  exact ZetaRieszPrimePairConvolution.ordered_kernel_eq_convolution _ _
    (fun p hp => (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hp).1.pos)
    (fun q hq => (ZetaRieszAllowancePrimeBoxes.logPrimes_bounds hq).1.pos) M s

/-- The imbalance also factors into shifted orders on the SAME two
literal prime windows. No diagonal can occur between the disjoint windows. -/
theorem balanced_imbalance_prime_orders (N M : ℕ) (s : ℂ) :
    let A := ZetaRieszAllowancePrimeBoxes.logPrimes N 1
    let B := ZetaRieszAllowancePrimeBoxes.logPrimes ((N : ℝ)+1) 1
    maskedImbalanceMoment (balancedPairs N) M s =
      ∑ k ∈ Finset.range (M+1),
        ((k+1 : ℂ)*(k+2)*ZetaRieszPrimePairConvolution.finiteMoment A (k+2) s*
            ZetaRieszPrimePairConvolution.finiteMoment B (M-k) s+
         ((M-k+1 : ℕ) : ℂ)*((M-k+2 : ℕ) : ℂ)*
            ZetaRieszPrimePairConvolution.finiteMoment A k s*
            ZetaRieszPrimePairConvolution.finiteMoment B (M-k+2) s-
         2*(k+1 : ℂ)*((M-k+1 : ℕ) : ℂ)*
            ZetaRieszPrimePairConvolution.finiteMoment A (k+1) s*
            ZetaRieszPrimePairConvolution.finiteMoment B (M-k+1) s) := by
  dsimp only
  unfold maskedImbalanceMoment
  have hpoint := Finset.sum_congr (s₁ := balancedPairs N) rfl
    (fun e he => imbalance_kernel_prime_orders M e.1 e.2
    (balanced_pair_data he).1.pos (balanced_pair_data he).2.1.pos s)
  rw [hpoint,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [balancedPairs,Finset.product_eq_sprod,Finset.sum_product,
    ZetaRieszPrimePairConvolution.finiteMoment,
    Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_assoc]
  congr 1
  · congr 1 <;> exact Finset.sum_comm
  · exact Finset.sum_comm

/-- The already-paid factorial prefixes tend to zero at source scale.
No signed neighbouring moment is included in the error. -/
theorem balanced_factorialPrefix_tendsto {u : ℝ} (hu : 1/2 <= u)
    (hU : u <= ZetaRieszWideOwnerAudit.radiusCeiling) {y : ℝ} (hy : 54 <= |y|) :
    Tendsto (fun N : ℕ => (u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
      factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N) e.1 e.2 (3/2+I*y)))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ prefixBudget_tendsto
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with N hN
  exact balanced_factorialPrefix_geometric hu hU hN hy

end RiemannGaussian.ZetaRieszSelbergAdjacentOrders
